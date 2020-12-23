%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   37 (  86 expanded)
%              Number of leaves         :    6 (  21 expanded)
%              Depth                    :   16
%              Number of atoms          :   65 ( 169 expanded)
%              Number of equality atoms :   13 (  30 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f340,plain,(
    $false ),
    inference(subsumption_resolution,[],[f325,f15])).

fof(f15,plain,(
    ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).

fof(f325,plain,(
    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(superposition,[],[f35,f259])).

fof(f259,plain,(
    k10_relat_1(sK2,sK1) = k10_relat_1(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f257,f47])).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,k2_xboole_0(X1,X0))) ),
    inference(superposition,[],[f35,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f257,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK1),k10_relat_1(sK2,k2_xboole_0(sK0,sK1)))
    | k10_relat_1(sK2,sK1) = k10_relat_1(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f93,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f93,plain,(
    r1_tarski(k10_relat_1(sK2,k2_xboole_0(sK0,sK1)),k10_relat_1(sK2,sK1)) ),
    inference(superposition,[],[f47,f86])).

fof(f86,plain,(
    sK1 = k2_xboole_0(sK1,k2_xboole_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f84,f21])).

fof(f21,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f84,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(sK1,k2_xboole_0(sK0,sK1)))
    | sK1 = k2_xboole_0(sK1,k2_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f78,f20])).

fof(f78,plain,(
    r1_tarski(k2_xboole_0(sK1,k2_xboole_0(sK0,sK1)),sK1) ),
    inference(forward_demodulation,[],[f70,f22])).

fof(f70,plain,(
    r1_tarski(k2_xboole_0(k2_xboole_0(sK0,sK1),sK1),sK1) ),
    inference(resolution,[],[f38,f24])).

fof(f24,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | r1_tarski(k2_xboole_0(k2_xboole_0(sK0,sK1),X0),sK1) ) ),
    inference(resolution,[],[f28,f17])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X1)
      | r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f28,plain,(
    r1_tarski(k2_xboole_0(sK0,sK1),sK1) ),
    inference(resolution,[],[f27,f24])).

fof(f27,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | r1_tarski(k2_xboole_0(sK0,X0),sK1) ) ),
    inference(resolution,[],[f14,f17])).

fof(f14,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f35,plain,(
    ! [X4,X5] : r1_tarski(k10_relat_1(sK2,X4),k10_relat_1(sK2,k2_xboole_0(X4,X5))) ),
    inference(superposition,[],[f21,f25])).

fof(f25,plain,(
    ! [X0,X1] : k10_relat_1(sK2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) ),
    inference(resolution,[],[f13,f16])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).

fof(f13,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:48:44 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (12006)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.51  % (11990)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.52  % (11990)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (11991)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.52  % (11997)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.53  % (11989)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.53  % (12008)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.53  % (11996)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.54  % (12001)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f340,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(subsumption_resolution,[],[f325,f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 0.21/0.54    inference(cnf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,plain,(
% 0.21/0.54    ? [X0,X1,X2] : (~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 0.21/0.54    inference(flattening,[],[f8])).
% 0.21/0.54  fof(f8,plain,(
% 0.21/0.54    ? [X0,X1,X2] : ((~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 0.21/0.54    inference(negated_conjecture,[],[f6])).
% 0.21/0.54  fof(f6,conjecture,(
% 0.21/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).
% 0.21/0.54  fof(f325,plain,(
% 0.21/0.54    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 0.21/0.54    inference(superposition,[],[f35,f259])).
% 0.21/0.54  fof(f259,plain,(
% 0.21/0.54    k10_relat_1(sK2,sK1) = k10_relat_1(sK2,k2_xboole_0(sK0,sK1))),
% 0.21/0.54    inference(subsumption_resolution,[],[f257,f47])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,k2_xboole_0(X1,X0)))) )),
% 0.21/0.54    inference(superposition,[],[f35,f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.54  fof(f257,plain,(
% 0.21/0.54    ~r1_tarski(k10_relat_1(sK2,sK1),k10_relat_1(sK2,k2_xboole_0(sK0,sK1))) | k10_relat_1(sK2,sK1) = k10_relat_1(sK2,k2_xboole_0(sK0,sK1))),
% 0.21/0.54    inference(resolution,[],[f93,f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.54  fof(f93,plain,(
% 0.21/0.54    r1_tarski(k10_relat_1(sK2,k2_xboole_0(sK0,sK1)),k10_relat_1(sK2,sK1))),
% 0.21/0.54    inference(superposition,[],[f47,f86])).
% 0.21/0.54  fof(f86,plain,(
% 0.21/0.54    sK1 = k2_xboole_0(sK1,k2_xboole_0(sK0,sK1))),
% 0.21/0.54    inference(subsumption_resolution,[],[f84,f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.54  fof(f84,plain,(
% 0.21/0.54    ~r1_tarski(sK1,k2_xboole_0(sK1,k2_xboole_0(sK0,sK1))) | sK1 = k2_xboole_0(sK1,k2_xboole_0(sK0,sK1))),
% 0.21/0.54    inference(resolution,[],[f78,f20])).
% 0.21/0.54  fof(f78,plain,(
% 0.21/0.54    r1_tarski(k2_xboole_0(sK1,k2_xboole_0(sK0,sK1)),sK1)),
% 0.21/0.54    inference(forward_demodulation,[],[f70,f22])).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    r1_tarski(k2_xboole_0(k2_xboole_0(sK0,sK1),sK1),sK1)),
% 0.21/0.54    inference(resolution,[],[f38,f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.54    inference(equality_resolution,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f2])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ( ! [X0] : (~r1_tarski(X0,sK1) | r1_tarski(k2_xboole_0(k2_xboole_0(sK0,sK1),X0),sK1)) )),
% 0.21/0.54    inference(resolution,[],[f28,f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X2,X1) | r1_tarski(k2_xboole_0(X0,X2),X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.21/0.54    inference(flattening,[],[f11])).
% 0.21/0.54  fof(f11,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    r1_tarski(k2_xboole_0(sK0,sK1),sK1)),
% 0.21/0.54    inference(resolution,[],[f27,f24])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ( ! [X0] : (~r1_tarski(X0,sK1) | r1_tarski(k2_xboole_0(sK0,X0),sK1)) )),
% 0.21/0.54    inference(resolution,[],[f14,f17])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    r1_tarski(sK0,sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f9])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ( ! [X4,X5] : (r1_tarski(k10_relat_1(sK2,X4),k10_relat_1(sK2,k2_xboole_0(X4,X5)))) )),
% 0.21/0.54    inference(superposition,[],[f21,f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k10_relat_1(sK2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) )),
% 0.21/0.54    inference(resolution,[],[f13,f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.21/0.54    inference(ennf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).
% 0.21/0.54  fof(f13,plain,(
% 0.21/0.54    v1_relat_1(sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f9])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (11990)------------------------------
% 0.21/0.54  % (11990)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (11990)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (11990)Memory used [KB]: 6396
% 0.21/0.54  % (11990)Time elapsed: 0.117 s
% 0.21/0.54  % (11990)------------------------------
% 0.21/0.54  % (11990)------------------------------
% 0.21/0.54  % (11977)Success in time 0.176 s
%------------------------------------------------------------------------------
