%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:02 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   58 (  84 expanded)
%              Number of leaves         :   13 (  21 expanded)
%              Depth                    :   14
%              Number of atoms          :  137 ( 223 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f395,plain,(
    $false ),
    inference(subsumption_resolution,[],[f394,f32])).

fof(f32,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f30])).

fof(f30,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_funct_1)).

fof(f394,plain,(
    ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f393,f33])).

fof(f33,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f393,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f390,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

fof(f390,plain,(
    ~ v1_funct_1(k7_relat_1(sK2,sK0)) ),
    inference(subsumption_resolution,[],[f385,f32])).

fof(f385,plain,
    ( ~ v1_funct_1(k7_relat_1(sK2,sK0))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f190,f143])).

fof(f143,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK1) ),
    inference(subsumption_resolution,[],[f138,f32])).

fof(f138,plain,
    ( ~ v1_relat_1(sK2)
    | ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK1) ),
    inference(resolution,[],[f89,f71])).

fof(f71,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k9_relat_1(sK2,sK0))
    | ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK1) ),
    inference(resolution,[],[f49,f50])).

fof(f50,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(sK1,k9_relat_1(sK2,sK0))) ),
    inference(backward_demodulation,[],[f34,f37])).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f34,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X0,k3_xboole_0(X1,X2)),k9_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f47,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_xboole_0(X1,X2))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_relat_1)).

fof(f190,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X0,k3_xboole_0(X1,k10_relat_1(X0,X2))),X2)
      | ~ v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f188,f58])).

fof(f58,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(superposition,[],[f36,f40])).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

% (26005)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
fof(f36,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f188,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X0,k3_xboole_0(X1,k10_relat_1(X0,X2))),X2)
      | ~ v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k3_xboole_0(X1,k10_relat_1(X0,X2)),X1) ) ),
    inference(duplicate_literal_removal,[],[f187])).

fof(f187,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X0,k3_xboole_0(X1,k10_relat_1(X0,X2))),X2)
      | ~ v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k3_xboole_0(X1,k10_relat_1(X0,X2)),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f76,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(k7_relat_1(X0,X1),k3_xboole_0(X1,k10_relat_1(X0,X2))),X2)
      | ~ v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f75,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(k7_relat_1(X0,X1),k3_xboole_0(X1,k10_relat_1(X0,X2))),X2)
      | ~ v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f42,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:28:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.43  % (26006)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.46  % (25996)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.47  % (26000)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (25998)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.47  % (25999)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.48  % (26013)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.48  % (26008)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.48  % (25995)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.48  % (26007)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.48  % (25997)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.49  % (26011)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.49  % (25998)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f395,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(subsumption_resolution,[],[f394,f32])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    v1_relat_1(sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f31])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f30])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.20/0.49    inference(flattening,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.20/0.49    inference(ennf_transformation,[],[f16])).
% 0.20/0.49  fof(f16,negated_conjecture,(
% 0.20/0.49    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)))),
% 0.20/0.49    inference(negated_conjecture,[],[f15])).
% 0.20/0.49  fof(f15,conjecture,(
% 0.20/0.49    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_funct_1)).
% 0.20/0.49  fof(f394,plain,(
% 0.20/0.49    ~v1_relat_1(sK2)),
% 0.20/0.49    inference(subsumption_resolution,[],[f393,f33])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    v1_funct_1(sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f31])).
% 0.20/0.49  fof(f393,plain,(
% 0.20/0.49    ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.20/0.49    inference(resolution,[],[f390,f44])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v1_funct_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(flattening,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,axiom,(
% 0.20/0.49    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).
% 0.20/0.49  fof(f390,plain,(
% 0.20/0.49    ~v1_funct_1(k7_relat_1(sK2,sK0))),
% 0.20/0.49    inference(subsumption_resolution,[],[f385,f32])).
% 0.20/0.49  fof(f385,plain,(
% 0.20/0.49    ~v1_funct_1(k7_relat_1(sK2,sK0)) | ~v1_relat_1(sK2)),
% 0.20/0.49    inference(resolution,[],[f190,f143])).
% 0.20/0.49  fof(f143,plain,(
% 0.20/0.49    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK1)),
% 0.20/0.49    inference(subsumption_resolution,[],[f138,f32])).
% 0.20/0.49  fof(f138,plain,(
% 0.20/0.49    ~v1_relat_1(sK2) | ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK1)),
% 0.20/0.49    inference(resolution,[],[f89,f71])).
% 0.20/0.49  fof(f71,plain,(
% 0.20/0.49    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k9_relat_1(sK2,sK0)) | ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK1)),
% 0.20/0.49    inference(resolution,[],[f49,f50])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(sK1,k9_relat_1(sK2,sK0)))),
% 0.20/0.49    inference(backward_demodulation,[],[f34,f37])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))),
% 0.20/0.49    inference(cnf_transformation,[],[f31])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.49    inference(flattening,[],[f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.20/0.49  fof(f89,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X0,k3_xboole_0(X1,X2)),k9_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(resolution,[],[f47,f48])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_xboole_0(X1,X2)) | r1_tarski(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.20/0.49    inference(ennf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) | ~v1_relat_1(X2))),
% 0.20/0.49    inference(ennf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_relat_1)).
% 0.20/0.49  fof(f190,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X0,k3_xboole_0(X1,k10_relat_1(X0,X2))),X2) | ~v1_funct_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f188,f58])).
% 0.20/0.49  fof(f58,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.20/0.49    inference(superposition,[],[f36,f40])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.49  % (26005)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.20/0.49  fof(f188,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X0,k3_xboole_0(X1,k10_relat_1(X0,X2))),X2) | ~v1_funct_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0) | ~r1_tarski(k3_xboole_0(X1,k10_relat_1(X0,X2)),X1)) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f187])).
% 0.20/0.49  fof(f187,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X0,k3_xboole_0(X1,k10_relat_1(X0,X2))),X2) | ~v1_funct_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0) | ~r1_tarski(k3_xboole_0(X1,k10_relat_1(X0,X2)),X1) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(superposition,[],[f76,f35])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) | ~r1_tarski(X1,X2) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X0] : (! [X1,X2] : (k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,axiom,(
% 0.20/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).
% 0.20/0.49  fof(f76,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(k7_relat_1(X0,X1),k3_xboole_0(X1,k10_relat_1(X0,X2))),X2) | ~v1_funct_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f75,f41])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,axiom,(
% 0.20/0.49    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.20/0.49  fof(f75,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(k7_relat_1(X0,X1),k3_xboole_0(X1,k10_relat_1(X0,X2))),X2) | ~v1_funct_1(k7_relat_1(X0,X1)) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(superposition,[],[f42,f46])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.20/0.49    inference(ennf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(flattening,[],[f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.49    inference(ennf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,axiom,(
% 0.20/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (25998)------------------------------
% 0.20/0.49  % (25998)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (25998)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (25998)Memory used [KB]: 1791
% 0.20/0.49  % (25998)Time elapsed: 0.075 s
% 0.20/0.49  % (25998)------------------------------
% 0.20/0.49  % (25998)------------------------------
% 0.20/0.50  % (25991)Success in time 0.139 s
%------------------------------------------------------------------------------
