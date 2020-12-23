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
% DateTime   : Thu Dec  3 12:54:18 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 151 expanded)
%              Number of leaves         :   13 (  39 expanded)
%              Depth                    :   22
%              Number of atoms          :  125 ( 521 expanded)
%              Number of equality atoms :   33 (  55 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f279,plain,(
    $false ),
    inference(subsumption_resolution,[],[f275,f31])).

fof(f31,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_tarski(sK0,k2_relat_1(sK2))
    & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f23])).

fof(f23,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_tarski(X0,k2_relat_1(X2))
        & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK0,sK1)
      & r1_tarski(sK0,k2_relat_1(sK2))
      & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(X0,k2_relat_1(X2))
            & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X0,k2_relat_1(X2))
          & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).

fof(f275,plain,(
    r1_tarski(sK0,sK1) ),
    inference(superposition,[],[f170,f33])).

fof(f33,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f170,plain,(
    ! [X1] : r1_tarski(sK0,k2_xboole_0(sK1,X1)) ),
    inference(forward_demodulation,[],[f166,f37])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f166,plain,(
    ! [X1] : r1_tarski(k2_xboole_0(sK0,k3_xboole_0(sK0,X1)),k2_xboole_0(sK1,X1)) ),
    inference(superposition,[],[f44,f147])).

fof(f147,plain,(
    sK0 = k3_xboole_0(sK0,sK1) ),
    inference(subsumption_resolution,[],[f143,f34])).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f143,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ r1_tarski(k3_xboole_0(sK0,sK1),sK0) ),
    inference(resolution,[],[f131,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f131,plain,(
    r1_tarski(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f130,f36])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f130,plain,(
    r1_tarski(sK0,k3_xboole_0(sK1,sK0)) ),
    inference(forward_demodulation,[],[f129,f55])).

fof(f55,plain,(
    sK0 = k3_xboole_0(sK0,k2_relat_1(sK2)) ),
    inference(resolution,[],[f30,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f30,plain,(
    r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f24])).

fof(f129,plain,(
    r1_tarski(sK0,k3_xboole_0(sK1,k3_xboole_0(sK0,k2_relat_1(sK2)))) ),
    inference(forward_demodulation,[],[f128,f36])).

fof(f128,plain,(
    r1_tarski(sK0,k3_xboole_0(sK1,k3_xboole_0(k2_relat_1(sK2),sK0))) ),
    inference(forward_demodulation,[],[f127,f55])).

fof(f127,plain,(
    r1_tarski(k3_xboole_0(sK0,k2_relat_1(sK2)),k3_xboole_0(sK1,k3_xboole_0(k2_relat_1(sK2),k3_xboole_0(sK0,k2_relat_1(sK2))))) ),
    inference(forward_demodulation,[],[f126,f92])).

fof(f92,plain,(
    ! [X0] : k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k3_xboole_0(X0,k2_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f52,f50])).

fof(f50,plain,(
    k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2)) ),
    inference(resolution,[],[f27,f32])).

fof(f32,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f27,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f52,plain,(
    ! [X0] : k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k3_xboole_0(X0,k9_relat_1(sK2,k1_relat_1(sK2))) ),
    inference(subsumption_resolution,[],[f51,f27])).

fof(f51,plain,(
    ! [X0] :
      ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k3_xboole_0(X0,k9_relat_1(sK2,k1_relat_1(sK2)))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f28,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).

fof(f28,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f126,plain,(
    r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),k3_xboole_0(sK1,k3_xboole_0(k2_relat_1(sK2),k9_relat_1(sK2,k10_relat_1(sK2,sK0))))) ),
    inference(forward_demodulation,[],[f125,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f125,plain,(
    r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),k3_xboole_0(k3_xboole_0(sK1,k2_relat_1(sK2)),k9_relat_1(sK2,k10_relat_1(sK2,sK0)))) ),
    inference(forward_demodulation,[],[f124,f36])).

fof(f124,plain,(
    r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),k3_xboole_0(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),k3_xboole_0(sK1,k2_relat_1(sK2)))) ),
    inference(forward_demodulation,[],[f112,f92])).

fof(f112,plain,(
    r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),k3_xboole_0(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),k9_relat_1(sK2,k10_relat_1(sK2,sK1)))) ),
    inference(superposition,[],[f48,f58])).

fof(f58,plain,(
    k10_relat_1(sK2,sK0) = k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(resolution,[],[f29,f38])).

fof(f29,plain,(
    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(k9_relat_1(sK2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) ),
    inference(resolution,[],[f27,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_relat_1)).

fof(f44,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:30:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (29537)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.47  % (29545)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.47  % (29545)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f279,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(subsumption_resolution,[],[f275,f31])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ~r1_tarski(sK0,sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.20/0.48    inference(flattening,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.20/0.48    inference(ennf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.20/0.48    inference(negated_conjecture,[],[f13])).
% 0.20/0.48  fof(f13,conjecture,(
% 0.20/0.48    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).
% 0.20/0.48  fof(f275,plain,(
% 0.20/0.48    r1_tarski(sK0,sK1)),
% 0.20/0.48    inference(superposition,[],[f170,f33])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.20/0.48    inference(rectify,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.20/0.48  fof(f170,plain,(
% 0.20/0.48    ( ! [X1] : (r1_tarski(sK0,k2_xboole_0(sK1,X1))) )),
% 0.20/0.48    inference(forward_demodulation,[],[f166,f37])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,axiom,(
% 0.20/0.48    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.20/0.48  fof(f166,plain,(
% 0.20/0.48    ( ! [X1] : (r1_tarski(k2_xboole_0(sK0,k3_xboole_0(sK0,X1)),k2_xboole_0(sK1,X1))) )),
% 0.20/0.48    inference(superposition,[],[f44,f147])).
% 0.20/0.48  fof(f147,plain,(
% 0.20/0.48    sK0 = k3_xboole_0(sK0,sK1)),
% 0.20/0.48    inference(subsumption_resolution,[],[f143,f34])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.20/0.48  fof(f143,plain,(
% 0.20/0.48    sK0 = k3_xboole_0(sK0,sK1) | ~r1_tarski(k3_xboole_0(sK0,sK1),sK0)),
% 0.20/0.48    inference(resolution,[],[f131,f42])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.48    inference(flattening,[],[f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.48    inference(nnf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.48  fof(f131,plain,(
% 0.20/0.48    r1_tarski(sK0,k3_xboole_0(sK0,sK1))),
% 0.20/0.48    inference(forward_demodulation,[],[f130,f36])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.48  fof(f130,plain,(
% 0.20/0.48    r1_tarski(sK0,k3_xboole_0(sK1,sK0))),
% 0.20/0.48    inference(forward_demodulation,[],[f129,f55])).
% 0.20/0.48  fof(f55,plain,(
% 0.20/0.48    sK0 = k3_xboole_0(sK0,k2_relat_1(sK2))),
% 0.20/0.48    inference(resolution,[],[f30,f38])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,axiom,(
% 0.20/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    r1_tarski(sK0,k2_relat_1(sK2))),
% 0.20/0.48    inference(cnf_transformation,[],[f24])).
% 0.20/0.48  fof(f129,plain,(
% 0.20/0.48    r1_tarski(sK0,k3_xboole_0(sK1,k3_xboole_0(sK0,k2_relat_1(sK2))))),
% 0.20/0.48    inference(forward_demodulation,[],[f128,f36])).
% 0.20/0.48  fof(f128,plain,(
% 0.20/0.48    r1_tarski(sK0,k3_xboole_0(sK1,k3_xboole_0(k2_relat_1(sK2),sK0)))),
% 0.20/0.48    inference(forward_demodulation,[],[f127,f55])).
% 0.20/0.48  fof(f127,plain,(
% 0.20/0.48    r1_tarski(k3_xboole_0(sK0,k2_relat_1(sK2)),k3_xboole_0(sK1,k3_xboole_0(k2_relat_1(sK2),k3_xboole_0(sK0,k2_relat_1(sK2)))))),
% 0.20/0.48    inference(forward_demodulation,[],[f126,f92])).
% 0.20/0.48  fof(f92,plain,(
% 0.20/0.48    ( ! [X0] : (k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k3_xboole_0(X0,k2_relat_1(sK2))) )),
% 0.20/0.48    inference(forward_demodulation,[],[f52,f50])).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2))),
% 0.20/0.48    inference(resolution,[],[f27,f32])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,axiom,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    v1_relat_1(sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f24])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    ( ! [X0] : (k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k3_xboole_0(X0,k9_relat_1(sK2,k1_relat_1(sK2)))) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f51,f27])).
% 0.20/0.48  fof(f51,plain,(
% 0.20/0.48    ( ! [X0] : (k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k3_xboole_0(X0,k9_relat_1(sK2,k1_relat_1(sK2))) | ~v1_relat_1(sK2)) )),
% 0.20/0.48    inference(resolution,[],[f28,f39])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(flattening,[],[f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.48    inference(ennf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,axiom,(
% 0.20/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    v1_funct_1(sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f24])).
% 0.20/0.48  fof(f126,plain,(
% 0.20/0.48    r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),k3_xboole_0(sK1,k3_xboole_0(k2_relat_1(sK2),k9_relat_1(sK2,k10_relat_1(sK2,sK0)))))),
% 0.20/0.48    inference(forward_demodulation,[],[f125,f43])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).
% 0.20/0.48  fof(f125,plain,(
% 0.20/0.48    r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),k3_xboole_0(k3_xboole_0(sK1,k2_relat_1(sK2)),k9_relat_1(sK2,k10_relat_1(sK2,sK0))))),
% 0.20/0.48    inference(forward_demodulation,[],[f124,f36])).
% 0.20/0.48  fof(f124,plain,(
% 0.20/0.48    r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),k3_xboole_0(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),k3_xboole_0(sK1,k2_relat_1(sK2))))),
% 0.20/0.48    inference(forward_demodulation,[],[f112,f92])).
% 0.20/0.48  fof(f112,plain,(
% 0.20/0.48    r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),k3_xboole_0(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),k9_relat_1(sK2,k10_relat_1(sK2,sK1))))),
% 0.20/0.48    inference(superposition,[],[f48,f58])).
% 0.20/0.48  fof(f58,plain,(
% 0.20/0.48    k10_relat_1(sK2,sK0) = k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 0.20/0.48    inference(resolution,[],[f29,f38])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 0.20/0.48    inference(cnf_transformation,[],[f24])).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)))) )),
% 0.20/0.48    inference(resolution,[],[f27,f45])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) | ~v1_relat_1(X2))),
% 0.20/0.48    inference(ennf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_relat_1)).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (29545)------------------------------
% 0.20/0.48  % (29545)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (29545)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (29545)Memory used [KB]: 1791
% 0.20/0.48  % (29545)Time elapsed: 0.070 s
% 0.20/0.48  % (29545)------------------------------
% 0.20/0.48  % (29545)------------------------------
% 0.20/0.48  % (29526)Success in time 0.125 s
%------------------------------------------------------------------------------
