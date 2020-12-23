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
% DateTime   : Thu Dec  3 12:47:16 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 237 expanded)
%              Number of leaves         :   14 (  78 expanded)
%              Depth                    :   13
%              Number of atoms          :   80 ( 270 expanded)
%              Number of equality atoms :   63 ( 244 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (3757)Termination reason: Refutation not found, incomplete strategy
fof(f57,plain,(
    $false ),
    inference(subsumption_resolution,[],[f43,f56])).

% (3757)Memory used [KB]: 1663
fof(f56,plain,(
    ! [X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k3_relat_1(k5_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1))) ),
    inference(forward_demodulation,[],[f55,f42])).

% (3757)Time elapsed: 0.097 s
% (3757)------------------------------
% (3757)------------------------------
fof(f42,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X6))) ),
    inference(definition_unfolding,[],[f30,f41])).

fof(f41,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k5_enumset1(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_enumset1(X7,X7,X7,X7,X7,X7,X7))) ),
    inference(definition_unfolding,[],[f24,f39,f40])).

fof(f40,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f22,f38])).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f28,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f32,f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f34,f35])).

fof(f35,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f33,f31])).

fof(f31,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f34,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f32,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f28,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f22,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f29,f38])).

fof(f29,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f24,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).

fof(f30,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

% (3734)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
fof(f55,plain,(
    ! [X0,X1] : k3_relat_1(k5_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1))) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X1))) ),
    inference(forward_demodulation,[],[f53,f51])).

% (3743)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% (3738)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% (3743)Refutation not found, incomplete strategy% (3743)------------------------------
% (3743)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (3738)Refutation not found, incomplete strategy% (3738)------------------------------
% (3738)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (3738)Termination reason: Refutation not found, incomplete strategy

% (3738)Memory used [KB]: 6140
% (3738)Time elapsed: 0.109 s
% (3738)------------------------------
% (3738)------------------------------
% (3743)Termination reason: Refutation not found, incomplete strategy

% (3743)Memory used [KB]: 10618
% (3743)Time elapsed: 0.105 s
% (3743)------------------------------
% (3743)------------------------------
% (3742)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% (3741)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% (3734)Refutation not found, incomplete strategy% (3734)------------------------------
% (3734)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (3734)Termination reason: Refutation not found, incomplete strategy

% (3734)Memory used [KB]: 1663
% (3734)Time elapsed: 0.117 s
% (3734)------------------------------
% (3734)------------------------------
% (3744)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% (3744)Refutation not found, incomplete strategy% (3744)------------------------------
% (3744)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (3744)Termination reason: Refutation not found, incomplete strategy

% (3744)Memory used [KB]: 10618
% (3744)Time elapsed: 0.123 s
% (3744)------------------------------
% (3744)------------------------------
% (3760)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% (3760)Refutation not found, incomplete strategy% (3760)------------------------------
% (3760)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f51,plain,(
    ! [X0,X1] : k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = k2_relat_1(k5_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1))) ),
    inference(subsumption_resolution,[],[f48,f47])).

% (3760)Termination reason: Refutation not found, incomplete strategy

% (3760)Memory used [KB]: 10618
% (3760)Time elapsed: 0.120 s
% (3760)------------------------------
% (3760)------------------------------
fof(f47,plain,(
    ! [X2,X0,X3,X1] : v1_relat_1(k5_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    inference(definition_unfolding,[],[f27,f38])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_relat_1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = k2_relat_1(k5_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1)))
      | ~ v1_relat_1(k5_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1))) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k5_enumset1(X1,X1,X1,X1,X1,X1,X1)
      | k5_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1)) != X2
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f26,f40,f40])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k1_tarski(X1)
      | k1_tarski(k4_tarski(X0,X1)) != X2
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k2_relat_1(X2) = k1_tarski(X1)
        & k1_tarski(X0) = k1_relat_1(X2) )
      | k1_tarski(k4_tarski(X0,X1)) != X2
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k2_relat_1(X2) = k1_tarski(X1)
        & k1_tarski(X0) = k1_relat_1(X2) )
      | k1_tarski(k4_tarski(X0,X1)) != X2
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( k1_tarski(k4_tarski(X0,X1)) = X2
       => ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_tarski(X0) = k1_relat_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relat_1)).

fof(f53,plain,(
    ! [X0,X1] : k3_relat_1(k5_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1))) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_relat_1(k5_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1))))) ),
    inference(superposition,[],[f52,f50])).

fof(f50,plain,(
    ! [X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_relat_1(k5_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1))) ),
    inference(subsumption_resolution,[],[f49,f47])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_relat_1(k5_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1)))
      | ~ v1_relat_1(k5_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1))) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)
      | k5_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1)) != X2
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f25,f40,f40])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) = k1_relat_1(X2)
      | k1_tarski(k4_tarski(X0,X1)) != X2
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] : k3_relat_1(k5_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3))) = k3_tarski(k5_enumset1(k1_relat_1(k5_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3))),k1_relat_1(k5_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3))),k1_relat_1(k5_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3))),k1_relat_1(k5_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3))),k1_relat_1(k5_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3))),k1_relat_1(k5_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3))),k2_relat_1(k5_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3))))) ),
    inference(resolution,[],[f47,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k3_tarski(k5_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(definition_unfolding,[],[f23,f39])).

fof(f23,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f43,plain,(
    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k3_relat_1(k5_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))) ),
    inference(definition_unfolding,[],[f21,f38,f40])).

fof(f21,plain,(
    k2_tarski(sK0,sK1) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK1))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    k2_tarski(sK0,sK1) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f19])).

fof(f19,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k3_relat_1(k1_tarski(k4_tarski(X0,X1)))
   => k2_tarski(sK0,sK1) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK1))) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k3_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k3_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:18:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (3748)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.50  % (3756)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.51  % (3757)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.51  % (3756)Refutation not found, incomplete strategy% (3756)------------------------------
% 0.22/0.51  % (3756)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (3740)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.51  % (3756)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (3756)Memory used [KB]: 10618
% 0.22/0.51  % (3756)Time elapsed: 0.055 s
% 0.22/0.51  % (3756)------------------------------
% 0.22/0.51  % (3756)------------------------------
% 0.22/0.51  % (3749)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.51  % (3749)Refutation not found, incomplete strategy% (3749)------------------------------
% 0.22/0.51  % (3749)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (3757)Refutation not found, incomplete strategy% (3757)------------------------------
% 0.22/0.51  % (3757)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (3739)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.51  % (3749)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (3749)Memory used [KB]: 6140
% 0.22/0.51  % (3749)Time elapsed: 0.002 s
% 0.22/0.51  % (3749)------------------------------
% 0.22/0.51  % (3749)------------------------------
% 0.22/0.51  % (3739)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  % (3757)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(subsumption_resolution,[],[f43,f56])).
% 0.22/0.51  
% 0.22/0.51  % (3757)Memory used [KB]: 1663
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k3_relat_1(k5_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1)))) )),
% 0.22/0.51    inference(forward_demodulation,[],[f55,f42])).
% 0.22/0.51  % (3757)Time elapsed: 0.097 s
% 0.22/0.51  % (3757)------------------------------
% 0.22/0.51  % (3757)------------------------------
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X6)))) )),
% 0.22/0.51    inference(definition_unfolding,[],[f30,f41])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k5_enumset1(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_enumset1(X7,X7,X7,X7,X7,X7,X7)))) )),
% 0.22/0.51    inference(definition_unfolding,[],[f24,f39,f40])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 0.22/0.51    inference(definition_unfolding,[],[f22,f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 0.22/0.51    inference(definition_unfolding,[],[f28,f37])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 0.22/0.51    inference(definition_unfolding,[],[f32,f36])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 0.22/0.51    inference(definition_unfolding,[],[f34,f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 0.22/0.51    inference(definition_unfolding,[],[f33,f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 0.22/0.51    inference(definition_unfolding,[],[f29,f38])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,axiom,(
% 0.22/0.51    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.22/0.51  % (3734)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k3_relat_1(k5_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1))) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X1)))) )),
% 0.22/0.51    inference(forward_demodulation,[],[f53,f51])).
% 0.22/0.51  % (3743)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.51  % (3738)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (3743)Refutation not found, incomplete strategy% (3743)------------------------------
% 0.22/0.52  % (3743)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (3738)Refutation not found, incomplete strategy% (3738)------------------------------
% 0.22/0.52  % (3738)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (3738)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (3738)Memory used [KB]: 6140
% 0.22/0.52  % (3738)Time elapsed: 0.109 s
% 0.22/0.52  % (3738)------------------------------
% 0.22/0.52  % (3738)------------------------------
% 0.22/0.52  % (3743)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (3743)Memory used [KB]: 10618
% 0.22/0.52  % (3743)Time elapsed: 0.105 s
% 0.22/0.52  % (3743)------------------------------
% 0.22/0.52  % (3743)------------------------------
% 1.20/0.52  % (3742)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.20/0.52  % (3741)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.20/0.53  % (3734)Refutation not found, incomplete strategy% (3734)------------------------------
% 1.20/0.53  % (3734)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.53  % (3734)Termination reason: Refutation not found, incomplete strategy
% 1.20/0.53  
% 1.20/0.53  % (3734)Memory used [KB]: 1663
% 1.20/0.53  % (3734)Time elapsed: 0.117 s
% 1.20/0.53  % (3734)------------------------------
% 1.20/0.53  % (3734)------------------------------
% 1.20/0.53  % (3744)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.20/0.53  % (3744)Refutation not found, incomplete strategy% (3744)------------------------------
% 1.20/0.53  % (3744)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.53  % (3744)Termination reason: Refutation not found, incomplete strategy
% 1.20/0.53  
% 1.20/0.53  % (3744)Memory used [KB]: 10618
% 1.20/0.53  % (3744)Time elapsed: 0.123 s
% 1.20/0.53  % (3744)------------------------------
% 1.20/0.53  % (3744)------------------------------
% 1.20/0.53  % (3760)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.20/0.53  % (3760)Refutation not found, incomplete strategy% (3760)------------------------------
% 1.20/0.53  % (3760)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.53  fof(f51,plain,(
% 1.20/0.53    ( ! [X0,X1] : (k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = k2_relat_1(k5_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1)))) )),
% 1.20/0.53    inference(subsumption_resolution,[],[f48,f47])).
% 1.20/0.53  % (3760)Termination reason: Refutation not found, incomplete strategy
% 1.20/0.53  
% 1.20/0.53  % (3760)Memory used [KB]: 10618
% 1.20/0.53  % (3760)Time elapsed: 0.120 s
% 1.20/0.53  % (3760)------------------------------
% 1.20/0.53  % (3760)------------------------------
% 1.20/0.53  fof(f47,plain,(
% 1.20/0.53    ( ! [X2,X0,X3,X1] : (v1_relat_1(k5_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3)))) )),
% 1.20/0.53    inference(definition_unfolding,[],[f27,f38])).
% 1.20/0.53  fof(f27,plain,(
% 1.20/0.53    ( ! [X2,X0,X3,X1] : (v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))) )),
% 1.20/0.53    inference(cnf_transformation,[],[f11])).
% 1.20/0.53  fof(f11,axiom,(
% 1.20/0.53    ! [X0,X1,X2,X3] : v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))),
% 1.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_relat_1)).
% 1.20/0.53  fof(f48,plain,(
% 1.20/0.53    ( ! [X0,X1] : (k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = k2_relat_1(k5_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1))) | ~v1_relat_1(k5_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1)))) )),
% 1.20/0.53    inference(equality_resolution,[],[f45])).
% 1.20/0.53  fof(f45,plain,(
% 1.20/0.53    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k5_enumset1(X1,X1,X1,X1,X1,X1,X1) | k5_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1)) != X2 | ~v1_relat_1(X2)) )),
% 1.20/0.53    inference(definition_unfolding,[],[f26,f40,f40])).
% 1.20/0.53  fof(f26,plain,(
% 1.20/0.53    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k1_tarski(X1) | k1_tarski(k4_tarski(X0,X1)) != X2 | ~v1_relat_1(X2)) )),
% 1.20/0.53    inference(cnf_transformation,[],[f18])).
% 1.20/0.53  fof(f18,plain,(
% 1.20/0.53    ! [X0,X1,X2] : ((k2_relat_1(X2) = k1_tarski(X1) & k1_tarski(X0) = k1_relat_1(X2)) | k1_tarski(k4_tarski(X0,X1)) != X2 | ~v1_relat_1(X2))),
% 1.20/0.53    inference(flattening,[],[f17])).
% 1.20/0.53  fof(f17,plain,(
% 1.20/0.53    ! [X0,X1,X2] : (((k2_relat_1(X2) = k1_tarski(X1) & k1_tarski(X0) = k1_relat_1(X2)) | k1_tarski(k4_tarski(X0,X1)) != X2) | ~v1_relat_1(X2))),
% 1.20/0.53    inference(ennf_transformation,[],[f12])).
% 1.20/0.53  fof(f12,axiom,(
% 1.20/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => (k1_tarski(k4_tarski(X0,X1)) = X2 => (k2_relat_1(X2) = k1_tarski(X1) & k1_tarski(X0) = k1_relat_1(X2))))),
% 1.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relat_1)).
% 1.20/0.53  fof(f53,plain,(
% 1.20/0.53    ( ! [X0,X1] : (k3_relat_1(k5_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1))) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_relat_1(k5_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1)))))) )),
% 1.20/0.53    inference(superposition,[],[f52,f50])).
% 1.20/0.53  fof(f50,plain,(
% 1.20/0.53    ( ! [X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_relat_1(k5_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1)))) )),
% 1.20/0.53    inference(subsumption_resolution,[],[f49,f47])).
% 1.20/0.53  fof(f49,plain,(
% 1.20/0.53    ( ! [X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_relat_1(k5_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1))) | ~v1_relat_1(k5_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1)))) )),
% 1.20/0.53    inference(equality_resolution,[],[f46])).
% 1.20/0.53  fof(f46,plain,(
% 1.20/0.53    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) | k5_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1)) != X2 | ~v1_relat_1(X2)) )),
% 1.20/0.53    inference(definition_unfolding,[],[f25,f40,f40])).
% 1.20/0.53  fof(f25,plain,(
% 1.20/0.53    ( ! [X2,X0,X1] : (k1_tarski(X0) = k1_relat_1(X2) | k1_tarski(k4_tarski(X0,X1)) != X2 | ~v1_relat_1(X2)) )),
% 1.20/0.53    inference(cnf_transformation,[],[f18])).
% 1.20/0.53  fof(f52,plain,(
% 1.20/0.53    ( ! [X2,X0,X3,X1] : (k3_relat_1(k5_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3))) = k3_tarski(k5_enumset1(k1_relat_1(k5_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3))),k1_relat_1(k5_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3))),k1_relat_1(k5_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3))),k1_relat_1(k5_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3))),k1_relat_1(k5_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3))),k1_relat_1(k5_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3))),k2_relat_1(k5_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X3)))))) )),
% 1.20/0.53    inference(resolution,[],[f47,f44])).
% 1.20/0.53  fof(f44,plain,(
% 1.20/0.53    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k3_tarski(k5_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0)))) )),
% 1.20/0.53    inference(definition_unfolding,[],[f23,f39])).
% 1.20/0.53  fof(f23,plain,(
% 1.20/0.53    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.20/0.53    inference(cnf_transformation,[],[f16])).
% 1.20/0.53  fof(f16,plain,(
% 1.20/0.53    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.20/0.53    inference(ennf_transformation,[],[f10])).
% 1.20/0.53  fof(f10,axiom,(
% 1.20/0.53    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 1.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 1.20/0.53  fof(f43,plain,(
% 1.20/0.53    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k3_relat_1(k5_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)))),
% 1.20/0.53    inference(definition_unfolding,[],[f21,f38,f40])).
% 1.20/0.53  fof(f21,plain,(
% 1.20/0.53    k2_tarski(sK0,sK1) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK1)))),
% 1.20/0.53    inference(cnf_transformation,[],[f20])).
% 1.20/0.53  fof(f20,plain,(
% 1.20/0.53    k2_tarski(sK0,sK1) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK1)))),
% 1.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f19])).
% 1.20/0.53  fof(f19,plain,(
% 1.20/0.53    ? [X0,X1] : k2_tarski(X0,X1) != k3_relat_1(k1_tarski(k4_tarski(X0,X1))) => k2_tarski(sK0,sK1) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK1)))),
% 1.20/0.53    introduced(choice_axiom,[])).
% 1.20/0.53  fof(f15,plain,(
% 1.20/0.53    ? [X0,X1] : k2_tarski(X0,X1) != k3_relat_1(k1_tarski(k4_tarski(X0,X1)))),
% 1.20/0.53    inference(ennf_transformation,[],[f14])).
% 1.20/0.53  fof(f14,negated_conjecture,(
% 1.20/0.53    ~! [X0,X1] : k2_tarski(X0,X1) = k3_relat_1(k1_tarski(k4_tarski(X0,X1)))),
% 1.20/0.53    inference(negated_conjecture,[],[f13])).
% 1.20/0.53  fof(f13,conjecture,(
% 1.20/0.53    ! [X0,X1] : k2_tarski(X0,X1) = k3_relat_1(k1_tarski(k4_tarski(X0,X1)))),
% 1.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_relat_1)).
% 1.20/0.53  % SZS output end Proof for theBenchmark
% 1.20/0.53  % (3739)------------------------------
% 1.20/0.53  % (3739)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.53  % (3739)Termination reason: Refutation
% 1.20/0.53  
% 1.20/0.53  % (3739)Memory used [KB]: 6268
% 1.20/0.53  % (3739)Time elapsed: 0.099 s
% 1.20/0.53  % (3739)------------------------------
% 1.20/0.53  % (3739)------------------------------
% 1.20/0.53  % (3755)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.20/0.53  % (3733)Success in time 0.171 s
%------------------------------------------------------------------------------
