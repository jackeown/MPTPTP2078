%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:05 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 128 expanded)
%              Number of leaves         :   17 (  36 expanded)
%              Depth                    :   19
%              Number of atoms          :  153 ( 271 expanded)
%              Number of equality atoms :   50 (  80 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f153,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f152])).

fof(f152,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f34,f151])).

fof(f151,plain,(
    k1_xboole_0 = k3_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f149,f53])).

fof(f53,plain,(
    ! [X0] : k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f36,f52])).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f44,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f36,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f149,plain,(
    k3_relat_1(k1_xboole_0) = k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f140,f144])).

fof(f144,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f141,f95])).

fof(f95,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(condensation,[],[f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f92,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f92,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(trivial_inequality_removal,[],[f91])).

fof(f91,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(k1_xboole_0,X0) ) ),
    inference(superposition,[],[f50,f89])).

fof(f89,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X4,X3] :
      ( k1_xboole_0 != X3
      | k4_xboole_0(X3,X4) = X3 ) ),
    inference(resolution,[],[f77,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f77,plain,(
    ! [X2,X1] :
      ( r1_xboole_0(X1,X2)
      | k1_xboole_0 != X1 ) ),
    inference(resolution,[],[f74,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k1_xboole_0 != X0 ) ),
    inference(duplicate_literal_removal,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f71,f47])).

fof(f71,plain,(
    ! [X0] :
      ( r1_xboole_0(X0,X0)
      | k1_xboole_0 != X0 ) ),
    inference(superposition,[],[f50,f69])).

fof(f69,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f55,f53])).

fof(f55,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f42,f52])).

fof(f42,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f141,plain,
    ( r2_hidden(sK2(k1_xboole_0),k1_xboole_0)
    | k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f137,f41])).

fof(f41,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f137,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(k1_xboole_0))
      | r2_hidden(sK2(k1_xboole_0),k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f135,f59])).

fof(f59,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f58,f35])).

fof(f35,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = k1_relat_1(X0) ) ),
    inference(resolution,[],[f40,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f40,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

fof(f135,plain,(
    ! [X0] :
      ( r2_hidden(sK2(k1_xboole_0),k1_relat_1(k1_xboole_0))
      | ~ r2_hidden(X0,k2_relat_1(k1_xboole_0)) ) ),
    inference(resolution,[],[f75,f35])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | r2_hidden(sK2(X1),k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1)) ) ),
    inference(resolution,[],[f48,f38])).

fof(f38,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | r2_hidden(sK2(X1),k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X1),k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f31])).

fof(f31,plain,(
    ! [X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
     => r2_hidden(sK2(X1),k1_relat_1(X1)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] : ~ r2_hidden(X2,k1_relat_1(X1))
          & r2_hidden(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relat_1)).

fof(f140,plain,(
    k3_relat_1(k1_xboole_0) = k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,k2_relat_1(k1_xboole_0))) ),
    inference(forward_demodulation,[],[f138,f59])).

fof(f138,plain,(
    k3_relat_1(k1_xboole_0) = k3_tarski(k1_enumset1(k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0))) ),
    inference(resolution,[],[f90,f35])).

fof(f90,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k3_relat_1(X0) = k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(resolution,[],[f54,f38])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(definition_unfolding,[],[f37,f52])).

fof(f37,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f34,plain,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(flattening,[],[f16])).

fof(f16,negated_conjecture,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    k1_xboole_0 = k3_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:48:35 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.45  % (26733)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.45  % (26725)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.45  % (26733)Refutation not found, incomplete strategy% (26733)------------------------------
% 0.22/0.45  % (26733)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (26722)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.46  % (26727)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.46  % (26726)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (26733)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (26733)Memory used [KB]: 10490
% 0.22/0.47  % (26733)Time elapsed: 0.051 s
% 0.22/0.47  % (26733)------------------------------
% 0.22/0.47  % (26733)------------------------------
% 0.22/0.47  % (26738)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.48  % (26723)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.48  % (26736)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.48  % (26723)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f153,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(trivial_inequality_removal,[],[f152])).
% 0.22/0.48  fof(f152,plain,(
% 0.22/0.48    k1_xboole_0 != k1_xboole_0),
% 0.22/0.48    inference(superposition,[],[f34,f151])).
% 0.22/0.48  fof(f151,plain,(
% 0.22/0.48    k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 0.22/0.48    inference(forward_demodulation,[],[f149,f53])).
% 0.22/0.48  fof(f53,plain,(
% 0.22/0.48    ( ! [X0] : (k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0) )),
% 0.22/0.48    inference(definition_unfolding,[],[f36,f52])).
% 0.22/0.48  fof(f52,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f43,f44])).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,axiom,(
% 0.22/0.48    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,axiom,(
% 0.22/0.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.22/0.48  fof(f149,plain,(
% 0.22/0.48    k3_relat_1(k1_xboole_0) = k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0))),
% 0.22/0.48    inference(backward_demodulation,[],[f140,f144])).
% 0.22/0.48  fof(f144,plain,(
% 0.22/0.48    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.48    inference(resolution,[],[f141,f95])).
% 0.22/0.48  fof(f95,plain,(
% 0.22/0.48    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.22/0.48    inference(condensation,[],[f93])).
% 0.22/0.48  fof(f93,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X0,k1_xboole_0)) )),
% 0.22/0.48    inference(resolution,[],[f92,f47])).
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f30])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f29])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.48    inference(rectify,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.22/0.48  fof(f92,plain,(
% 0.22/0.48    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.48    inference(trivial_inequality_removal,[],[f91])).
% 0.22/0.48  fof(f91,plain,(
% 0.22/0.48    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.48    inference(superposition,[],[f50,f89])).
% 0.22/0.48  fof(f89,plain,(
% 0.22/0.48    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.48    inference(equality_resolution,[],[f80])).
% 0.22/0.48  fof(f80,plain,(
% 0.22/0.48    ( ! [X4,X3] : (k1_xboole_0 != X3 | k4_xboole_0(X3,X4) = X3) )),
% 0.22/0.48    inference(resolution,[],[f77,f49])).
% 0.22/0.48  fof(f49,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f33])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.48    inference(nnf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,axiom,(
% 0.22/0.48    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.22/0.48  fof(f77,plain,(
% 0.22/0.48    ( ! [X2,X1] : (r1_xboole_0(X1,X2) | k1_xboole_0 != X1) )),
% 0.22/0.48    inference(resolution,[],[f74,f45])).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f30])).
% 0.22/0.48  fof(f74,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k1_xboole_0 != X0) )),
% 0.22/0.48    inference(duplicate_literal_removal,[],[f72])).
% 0.22/0.48  fof(f72,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_xboole_0 != X0 | ~r2_hidden(X1,X0) | ~r2_hidden(X1,X0)) )),
% 0.22/0.48    inference(resolution,[],[f71,f47])).
% 0.22/0.48  fof(f71,plain,(
% 0.22/0.48    ( ! [X0] : (r1_xboole_0(X0,X0) | k1_xboole_0 != X0) )),
% 0.22/0.48    inference(superposition,[],[f50,f69])).
% 0.22/0.48  fof(f69,plain,(
% 0.22/0.48    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.22/0.48    inference(superposition,[],[f55,f53])).
% 0.22/0.48  fof(f55,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f42,f52])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f33])).
% 0.22/0.48  fof(f141,plain,(
% 0.22/0.48    r2_hidden(sK2(k1_xboole_0),k1_xboole_0) | k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.48    inference(resolution,[],[f137,f41])).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f28])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f27])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.22/0.48    inference(ennf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.22/0.48  fof(f137,plain,(
% 0.22/0.48    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(k1_xboole_0)) | r2_hidden(sK2(k1_xboole_0),k1_xboole_0)) )),
% 0.22/0.48    inference(forward_demodulation,[],[f135,f59])).
% 0.22/0.48  fof(f59,plain,(
% 0.22/0.48    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.48    inference(resolution,[],[f58,f35])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    v1_xboole_0(k1_xboole_0)),
% 0.22/0.48    inference(cnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    v1_xboole_0(k1_xboole_0)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.48  fof(f58,plain,(
% 0.22/0.48    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = k1_relat_1(X0)) )),
% 0.22/0.48    inference(resolution,[],[f40,f39])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    ( ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f13])).
% 0.22/0.48  fof(f13,axiom,(
% 0.22/0.48    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k1_relat_1(X0)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).
% 0.22/0.48  fof(f135,plain,(
% 0.22/0.48    ( ! [X0] : (r2_hidden(sK2(k1_xboole_0),k1_relat_1(k1_xboole_0)) | ~r2_hidden(X0,k2_relat_1(k1_xboole_0))) )),
% 0.22/0.48    inference(resolution,[],[f75,f35])).
% 0.22/0.48  fof(f75,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v1_xboole_0(X1) | r2_hidden(sK2(X1),k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1))) )),
% 0.22/0.48    inference(resolution,[],[f48,f38])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,axiom,(
% 0.22/0.48    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r2_hidden(X0,k2_relat_1(X1)) | r2_hidden(sK2(X1),k1_relat_1(X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f32])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ! [X0,X1] : (r2_hidden(sK2(X1),k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f31])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ! [X1] : (? [X2] : r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(sK2(X1),k1_relat_1(X1)))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ! [X0,X1] : (? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(flattening,[],[f25])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ! [X0,X1] : ((? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f14])).
% 0.22/0.48  fof(f14,axiom,(
% 0.22/0.48    ! [X0,X1] : (v1_relat_1(X1) => ~(! [X2] : ~r2_hidden(X2,k1_relat_1(X1)) & r2_hidden(X0,k2_relat_1(X1))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relat_1)).
% 0.22/0.48  fof(f140,plain,(
% 0.22/0.48    k3_relat_1(k1_xboole_0) = k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,k2_relat_1(k1_xboole_0)))),
% 0.22/0.48    inference(forward_demodulation,[],[f138,f59])).
% 0.22/0.48  fof(f138,plain,(
% 0.22/0.48    k3_relat_1(k1_xboole_0) = k3_tarski(k1_enumset1(k1_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0)))),
% 0.22/0.48    inference(resolution,[],[f90,f35])).
% 0.22/0.48  fof(f90,plain,(
% 0.22/0.48    ( ! [X0] : (~v1_xboole_0(X0) | k3_relat_1(X0) = k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0)))) )),
% 0.22/0.48    inference(resolution,[],[f54,f38])).
% 0.22/0.48  fof(f54,plain,(
% 0.22/0.48    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0)))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f37,f52])).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f12])).
% 0.22/0.48  fof(f12,axiom,(
% 0.22/0.48    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    k1_xboole_0 != k3_relat_1(k1_xboole_0)),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    k1_xboole_0 != k3_relat_1(k1_xboole_0)),
% 0.22/0.48    inference(flattening,[],[f16])).
% 0.22/0.48  fof(f16,negated_conjecture,(
% 0.22/0.48    ~k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 0.22/0.48    inference(negated_conjecture,[],[f15])).
% 0.22/0.48  fof(f15,conjecture,(
% 0.22/0.48    k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_relat_1)).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (26723)------------------------------
% 0.22/0.48  % (26723)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (26723)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (26723)Memory used [KB]: 1663
% 0.22/0.48  % (26723)Time elapsed: 0.067 s
% 0.22/0.48  % (26723)------------------------------
% 0.22/0.48  % (26723)------------------------------
% 0.22/0.48  % (26717)Success in time 0.119 s
%------------------------------------------------------------------------------
