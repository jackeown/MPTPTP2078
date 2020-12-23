%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:03 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   34 (  74 expanded)
%              Number of leaves         :    7 (  23 expanded)
%              Depth                    :   11
%              Number of atoms          :   87 ( 282 expanded)
%              Number of equality atoms :   38 ( 151 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f38,plain,(
    $false ),
    inference(subsumption_resolution,[],[f37,f36])).

fof(f36,plain,(
    k1_xboole_0 != sK1 ),
    inference(backward_demodulation,[],[f19,f32])).

fof(f32,plain,(
    k1_xboole_0 = sK0 ),
    inference(resolution,[],[f29,f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f29,plain,(
    v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f28,f15])).

fof(f15,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( sK0 != sK1
    & k1_xboole_0 = k2_relat_1(sK1)
    & k1_xboole_0 = k2_relat_1(sK0)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f13,f12])).

% (355)Refutation not found, incomplete strategy% (355)------------------------------
% (355)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (355)Termination reason: Refutation not found, incomplete strategy

% (355)Memory used [KB]: 10618
% (355)Time elapsed: 0.108 s
% (355)------------------------------
% (355)------------------------------
fof(f12,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( X0 != X1
            & k1_xboole_0 = k2_relat_1(X1)
            & k1_xboole_0 = k2_relat_1(X0)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( sK0 != X1
          & k1_xboole_0 = k2_relat_1(X1)
          & k1_xboole_0 = k2_relat_1(sK0)
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X1] :
        ( sK0 != X1
        & k1_xboole_0 = k2_relat_1(X1)
        & k1_xboole_0 = k2_relat_1(sK0)
        & v1_relat_1(X1) )
   => ( sK0 != sK1
      & k1_xboole_0 = k2_relat_1(sK1)
      & k1_xboole_0 = k2_relat_1(sK0)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & k1_xboole_0 = k2_relat_1(X1)
          & k1_xboole_0 = k2_relat_1(X0)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & k1_xboole_0 = k2_relat_1(X1)
          & k1_xboole_0 = k2_relat_1(X0)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( ( k1_xboole_0 = k2_relat_1(X1)
                & k1_xboole_0 = k2_relat_1(X0) )
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( ( k1_xboole_0 = k2_relat_1(X1)
              & k1_xboole_0 = k2_relat_1(X0) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t197_relat_1)).

fof(f28,plain,
    ( ~ v1_relat_1(sK0)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f26,f24])).

fof(f24,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f20,f21])).

fof(f21,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f20,plain,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc13_subset_1)).

fof(f26,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(sK0)
    | v1_xboole_0(sK0) ),
    inference(superposition,[],[f23,f17])).

fof(f17,plain,(
    k1_xboole_0 = k2_relat_1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

fof(f19,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f14])).

fof(f37,plain,(
    k1_xboole_0 = sK1 ),
    inference(resolution,[],[f31,f22])).

fof(f31,plain,(
    v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f30,f16])).

fof(f16,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f30,plain,
    ( ~ v1_relat_1(sK1)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f27,f24])).

fof(f27,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(sK1)
    | v1_xboole_0(sK1) ),
    inference(superposition,[],[f23,f18])).

fof(f18,plain,(
    k1_xboole_0 = k2_relat_1(sK1) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n022.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 12:20:26 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.24/0.53  % (345)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.24/0.53  % (352)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.24/0.53  % (360)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.24/0.53  % (360)Refutation not found, incomplete strategy% (360)------------------------------
% 0.24/0.53  % (360)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.24/0.53  % (360)Termination reason: Refutation not found, incomplete strategy
% 0.24/0.53  
% 0.24/0.53  % (360)Memory used [KB]: 6140
% 0.24/0.53  % (360)Time elapsed: 0.001 s
% 0.24/0.53  % (360)------------------------------
% 0.24/0.53  % (360)------------------------------
% 0.24/0.53  % (355)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.24/0.53  % (352)Refutation found. Thanks to Tanya!
% 0.24/0.53  % SZS status Theorem for theBenchmark
% 0.24/0.53  % (356)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.24/0.53  % SZS output start Proof for theBenchmark
% 0.24/0.53  fof(f38,plain,(
% 0.24/0.53    $false),
% 0.24/0.53    inference(subsumption_resolution,[],[f37,f36])).
% 0.24/0.53  fof(f36,plain,(
% 0.24/0.53    k1_xboole_0 != sK1),
% 0.24/0.53    inference(backward_demodulation,[],[f19,f32])).
% 0.24/0.53  fof(f32,plain,(
% 0.24/0.53    k1_xboole_0 = sK0),
% 0.24/0.53    inference(resolution,[],[f29,f22])).
% 0.24/0.53  fof(f22,plain,(
% 0.24/0.53    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.24/0.53    inference(cnf_transformation,[],[f9])).
% 0.24/0.53  fof(f9,plain,(
% 0.24/0.53    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.24/0.53    inference(ennf_transformation,[],[f1])).
% 0.24/0.53  fof(f1,axiom,(
% 0.24/0.53    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.24/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.24/0.53  fof(f29,plain,(
% 0.24/0.53    v1_xboole_0(sK0)),
% 0.24/0.53    inference(subsumption_resolution,[],[f28,f15])).
% 0.24/0.53  fof(f15,plain,(
% 0.24/0.53    v1_relat_1(sK0)),
% 0.24/0.53    inference(cnf_transformation,[],[f14])).
% 0.24/0.53  fof(f14,plain,(
% 0.24/0.53    (sK0 != sK1 & k1_xboole_0 = k2_relat_1(sK1) & k1_xboole_0 = k2_relat_1(sK0) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.24/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f13,f12])).
% 0.24/0.53  % (355)Refutation not found, incomplete strategy% (355)------------------------------
% 0.24/0.53  % (355)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.24/0.53  % (355)Termination reason: Refutation not found, incomplete strategy
% 0.24/0.53  
% 0.24/0.53  % (355)Memory used [KB]: 10618
% 0.24/0.53  % (355)Time elapsed: 0.108 s
% 0.24/0.53  % (355)------------------------------
% 0.24/0.53  % (355)------------------------------
% 0.24/0.53  fof(f12,plain,(
% 0.24/0.53    ? [X0] : (? [X1] : (X0 != X1 & k1_xboole_0 = k2_relat_1(X1) & k1_xboole_0 = k2_relat_1(X0) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (sK0 != X1 & k1_xboole_0 = k2_relat_1(X1) & k1_xboole_0 = k2_relat_1(sK0) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.24/0.53    introduced(choice_axiom,[])).
% 0.24/0.53  fof(f13,plain,(
% 0.24/0.53    ? [X1] : (sK0 != X1 & k1_xboole_0 = k2_relat_1(X1) & k1_xboole_0 = k2_relat_1(sK0) & v1_relat_1(X1)) => (sK0 != sK1 & k1_xboole_0 = k2_relat_1(sK1) & k1_xboole_0 = k2_relat_1(sK0) & v1_relat_1(sK1))),
% 0.24/0.53    introduced(choice_axiom,[])).
% 0.24/0.53  fof(f8,plain,(
% 0.24/0.53    ? [X0] : (? [X1] : (X0 != X1 & k1_xboole_0 = k2_relat_1(X1) & k1_xboole_0 = k2_relat_1(X0) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.24/0.53    inference(flattening,[],[f7])).
% 0.24/0.53  fof(f7,plain,(
% 0.24/0.53    ? [X0] : (? [X1] : ((X0 != X1 & (k1_xboole_0 = k2_relat_1(X1) & k1_xboole_0 = k2_relat_1(X0))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.24/0.53    inference(ennf_transformation,[],[f6])).
% 0.24/0.53  fof(f6,negated_conjecture,(
% 0.24/0.53    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ((k1_xboole_0 = k2_relat_1(X1) & k1_xboole_0 = k2_relat_1(X0)) => X0 = X1)))),
% 0.24/0.53    inference(negated_conjecture,[],[f5])).
% 0.24/0.53  fof(f5,conjecture,(
% 0.24/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ((k1_xboole_0 = k2_relat_1(X1) & k1_xboole_0 = k2_relat_1(X0)) => X0 = X1)))),
% 0.24/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t197_relat_1)).
% 0.24/0.53  fof(f28,plain,(
% 0.24/0.53    ~v1_relat_1(sK0) | v1_xboole_0(sK0)),
% 0.24/0.53    inference(subsumption_resolution,[],[f26,f24])).
% 0.24/0.53  fof(f24,plain,(
% 0.24/0.53    v1_xboole_0(k1_xboole_0)),
% 0.24/0.53    inference(backward_demodulation,[],[f20,f21])).
% 0.24/0.53  fof(f21,plain,(
% 0.24/0.53    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.24/0.53    inference(cnf_transformation,[],[f2])).
% 0.24/0.53  fof(f2,axiom,(
% 0.24/0.53    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.24/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 0.24/0.53  fof(f20,plain,(
% 0.24/0.53    ( ! [X0] : (v1_xboole_0(k1_subset_1(X0))) )),
% 0.24/0.53    inference(cnf_transformation,[],[f3])).
% 0.24/0.53  fof(f3,axiom,(
% 0.24/0.53    ! [X0] : v1_xboole_0(k1_subset_1(X0))),
% 0.24/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc13_subset_1)).
% 0.24/0.53  fof(f26,plain,(
% 0.24/0.53    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(sK0) | v1_xboole_0(sK0)),
% 0.24/0.53    inference(superposition,[],[f23,f17])).
% 0.24/0.53  fof(f17,plain,(
% 0.24/0.53    k1_xboole_0 = k2_relat_1(sK0)),
% 0.24/0.53    inference(cnf_transformation,[],[f14])).
% 0.24/0.53  fof(f23,plain,(
% 0.24/0.53    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 0.24/0.53    inference(cnf_transformation,[],[f11])).
% 0.24/0.53  fof(f11,plain,(
% 0.24/0.53    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.24/0.53    inference(flattening,[],[f10])).
% 0.24/0.53  fof(f10,plain,(
% 0.24/0.53    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 0.24/0.53    inference(ennf_transformation,[],[f4])).
% 0.24/0.53  fof(f4,axiom,(
% 0.24/0.53    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_relat_1(X0)))),
% 0.24/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).
% 0.24/0.53  fof(f19,plain,(
% 0.24/0.53    sK0 != sK1),
% 0.24/0.53    inference(cnf_transformation,[],[f14])).
% 0.24/0.53  fof(f37,plain,(
% 0.24/0.53    k1_xboole_0 = sK1),
% 0.24/0.53    inference(resolution,[],[f31,f22])).
% 0.24/0.53  fof(f31,plain,(
% 0.24/0.53    v1_xboole_0(sK1)),
% 0.24/0.53    inference(subsumption_resolution,[],[f30,f16])).
% 0.24/0.53  fof(f16,plain,(
% 0.24/0.53    v1_relat_1(sK1)),
% 0.24/0.53    inference(cnf_transformation,[],[f14])).
% 0.24/0.53  fof(f30,plain,(
% 0.24/0.53    ~v1_relat_1(sK1) | v1_xboole_0(sK1)),
% 0.24/0.53    inference(subsumption_resolution,[],[f27,f24])).
% 0.24/0.53  fof(f27,plain,(
% 0.24/0.53    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(sK1) | v1_xboole_0(sK1)),
% 0.24/0.53    inference(superposition,[],[f23,f18])).
% 0.24/0.53  fof(f18,plain,(
% 0.24/0.53    k1_xboole_0 = k2_relat_1(sK1)),
% 0.24/0.53    inference(cnf_transformation,[],[f14])).
% 0.24/0.53  % SZS output end Proof for theBenchmark
% 0.24/0.53  % (352)------------------------------
% 0.24/0.53  % (352)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.24/0.53  % (352)Termination reason: Refutation
% 0.24/0.53  
% 0.24/0.53  % (352)Memory used [KB]: 6140
% 0.24/0.53  % (352)Time elapsed: 0.103 s
% 0.24/0.53  % (352)------------------------------
% 0.24/0.53  % (352)------------------------------
% 0.24/0.53  % (356)Refutation not found, incomplete strategy% (356)------------------------------
% 0.24/0.53  % (356)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.24/0.53  % (356)Termination reason: Refutation not found, incomplete strategy
% 0.24/0.53  
% 0.24/0.53  % (356)Memory used [KB]: 10618
% 0.24/0.53  % (356)Time elapsed: 0.107 s
% 0.24/0.53  % (356)------------------------------
% 0.24/0.53  % (356)------------------------------
% 0.24/0.53  % (344)Success in time 0.159 s
%------------------------------------------------------------------------------
