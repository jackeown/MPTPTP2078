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
% DateTime   : Thu Dec  3 12:48:11 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   25 (  51 expanded)
%              Number of leaves         :    4 (  12 expanded)
%              Depth                    :   12
%              Number of atoms          :   72 ( 189 expanded)
%              Number of equality atoms :   57 ( 146 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f27,plain,(
    $false ),
    inference(global_subsumption,[],[f16,f26])).

fof(f26,plain,(
    k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f25])).

fof(f25,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f22,f15])).

fof(f15,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f22,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f14,f21])).

fof(f21,plain,(
    k1_xboole_0 = sK0 ),
    inference(global_subsumption,[],[f13,f19,f20])).

fof(f20,plain,
    ( k1_xboole_0 != k2_relat_1(sK0)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f18,f12])).

fof(f12,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ( k1_xboole_0 != k2_relat_1(sK0)
      | k1_xboole_0 != k1_relat_1(sK0) )
    & ( k1_xboole_0 = k2_relat_1(sK0)
      | k1_xboole_0 = k1_relat_1(sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f10])).

fof(f10,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k2_relat_1(sK0)
        | k1_xboole_0 != k1_relat_1(sK0) )
      & ( k1_xboole_0 = k2_relat_1(sK0)
        | k1_xboole_0 = k1_relat_1(sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k2_relat_1(X0)
        | k1_xboole_0 != k1_relat_1(X0) )
      & ( k1_xboole_0 = k2_relat_1(X0)
        | k1_xboole_0 = k1_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k2_relat_1(X0)
        | k1_xboole_0 != k1_relat_1(X0) )
      & ( k1_xboole_0 = k2_relat_1(X0)
        | k1_xboole_0 = k1_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <~> k1_xboole_0 = k2_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k1_relat_1(X0)
        <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f19,plain,
    ( k1_xboole_0 != k1_relat_1(sK0)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f17,f12])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f13,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | k1_xboole_0 = k1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f14,plain,
    ( k1_xboole_0 != k1_relat_1(sK0)
    | k1_xboole_0 != k2_relat_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f16,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:31:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.40  % (25931)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.21/0.42  % (25926)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.43  % (25924)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.21/0.43  % (25926)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(global_subsumption,[],[f16,f26])).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    k1_xboole_0 != k2_relat_1(k1_xboole_0)),
% 0.21/0.43    inference(trivial_inequality_removal,[],[f25])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 != k2_relat_1(k1_xboole_0)),
% 0.21/0.43    inference(forward_demodulation,[],[f22,f15])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.43    inference(cnf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    k1_xboole_0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 != k2_relat_1(k1_xboole_0)),
% 0.21/0.43    inference(superposition,[],[f14,f21])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    k1_xboole_0 = sK0),
% 0.21/0.43    inference(global_subsumption,[],[f13,f19,f20])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    k1_xboole_0 != k2_relat_1(sK0) | k1_xboole_0 = sK0),
% 0.21/0.43    inference(resolution,[],[f18,f12])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    v1_relat_1(sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f11])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    (k1_xboole_0 != k2_relat_1(sK0) | k1_xboole_0 != k1_relat_1(sK0)) & (k1_xboole_0 = k2_relat_1(sK0) | k1_xboole_0 = k1_relat_1(sK0)) & v1_relat_1(sK0)),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f10])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ? [X0] : ((k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k2_relat_1(sK0) | k1_xboole_0 != k1_relat_1(sK0)) & (k1_xboole_0 = k2_relat_1(sK0) | k1_xboole_0 = k1_relat_1(sK0)) & v1_relat_1(sK0))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f9,plain,(
% 0.21/0.43    ? [X0] : ((k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) & v1_relat_1(X0))),
% 0.21/0.43    inference(flattening,[],[f8])).
% 0.21/0.43  fof(f8,plain,(
% 0.21/0.43    ? [X0] : (((k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0))) & v1_relat_1(X0))),
% 0.21/0.43    inference(nnf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,plain,(
% 0.21/0.43    ? [X0] : ((k1_xboole_0 = k1_relat_1(X0) <~> k1_xboole_0 = k2_relat_1(X0)) & v1_relat_1(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,negated_conjecture,(
% 0.21/0.43    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.21/0.43    inference(negated_conjecture,[],[f3])).
% 0.21/0.43  fof(f3,conjecture,(
% 0.21/0.43    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,plain,(
% 0.21/0.43    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.43    inference(flattening,[],[f6])).
% 0.21/0.43  fof(f6,plain,(
% 0.21/0.43    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    k1_xboole_0 != k1_relat_1(sK0) | k1_xboole_0 = sK0),
% 0.21/0.43    inference(resolution,[],[f17,f12])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f7])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    k1_xboole_0 = k2_relat_1(sK0) | k1_xboole_0 = k1_relat_1(sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f11])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    k1_xboole_0 != k1_relat_1(sK0) | k1_xboole_0 != k2_relat_1(sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f11])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.43    inference(cnf_transformation,[],[f1])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (25926)------------------------------
% 0.21/0.43  % (25926)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (25926)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (25926)Memory used [KB]: 6012
% 0.21/0.43  % (25926)Time elapsed: 0.003 s
% 0.21/0.43  % (25926)------------------------------
% 0.21/0.43  % (25926)------------------------------
% 0.21/0.43  % (25928)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.43  % (25921)Success in time 0.072 s
%------------------------------------------------------------------------------
