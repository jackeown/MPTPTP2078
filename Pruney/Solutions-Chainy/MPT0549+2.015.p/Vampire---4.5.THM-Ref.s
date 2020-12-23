%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:37 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 161 expanded)
%              Number of leaves         :    9 (  37 expanded)
%              Depth                    :   17
%              Number of atoms          :  121 ( 556 expanded)
%              Number of equality atoms :   43 ( 203 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f56,plain,(
    $false ),
    inference(global_subsumption,[],[f24,f22,f55,f54])).

fof(f54,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ v1_relat_1(sK1) ),
    inference(trivial_inequality_removal,[],[f52])).

fof(f52,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f32,f50])).

fof(f50,plain,(
    k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f49])).

fof(f49,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(resolution,[],[f47,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f47,plain,
    ( v1_xboole_0(k7_relat_1(sK1,sK0))
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(global_subsumption,[],[f25,f45])).

fof(f45,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k7_relat_1(sK1,sK0))
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(superposition,[],[f40,f43])).

fof(f43,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,sK0)
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(global_subsumption,[],[f22,f41])).

fof(f41,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ v1_relat_1(sK1)
    | k1_xboole_0 = k9_relat_1(sK1,sK0) ),
    inference(resolution,[],[f33,f23])).

fof(f23,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 = k9_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 != k9_relat_1(sK1,sK0) )
    & ( r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 = k9_relat_1(sK1,sK0) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f19])).

fof(f19,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k9_relat_1(X1,X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 = k9_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
        | k1_xboole_0 != k9_relat_1(sK1,sK0) )
      & ( r1_xboole_0(k1_relat_1(sK1),sK0)
        | k1_xboole_0 = k9_relat_1(sK1,sK0) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k9_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k9_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k9_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k9_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k9_relat_1(X1,X0)
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k7_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k9_relat_1(sK1,X0))
      | v1_xboole_0(k7_relat_1(sK1,X0)) ) ),
    inference(global_subsumption,[],[f22,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k9_relat_1(sK1,X0))
      | v1_xboole_0(k7_relat_1(sK1,X0))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f38,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k7_relat_1(sK1,X0))
      | ~ v1_xboole_0(k9_relat_1(sK1,X0))
      | v1_xboole_0(k7_relat_1(sK1,X0)) ) ),
    inference(superposition,[],[f29,f36])).

fof(f36,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
    inference(resolution,[],[f31,f22])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
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

fof(f25,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k7_relat_1(X1,X0)
      | r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f55,plain,(
    k1_xboole_0 = k9_relat_1(sK1,sK0) ),
    inference(forward_demodulation,[],[f51,f27])).

fof(f27,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f51,plain,(
    k2_relat_1(k1_xboole_0) = k9_relat_1(sK1,sK0) ),
    inference(superposition,[],[f36,f50])).

fof(f22,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f24,plain,
    ( k1_xboole_0 != k9_relat_1(sK1,sK0)
    | ~ r1_xboole_0(k1_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 18:19:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.45  % (22228)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.46  % (22233)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.22/0.46  % (22226)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.22/0.46  % (22230)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.22/0.46  % (22223)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.22/0.46  % (22227)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.46  % (22226)Refutation found. Thanks to Tanya!
% 0.22/0.46  % SZS status Theorem for theBenchmark
% 0.22/0.46  % SZS output start Proof for theBenchmark
% 0.22/0.46  fof(f56,plain,(
% 0.22/0.46    $false),
% 0.22/0.46    inference(global_subsumption,[],[f24,f22,f55,f54])).
% 0.22/0.46  fof(f54,plain,(
% 0.22/0.46    r1_xboole_0(k1_relat_1(sK1),sK0) | ~v1_relat_1(sK1)),
% 0.22/0.46    inference(trivial_inequality_removal,[],[f52])).
% 0.22/0.46  fof(f52,plain,(
% 0.22/0.46    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_relat_1(sK1),sK0) | ~v1_relat_1(sK1)),
% 0.22/0.46    inference(superposition,[],[f32,f50])).
% 0.22/0.46  fof(f50,plain,(
% 0.22/0.46    k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.22/0.46    inference(duplicate_literal_removal,[],[f49])).
% 0.22/0.46  fof(f49,plain,(
% 0.22/0.46    k1_xboole_0 = k7_relat_1(sK1,sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.22/0.46    inference(resolution,[],[f47,f28])).
% 0.22/0.46  fof(f28,plain,(
% 0.22/0.46    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.46    inference(cnf_transformation,[],[f11])).
% 0.22/0.46  fof(f11,plain,(
% 0.22/0.46    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.46    inference(ennf_transformation,[],[f2])).
% 0.22/0.46  fof(f2,axiom,(
% 0.22/0.46    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.46  fof(f47,plain,(
% 0.22/0.46    v1_xboole_0(k7_relat_1(sK1,sK0)) | k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.22/0.46    inference(global_subsumption,[],[f25,f45])).
% 0.22/0.46  fof(f45,plain,(
% 0.22/0.46    ~v1_xboole_0(k1_xboole_0) | v1_xboole_0(k7_relat_1(sK1,sK0)) | k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.22/0.46    inference(superposition,[],[f40,f43])).
% 0.22/0.46  fof(f43,plain,(
% 0.22/0.46    k1_xboole_0 = k9_relat_1(sK1,sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.22/0.46    inference(global_subsumption,[],[f22,f41])).
% 0.22/0.46  fof(f41,plain,(
% 0.22/0.46    k1_xboole_0 = k7_relat_1(sK1,sK0) | ~v1_relat_1(sK1) | k1_xboole_0 = k9_relat_1(sK1,sK0)),
% 0.22/0.46    inference(resolution,[],[f33,f23])).
% 0.22/0.46  fof(f23,plain,(
% 0.22/0.46    r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k9_relat_1(sK1,sK0)),
% 0.22/0.46    inference(cnf_transformation,[],[f20])).
% 0.22/0.46  fof(f20,plain,(
% 0.22/0.46    (~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k9_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k9_relat_1(sK1,sK0)) & v1_relat_1(sK1)),
% 0.22/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f19])).
% 0.22/0.46  fof(f19,plain,(
% 0.22/0.46    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k9_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k9_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k9_relat_1(sK1,sK0)) & v1_relat_1(sK1))),
% 0.22/0.46    introduced(choice_axiom,[])).
% 0.22/0.46  fof(f18,plain,(
% 0.22/0.46    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k9_relat_1(X1,X0)) & v1_relat_1(X1))),
% 0.22/0.46    inference(flattening,[],[f17])).
% 0.22/0.46  fof(f17,plain,(
% 0.22/0.46    ? [X0,X1] : (((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k9_relat_1(X1,X0))) & v1_relat_1(X1))),
% 0.22/0.46    inference(nnf_transformation,[],[f10])).
% 0.22/0.46  fof(f10,plain,(
% 0.22/0.46    ? [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <~> r1_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 0.22/0.46    inference(ennf_transformation,[],[f9])).
% 0.22/0.46  fof(f9,negated_conjecture,(
% 0.22/0.46    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.22/0.46    inference(negated_conjecture,[],[f8])).
% 0.22/0.46  fof(f8,conjecture,(
% 0.22/0.46    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).
% 0.22/0.46  fof(f33,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f21])).
% 0.22/0.46  fof(f21,plain,(
% 0.22/0.46    ! [X0,X1] : (((k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.22/0.46    inference(nnf_transformation,[],[f16])).
% 0.22/0.46  fof(f16,plain,(
% 0.22/0.46    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.46    inference(ennf_transformation,[],[f7])).
% 0.22/0.46  fof(f7,axiom,(
% 0.22/0.46    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).
% 0.22/0.46  fof(f40,plain,(
% 0.22/0.46    ( ! [X0] : (~v1_xboole_0(k9_relat_1(sK1,X0)) | v1_xboole_0(k7_relat_1(sK1,X0))) )),
% 0.22/0.46    inference(global_subsumption,[],[f22,f39])).
% 0.22/0.46  fof(f39,plain,(
% 0.22/0.46    ( ! [X0] : (~v1_xboole_0(k9_relat_1(sK1,X0)) | v1_xboole_0(k7_relat_1(sK1,X0)) | ~v1_relat_1(sK1)) )),
% 0.22/0.46    inference(resolution,[],[f38,f30])).
% 0.22/0.46  fof(f30,plain,(
% 0.22/0.46    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f14])).
% 0.22/0.46  fof(f14,plain,(
% 0.22/0.46    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.46    inference(ennf_transformation,[],[f3])).
% 0.22/0.46  fof(f3,axiom,(
% 0.22/0.46    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.22/0.46  fof(f38,plain,(
% 0.22/0.46    ( ! [X0] : (~v1_relat_1(k7_relat_1(sK1,X0)) | ~v1_xboole_0(k9_relat_1(sK1,X0)) | v1_xboole_0(k7_relat_1(sK1,X0))) )),
% 0.22/0.46    inference(superposition,[],[f29,f36])).
% 0.22/0.46  fof(f36,plain,(
% 0.22/0.46    ( ! [X0] : (k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0)) )),
% 0.22/0.46    inference(resolution,[],[f31,f22])).
% 0.22/0.46  fof(f31,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f15])).
% 0.22/0.46  fof(f15,plain,(
% 0.22/0.46    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.46    inference(ennf_transformation,[],[f5])).
% 0.22/0.46  fof(f5,axiom,(
% 0.22/0.46    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.22/0.46  fof(f29,plain,(
% 0.22/0.46    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f13])).
% 0.22/0.46  fof(f13,plain,(
% 0.22/0.46    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.22/0.46    inference(flattening,[],[f12])).
% 0.22/0.46  fof(f12,plain,(
% 0.22/0.46    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 0.22/0.46    inference(ennf_transformation,[],[f4])).
% 0.22/0.46  fof(f4,axiom,(
% 0.22/0.46    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_relat_1(X0)))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).
% 0.22/0.46  fof(f25,plain,(
% 0.22/0.46    v1_xboole_0(k1_xboole_0)),
% 0.22/0.46    inference(cnf_transformation,[],[f1])).
% 0.22/0.46  fof(f1,axiom,(
% 0.22/0.46    v1_xboole_0(k1_xboole_0)),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.46  fof(f32,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k1_xboole_0 != k7_relat_1(X1,X0) | r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f21])).
% 0.22/0.46  fof(f55,plain,(
% 0.22/0.46    k1_xboole_0 = k9_relat_1(sK1,sK0)),
% 0.22/0.46    inference(forward_demodulation,[],[f51,f27])).
% 0.22/0.46  fof(f27,plain,(
% 0.22/0.46    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.46    inference(cnf_transformation,[],[f6])).
% 0.22/0.46  fof(f6,axiom,(
% 0.22/0.46    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.46  fof(f51,plain,(
% 0.22/0.46    k2_relat_1(k1_xboole_0) = k9_relat_1(sK1,sK0)),
% 0.22/0.46    inference(superposition,[],[f36,f50])).
% 0.22/0.46  fof(f22,plain,(
% 0.22/0.46    v1_relat_1(sK1)),
% 0.22/0.46    inference(cnf_transformation,[],[f20])).
% 0.22/0.46  fof(f24,plain,(
% 0.22/0.46    k1_xboole_0 != k9_relat_1(sK1,sK0) | ~r1_xboole_0(k1_relat_1(sK1),sK0)),
% 0.22/0.46    inference(cnf_transformation,[],[f20])).
% 0.22/0.46  % SZS output end Proof for theBenchmark
% 0.22/0.46  % (22226)------------------------------
% 0.22/0.46  % (22226)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (22226)Termination reason: Refutation
% 0.22/0.46  
% 0.22/0.46  % (22226)Memory used [KB]: 6140
% 0.22/0.46  % (22226)Time elapsed: 0.006 s
% 0.22/0.46  % (22226)------------------------------
% 0.22/0.46  % (22226)------------------------------
% 0.22/0.47  % (22218)Success in time 0.103 s
%------------------------------------------------------------------------------
