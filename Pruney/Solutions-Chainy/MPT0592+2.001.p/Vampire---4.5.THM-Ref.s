%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:02 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   38 (  77 expanded)
%              Number of leaves         :    8 (  25 expanded)
%              Depth                    :   12
%              Number of atoms          :  100 ( 296 expanded)
%              Number of equality atoms :   35 ( 146 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f58,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f39,f56])).

fof(f56,plain,(
    ~ spl2_1 ),
    inference(avatar_contradiction_clause,[],[f52])).

fof(f52,plain,
    ( $false
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f21,f51])).

fof(f51,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl2_1 ),
    inference(forward_demodulation,[],[f50,f19])).

fof(f19,plain,(
    k1_xboole_0 = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( sK0 != sK1
    & k1_xboole_0 = k1_relat_1(sK1)
    & k1_xboole_0 = k1_relat_1(sK0)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f14,f13])).

fof(f13,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( X0 != X1
            & k1_xboole_0 = k1_relat_1(X1)
            & k1_xboole_0 = k1_relat_1(X0)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( sK0 != X1
          & k1_xboole_0 = k1_relat_1(X1)
          & k1_xboole_0 = k1_relat_1(sK0)
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X1] :
        ( sK0 != X1
        & k1_xboole_0 = k1_relat_1(X1)
        & k1_xboole_0 = k1_relat_1(sK0)
        & v1_relat_1(X1) )
   => ( sK0 != sK1
      & k1_xboole_0 = k1_relat_1(sK1)
      & k1_xboole_0 = k1_relat_1(sK0)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & k1_xboole_0 = k1_relat_1(X1)
          & k1_xboole_0 = k1_relat_1(X0)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & k1_xboole_0 = k1_relat_1(X1)
          & k1_xboole_0 = k1_relat_1(X0)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( ( k1_xboole_0 = k1_relat_1(X1)
                & k1_xboole_0 = k1_relat_1(X0) )
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( ( k1_xboole_0 = k1_relat_1(X1)
              & k1_xboole_0 = k1_relat_1(X0) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t196_relat_1)).

fof(f50,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK1))
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f17,f49,f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).

fof(f49,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f45,f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f45,plain,
    ( k1_xboole_0 != sK1
    | ~ spl2_1 ),
    inference(backward_demodulation,[],[f20,f41])).

fof(f41,plain,
    ( k1_xboole_0 = sK0
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f30,f22])).

fof(f30,plain,
    ( v1_xboole_0(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl2_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f20,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f15])).

fof(f17,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f21,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f39,plain,(
    spl2_2 ),
    inference(avatar_contradiction_clause,[],[f36])).

fof(f36,plain,
    ( $false
    | spl2_2 ),
    inference(unit_resulting_resolution,[],[f21,f34])).

fof(f34,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl2_2
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f35,plain,
    ( spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f26,f32,f28])).

fof(f26,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(sK0) ),
    inference(global_subsumption,[],[f16,f25])).

fof(f25,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(sK0)
    | v1_xboole_0(sK0) ),
    inference(superposition,[],[f24,f18])).

fof(f18,plain,(
    k1_xboole_0 = k1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:12:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.46  % (10174)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.46  % (10174)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f58,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f35,f39,f56])).
% 0.20/0.46  fof(f56,plain,(
% 0.20/0.46    ~spl2_1),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f52])).
% 0.20/0.46  fof(f52,plain,(
% 0.20/0.46    $false | ~spl2_1),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f21,f51])).
% 0.20/0.46  fof(f51,plain,(
% 0.20/0.46    ~v1_xboole_0(k1_xboole_0) | ~spl2_1),
% 0.20/0.46    inference(forward_demodulation,[],[f50,f19])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    k1_xboole_0 = k1_relat_1(sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    (sK0 != sK1 & k1_xboole_0 = k1_relat_1(sK1) & k1_xboole_0 = k1_relat_1(sK0) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f14,f13])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : (X0 != X1 & k1_xboole_0 = k1_relat_1(X1) & k1_xboole_0 = k1_relat_1(X0) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (sK0 != X1 & k1_xboole_0 = k1_relat_1(X1) & k1_xboole_0 = k1_relat_1(sK0) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    ? [X1] : (sK0 != X1 & k1_xboole_0 = k1_relat_1(X1) & k1_xboole_0 = k1_relat_1(sK0) & v1_relat_1(X1)) => (sK0 != sK1 & k1_xboole_0 = k1_relat_1(sK1) & k1_xboole_0 = k1_relat_1(sK0) & v1_relat_1(sK1))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f8,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : (X0 != X1 & k1_xboole_0 = k1_relat_1(X1) & k1_xboole_0 = k1_relat_1(X0) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.20/0.46    inference(flattening,[],[f7])).
% 0.20/0.46  fof(f7,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : ((X0 != X1 & (k1_xboole_0 = k1_relat_1(X1) & k1_xboole_0 = k1_relat_1(X0))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f6])).
% 0.20/0.46  fof(f6,negated_conjecture,(
% 0.20/0.46    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ((k1_xboole_0 = k1_relat_1(X1) & k1_xboole_0 = k1_relat_1(X0)) => X0 = X1)))),
% 0.20/0.46    inference(negated_conjecture,[],[f5])).
% 0.20/0.46  fof(f5,conjecture,(
% 0.20/0.46    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ((k1_xboole_0 = k1_relat_1(X1) & k1_xboole_0 = k1_relat_1(X0)) => X0 = X1)))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t196_relat_1)).
% 0.20/0.46  fof(f50,plain,(
% 0.20/0.46    ~v1_xboole_0(k1_relat_1(sK1)) | ~spl2_1),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f17,f49,f24])).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    ( ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f12])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.20/0.46    inference(flattening,[],[f11])).
% 0.20/0.46  fof(f11,plain,(
% 0.20/0.46    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k1_relat_1(X0)))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).
% 0.20/0.46  fof(f49,plain,(
% 0.20/0.46    ~v1_xboole_0(sK1) | ~spl2_1),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f45,f22])).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f9])).
% 0.20/0.46  fof(f9,plain,(
% 0.20/0.46    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.46  fof(f45,plain,(
% 0.20/0.46    k1_xboole_0 != sK1 | ~spl2_1),
% 0.20/0.46    inference(backward_demodulation,[],[f20,f41])).
% 0.20/0.46  fof(f41,plain,(
% 0.20/0.46    k1_xboole_0 = sK0 | ~spl2_1),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f30,f22])).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    v1_xboole_0(sK0) | ~spl2_1),
% 0.20/0.46    inference(avatar_component_clause,[],[f28])).
% 0.20/0.46  fof(f28,plain,(
% 0.20/0.46    spl2_1 <=> v1_xboole_0(sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    sK0 != sK1),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    v1_relat_1(sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    v1_xboole_0(k1_xboole_0)),
% 0.20/0.46    inference(cnf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    v1_xboole_0(k1_xboole_0)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.46  fof(f39,plain,(
% 0.20/0.46    spl2_2),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f36])).
% 0.20/0.46  fof(f36,plain,(
% 0.20/0.46    $false | spl2_2),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f21,f34])).
% 0.20/0.46  fof(f34,plain,(
% 0.20/0.46    ~v1_xboole_0(k1_xboole_0) | spl2_2),
% 0.20/0.46    inference(avatar_component_clause,[],[f32])).
% 0.20/0.46  fof(f32,plain,(
% 0.20/0.46    spl2_2 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.46  fof(f35,plain,(
% 0.20/0.46    spl2_1 | ~spl2_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f26,f32,f28])).
% 0.20/0.46  fof(f26,plain,(
% 0.20/0.46    ~v1_xboole_0(k1_xboole_0) | v1_xboole_0(sK0)),
% 0.20/0.46    inference(global_subsumption,[],[f16,f25])).
% 0.20/0.46  fof(f25,plain,(
% 0.20/0.46    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(sK0) | v1_xboole_0(sK0)),
% 0.20/0.46    inference(superposition,[],[f24,f18])).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    k1_xboole_0 = k1_relat_1(sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    v1_relat_1(sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (10174)------------------------------
% 0.20/0.46  % (10174)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (10174)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (10174)Memory used [KB]: 10618
% 0.20/0.46  % (10174)Time elapsed: 0.055 s
% 0.20/0.46  % (10174)------------------------------
% 0.20/0.46  % (10174)------------------------------
% 0.20/0.47  % (10162)Success in time 0.11 s
%------------------------------------------------------------------------------
