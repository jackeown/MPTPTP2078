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
% DateTime   : Thu Dec  3 12:51:03 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   46 (  87 expanded)
%              Number of leaves         :   11 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :  119 ( 321 expanded)
%              Number of equality atoms :   35 ( 146 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f112,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f55,f61,f68,f82,f111])).

fof(f111,plain,
    ( ~ spl2_1
    | ~ spl2_3 ),
    inference(avatar_contradiction_clause,[],[f110])).

fof(f110,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f36,f106,f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f106,plain,
    ( k1_xboole_0 != sK1
    | ~ spl2_1 ),
    inference(backward_demodulation,[],[f18,f78])).

fof(f78,plain,
    ( k1_xboole_0 = sK0
    | ~ spl2_1 ),
    inference(resolution,[],[f26,f19])).

fof(f26,plain,
    ( v1_xboole_0(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f24])).

fof(f24,plain,
    ( spl2_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f18,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( sK0 != sK1
    & k1_xboole_0 = k2_relat_1(sK1)
    & k1_xboole_0 = k2_relat_1(sK0)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f12,f11])).

fof(f11,plain,
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

fof(f12,plain,
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

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & k1_xboole_0 = k2_relat_1(X1)
          & k1_xboole_0 = k2_relat_1(X0)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & k1_xboole_0 = k2_relat_1(X1)
          & k1_xboole_0 = k2_relat_1(X0)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( ( k1_xboole_0 = k2_relat_1(X1)
                & k1_xboole_0 = k2_relat_1(X0) )
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( ( k1_xboole_0 = k2_relat_1(X1)
              & k1_xboole_0 = k2_relat_1(X0) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t197_relat_1)).

fof(f36,plain,
    ( v1_xboole_0(sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl2_3
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f82,plain,(
    spl2_7 ),
    inference(avatar_contradiction_clause,[],[f79])).

fof(f79,plain,
    ( $false
    | spl2_7 ),
    inference(unit_resulting_resolution,[],[f15,f60])).

fof(f60,plain,
    ( ~ v1_relat_1(sK1)
    | spl2_7 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl2_7
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f15,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f68,plain,(
    spl2_6 ),
    inference(avatar_contradiction_clause,[],[f62])).

fof(f62,plain,
    ( $false
    | spl2_6 ),
    inference(unit_resulting_resolution,[],[f21,f50])).

fof(f50,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl2_6 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl2_6
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f21,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f61,plain,
    ( spl2_3
    | ~ spl2_7
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f56,f48,f58,f34])).

fof(f56,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(sK1)
    | v1_xboole_0(sK1) ),
    inference(superposition,[],[f20,f17])).

fof(f17,plain,(
    k1_xboole_0 = k2_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

fof(f55,plain,(
    spl2_5 ),
    inference(avatar_contradiction_clause,[],[f52])).

fof(f52,plain,
    ( $false
    | spl2_5 ),
    inference(unit_resulting_resolution,[],[f14,f46])).

fof(f46,plain,
    ( ~ v1_relat_1(sK0)
    | spl2_5 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl2_5
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f14,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f51,plain,
    ( spl2_1
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f42,f48,f44,f24])).

fof(f42,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(sK0)
    | v1_xboole_0(sK0) ),
    inference(superposition,[],[f20,f16])).

fof(f16,plain,(
    k1_xboole_0 = k2_relat_1(sK0) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:48:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (21418)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.49  % (21418)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f112,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f51,f55,f61,f68,f82,f111])).
% 0.22/0.49  fof(f111,plain,(
% 0.22/0.49    ~spl2_1 | ~spl2_3),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f110])).
% 0.22/0.49  fof(f110,plain,(
% 0.22/0.49    $false | (~spl2_1 | ~spl2_3)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f36,f106,f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,plain,(
% 0.22/0.49    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.49  fof(f106,plain,(
% 0.22/0.49    k1_xboole_0 != sK1 | ~spl2_1),
% 0.22/0.49    inference(backward_demodulation,[],[f18,f78])).
% 0.22/0.49  fof(f78,plain,(
% 0.22/0.49    k1_xboole_0 = sK0 | ~spl2_1),
% 0.22/0.49    inference(resolution,[],[f26,f19])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    v1_xboole_0(sK0) | ~spl2_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    spl2_1 <=> v1_xboole_0(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    sK0 != sK1),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    (sK0 != sK1 & k1_xboole_0 = k2_relat_1(sK1) & k1_xboole_0 = k2_relat_1(sK0) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f12,f11])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (X0 != X1 & k1_xboole_0 = k2_relat_1(X1) & k1_xboole_0 = k2_relat_1(X0) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (sK0 != X1 & k1_xboole_0 = k2_relat_1(X1) & k1_xboole_0 = k2_relat_1(sK0) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ? [X1] : (sK0 != X1 & k1_xboole_0 = k2_relat_1(X1) & k1_xboole_0 = k2_relat_1(sK0) & v1_relat_1(X1)) => (sK0 != sK1 & k1_xboole_0 = k2_relat_1(sK1) & k1_xboole_0 = k2_relat_1(sK0) & v1_relat_1(sK1))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f7,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (X0 != X1 & k1_xboole_0 = k2_relat_1(X1) & k1_xboole_0 = k2_relat_1(X0) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.22/0.49    inference(flattening,[],[f6])).
% 0.22/0.49  fof(f6,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : ((X0 != X1 & (k1_xboole_0 = k2_relat_1(X1) & k1_xboole_0 = k2_relat_1(X0))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,negated_conjecture,(
% 0.22/0.49    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ((k1_xboole_0 = k2_relat_1(X1) & k1_xboole_0 = k2_relat_1(X0)) => X0 = X1)))),
% 0.22/0.49    inference(negated_conjecture,[],[f4])).
% 0.22/0.49  fof(f4,conjecture,(
% 0.22/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ((k1_xboole_0 = k2_relat_1(X1) & k1_xboole_0 = k2_relat_1(X0)) => X0 = X1)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t197_relat_1)).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    v1_xboole_0(sK1) | ~spl2_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f34])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    spl2_3 <=> v1_xboole_0(sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.49  fof(f82,plain,(
% 0.22/0.49    spl2_7),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f79])).
% 0.22/0.49  fof(f79,plain,(
% 0.22/0.49    $false | spl2_7),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f15,f60])).
% 0.22/0.49  fof(f60,plain,(
% 0.22/0.49    ~v1_relat_1(sK1) | spl2_7),
% 0.22/0.49    inference(avatar_component_clause,[],[f58])).
% 0.22/0.49  fof(f58,plain,(
% 0.22/0.49    spl2_7 <=> v1_relat_1(sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    v1_relat_1(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f68,plain,(
% 0.22/0.49    spl2_6),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f62])).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    $false | spl2_6),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f21,f50])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    ~v1_xboole_0(k1_xboole_0) | spl2_6),
% 0.22/0.49    inference(avatar_component_clause,[],[f48])).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    spl2_6 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    v1_xboole_0(k1_xboole_0)),
% 0.22/0.49    inference(cnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    v1_xboole_0(k1_xboole_0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.49  fof(f61,plain,(
% 0.22/0.49    spl2_3 | ~spl2_7 | ~spl2_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f56,f48,f58,f34])).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(sK1) | v1_xboole_0(sK1)),
% 0.22/0.49    inference(superposition,[],[f20,f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    k1_xboole_0 = k2_relat_1(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,plain,(
% 0.22/0.49    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.22/0.49    inference(flattening,[],[f9])).
% 0.22/0.49  fof(f9,plain,(
% 0.22/0.49    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_relat_1(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    spl2_5),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f52])).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    $false | spl2_5),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f14,f46])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    ~v1_relat_1(sK0) | spl2_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f44])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    spl2_5 <=> v1_relat_1(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    v1_relat_1(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    spl2_1 | ~spl2_5 | ~spl2_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f42,f48,f44,f24])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(sK0) | v1_xboole_0(sK0)),
% 0.22/0.49    inference(superposition,[],[f20,f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    k1_xboole_0 = k2_relat_1(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (21418)------------------------------
% 0.22/0.49  % (21418)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (21418)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (21418)Memory used [KB]: 6140
% 0.22/0.49  % (21418)Time elapsed: 0.047 s
% 0.22/0.49  % (21418)------------------------------
% 0.22/0.49  % (21418)------------------------------
% 0.22/0.50  % (21407)Success in time 0.128 s
%------------------------------------------------------------------------------
