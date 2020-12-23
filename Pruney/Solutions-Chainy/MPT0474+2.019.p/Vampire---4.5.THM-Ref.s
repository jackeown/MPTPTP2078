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
% DateTime   : Thu Dec  3 12:48:14 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   55 (  72 expanded)
%              Number of leaves         :   16 (  31 expanded)
%              Depth                    :    7
%              Number of atoms          :  113 ( 152 expanded)
%              Number of equality atoms :   37 (  50 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f65,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f27,f32,f36,f40,f44,f50,f54,f59,f64])).

fof(f64,plain,
    ( ~ spl1_1
    | spl1_2
    | ~ spl1_6
    | ~ spl1_8 ),
    inference(avatar_contradiction_clause,[],[f63])).

fof(f63,plain,
    ( $false
    | ~ spl1_1
    | spl1_2
    | ~ spl1_6
    | ~ spl1_8 ),
    inference(subsumption_resolution,[],[f62,f31])).

fof(f31,plain,
    ( k1_xboole_0 != k4_relat_1(k1_xboole_0)
    | spl1_2 ),
    inference(avatar_component_clause,[],[f29])).

fof(f29,plain,
    ( spl1_2
  <=> k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f62,plain,
    ( k1_xboole_0 = k4_relat_1(k1_xboole_0)
    | ~ spl1_1
    | ~ spl1_6
    | ~ spl1_8 ),
    inference(forward_demodulation,[],[f61,f49])).

fof(f49,plain,
    ( ! [X0] : k1_xboole_0 = k6_subset_1(X0,X0)
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl1_6
  <=> ! [X0] : k1_xboole_0 = k6_subset_1(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f61,plain,
    ( k1_xboole_0 = k4_relat_1(k6_subset_1(sK0,sK0))
    | ~ spl1_1
    | ~ spl1_6
    | ~ spl1_8 ),
    inference(forward_demodulation,[],[f60,f49])).

fof(f60,plain,
    ( k4_relat_1(k6_subset_1(sK0,sK0)) = k6_subset_1(k4_relat_1(sK0),k4_relat_1(sK0))
    | ~ spl1_1
    | ~ spl1_8 ),
    inference(resolution,[],[f58,f26])).

fof(f26,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f24])).

fof(f24,plain,
    ( spl1_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f58,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k4_relat_1(k6_subset_1(sK0,X0)) = k6_subset_1(k4_relat_1(sK0),k4_relat_1(X0)) )
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl1_8
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | k4_relat_1(k6_subset_1(sK0,X0)) = k6_subset_1(k4_relat_1(sK0),k4_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f59,plain,
    ( spl1_8
    | ~ spl1_1
    | ~ spl1_7 ),
    inference(avatar_split_clause,[],[f55,f52,f24,f57])).

fof(f52,plain,
    ( spl1_7
  <=> ! [X1,X0] :
        ( k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f55,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k4_relat_1(k6_subset_1(sK0,X0)) = k6_subset_1(k4_relat_1(sK0),k4_relat_1(X0)) )
    | ~ spl1_1
    | ~ spl1_7 ),
    inference(resolution,[],[f53,f26])).

fof(f53,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) )
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f52])).

fof(f54,plain,(
    spl1_7 ),
    inference(avatar_split_clause,[],[f17,f52])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_relat_1)).

fof(f50,plain,
    ( spl1_6
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f46,f42,f38,f34,f48])).

fof(f34,plain,
    ( spl1_3
  <=> ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f38,plain,
    ( spl1_4
  <=> ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f42,plain,
    ( spl1_5
  <=> ! [X1,X0] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k6_subset_1(X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f46,plain,
    ( ! [X0] : k1_xboole_0 = k6_subset_1(X0,X0)
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(forward_demodulation,[],[f45,f35])).

fof(f35,plain,
    ( ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f34])).

fof(f45,plain,
    ( ! [X0] : k5_xboole_0(X0,X0) = k6_subset_1(X0,X0)
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(superposition,[],[f43,f39])).

fof(f39,plain,
    ( ! [X0] : k3_xboole_0(X0,X0) = X0
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f38])).

fof(f43,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k6_subset_1(X0,X1)
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f42])).

fof(f44,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f22,f42])).

fof(f22,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k6_subset_1(X0,X1) ),
    inference(definition_unfolding,[],[f20,f19])).

fof(f19,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f20,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f40,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f18,f38])).

fof(f18,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f36,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f16,f34])).

fof(f16,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f32,plain,(
    ~ spl1_2 ),
    inference(avatar_split_clause,[],[f15,f29])).

fof(f15,plain,(
    k1_xboole_0 != k4_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    k1_xboole_0 != k4_relat_1(k1_xboole_0) ),
    inference(flattening,[],[f8])).

fof(f8,negated_conjecture,(
    k1_xboole_0 != k4_relat_1(k1_xboole_0) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_relat_1)).

fof(f27,plain,(
    spl1_1 ),
    inference(avatar_split_clause,[],[f21,f24])).

fof(f21,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f13])).

fof(f13,plain,
    ( ? [X0] : v1_relat_1(X0)
   => v1_relat_1(sK0) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] : v1_relat_1(X0) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ? [X0] :
      ( v1_relat_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:24:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.48  % (20823)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.48  % (20815)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.49  % (20815)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f27,f32,f36,f40,f44,f50,f54,f59,f64])).
% 0.22/0.49  fof(f64,plain,(
% 0.22/0.49    ~spl1_1 | spl1_2 | ~spl1_6 | ~spl1_8),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f63])).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    $false | (~spl1_1 | spl1_2 | ~spl1_6 | ~spl1_8)),
% 0.22/0.49    inference(subsumption_resolution,[],[f62,f31])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    k1_xboole_0 != k4_relat_1(k1_xboole_0) | spl1_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f29])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    spl1_2 <=> k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    k1_xboole_0 = k4_relat_1(k1_xboole_0) | (~spl1_1 | ~spl1_6 | ~spl1_8)),
% 0.22/0.49    inference(forward_demodulation,[],[f61,f49])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    ( ! [X0] : (k1_xboole_0 = k6_subset_1(X0,X0)) ) | ~spl1_6),
% 0.22/0.49    inference(avatar_component_clause,[],[f48])).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    spl1_6 <=> ! [X0] : k1_xboole_0 = k6_subset_1(X0,X0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.22/0.49  fof(f61,plain,(
% 0.22/0.49    k1_xboole_0 = k4_relat_1(k6_subset_1(sK0,sK0)) | (~spl1_1 | ~spl1_6 | ~spl1_8)),
% 0.22/0.49    inference(forward_demodulation,[],[f60,f49])).
% 0.22/0.49  fof(f60,plain,(
% 0.22/0.49    k4_relat_1(k6_subset_1(sK0,sK0)) = k6_subset_1(k4_relat_1(sK0),k4_relat_1(sK0)) | (~spl1_1 | ~spl1_8)),
% 0.22/0.49    inference(resolution,[],[f58,f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    v1_relat_1(sK0) | ~spl1_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    spl1_1 <=> v1_relat_1(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.22/0.49  fof(f58,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_relat_1(X0) | k4_relat_1(k6_subset_1(sK0,X0)) = k6_subset_1(k4_relat_1(sK0),k4_relat_1(X0))) ) | ~spl1_8),
% 0.22/0.49    inference(avatar_component_clause,[],[f57])).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    spl1_8 <=> ! [X0] : (~v1_relat_1(X0) | k4_relat_1(k6_subset_1(sK0,X0)) = k6_subset_1(k4_relat_1(sK0),k4_relat_1(X0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.22/0.49  fof(f59,plain,(
% 0.22/0.49    spl1_8 | ~spl1_1 | ~spl1_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f55,f52,f24,f57])).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    spl1_7 <=> ! [X1,X0] : (k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_relat_1(X0) | k4_relat_1(k6_subset_1(sK0,X0)) = k6_subset_1(k4_relat_1(sK0),k4_relat_1(X0))) ) | (~spl1_1 | ~spl1_7)),
% 0.22/0.49    inference(resolution,[],[f53,f26])).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1))) ) | ~spl1_7),
% 0.22/0.49    inference(avatar_component_clause,[],[f52])).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    spl1_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f17,f52])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_relat_1)).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    spl1_6 | ~spl1_3 | ~spl1_4 | ~spl1_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f46,f42,f38,f34,f48])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    spl1_3 <=> ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    spl1_4 <=> ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    spl1_5 <=> ! [X1,X0] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k6_subset_1(X0,X1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    ( ! [X0] : (k1_xboole_0 = k6_subset_1(X0,X0)) ) | (~spl1_3 | ~spl1_4 | ~spl1_5)),
% 0.22/0.49    inference(forward_demodulation,[],[f45,f35])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) ) | ~spl1_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f34])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    ( ! [X0] : (k5_xboole_0(X0,X0) = k6_subset_1(X0,X0)) ) | (~spl1_4 | ~spl1_5)),
% 0.22/0.49    inference(superposition,[],[f43,f39])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) ) | ~spl1_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f38])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k6_subset_1(X0,X1)) ) | ~spl1_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f42])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    spl1_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f22,f42])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k6_subset_1(X0,X1)) )),
% 0.22/0.49    inference(definition_unfolding,[],[f20,f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    spl1_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f18,f38])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,plain,(
% 0.22/0.49    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.49    inference(rectify,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    spl1_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f16,f34])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ~spl1_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f15,f29])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    k1_xboole_0 != k4_relat_1(k1_xboole_0)),
% 0.22/0.49    inference(cnf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,plain,(
% 0.22/0.49    k1_xboole_0 != k4_relat_1(k1_xboole_0)),
% 0.22/0.49    inference(flattening,[],[f8])).
% 0.22/0.49  fof(f8,negated_conjecture,(
% 0.22/0.49    ~k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 0.22/0.49    inference(negated_conjecture,[],[f7])).
% 0.22/0.49  fof(f7,conjecture,(
% 0.22/0.49    k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_relat_1)).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    spl1_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f21,f24])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    v1_relat_1(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    v1_relat_1(sK0)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ? [X0] : v1_relat_1(X0) => v1_relat_1(sK0)),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ? [X0] : v1_relat_1(X0)),
% 0.22/0.49    inference(pure_predicate_removal,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ? [X0] : (v1_relat_1(X0) & ~v1_xboole_0(X0))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_relat_1)).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (20815)------------------------------
% 0.22/0.49  % (20815)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (20815)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (20815)Memory used [KB]: 6140
% 0.22/0.49  % (20815)Time elapsed: 0.075 s
% 0.22/0.49  % (20815)------------------------------
% 0.22/0.49  % (20815)------------------------------
% 0.22/0.49  % (20807)Success in time 0.136 s
%------------------------------------------------------------------------------
