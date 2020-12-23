%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   37 (  50 expanded)
%              Number of leaves         :   11 (  23 expanded)
%              Depth                    :    6
%              Number of atoms          :   71 ( 101 expanded)
%              Number of equality atoms :    8 (  12 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f51,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f19,f23,f27,f31,f36,f48,f50])).

fof(f50,plain,
    ( spl2_1
    | ~ spl2_7 ),
    inference(avatar_contradiction_clause,[],[f49])).

fof(f49,plain,
    ( $false
    | spl2_1
    | ~ spl2_7 ),
    inference(resolution,[],[f47,f18])).

fof(f18,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f16])).

fof(f16,plain,
    ( spl2_1
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f47,plain,
    ( ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl2_7
  <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f48,plain,
    ( spl2_7
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f44,f34,f29,f46])).

fof(f29,plain,
    ( spl2_4
  <=> ! [X0] : m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f34,plain,
    ( spl2_5
  <=> ! [X0] : k1_xboole_0 = sK1(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f44,plain,
    ( ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(superposition,[],[f30,f35])).

fof(f35,plain,
    ( ! [X0] : k1_xboole_0 = sK1(X0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f34])).

fof(f30,plain,
    ( ! [X0] : m1_subset_1(sK1(X0),k1_zfmisc_1(X0))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f29])).

fof(f36,plain,
    ( spl2_5
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f32,f25,f21,f34])).

fof(f21,plain,
    ( spl2_2
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f25,plain,
    ( spl2_3
  <=> ! [X0] : v1_xboole_0(sK1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f32,plain,
    ( ! [X0] : k1_xboole_0 = sK1(X0)
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(resolution,[],[f22,f26])).

fof(f26,plain,
    ( ! [X0] : v1_xboole_0(sK1(X0))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f25])).

fof(f22,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f21])).

fof(f31,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f13,f29])).

fof(f13,plain,(
    ! [X0] : m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( v1_xboole_0(sK1(X0))
      & m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f2,f9])).

fof(f9,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_xboole_0(sK1(X0))
        & m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).

fof(f27,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f14,f25])).

fof(f14,plain,(
    ! [X0] : v1_xboole_0(sK1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f23,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f12,f21])).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f19,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f11,f16])).

fof(f11,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f5,f7])).

fof(f7,plain,
    ( ? [X0] : ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
   => ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0] : ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:45:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (26809)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.21/0.41  % (26806)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.41  % (26807)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.41  % (26806)Refutation found. Thanks to Tanya!
% 0.21/0.41  % SZS status Theorem for theBenchmark
% 0.21/0.41  % SZS output start Proof for theBenchmark
% 0.21/0.41  fof(f51,plain,(
% 0.21/0.41    $false),
% 0.21/0.41    inference(avatar_sat_refutation,[],[f19,f23,f27,f31,f36,f48,f50])).
% 0.21/0.41  fof(f50,plain,(
% 0.21/0.41    spl2_1 | ~spl2_7),
% 0.21/0.41    inference(avatar_contradiction_clause,[],[f49])).
% 0.21/0.41  fof(f49,plain,(
% 0.21/0.41    $false | (spl2_1 | ~spl2_7)),
% 0.21/0.41    inference(resolution,[],[f47,f18])).
% 0.21/0.41  fof(f18,plain,(
% 0.21/0.41    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) | spl2_1),
% 0.21/0.41    inference(avatar_component_clause,[],[f16])).
% 0.21/0.41  fof(f16,plain,(
% 0.21/0.41    spl2_1 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.41  fof(f47,plain,(
% 0.21/0.41    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | ~spl2_7),
% 0.21/0.41    inference(avatar_component_clause,[],[f46])).
% 0.21/0.41  fof(f46,plain,(
% 0.21/0.41    spl2_7 <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.41  fof(f48,plain,(
% 0.21/0.41    spl2_7 | ~spl2_4 | ~spl2_5),
% 0.21/0.41    inference(avatar_split_clause,[],[f44,f34,f29,f46])).
% 0.21/0.41  fof(f29,plain,(
% 0.21/0.41    spl2_4 <=> ! [X0] : m1_subset_1(sK1(X0),k1_zfmisc_1(X0))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.41  fof(f34,plain,(
% 0.21/0.41    spl2_5 <=> ! [X0] : k1_xboole_0 = sK1(X0)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.41  fof(f44,plain,(
% 0.21/0.41    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | (~spl2_4 | ~spl2_5)),
% 0.21/0.41    inference(superposition,[],[f30,f35])).
% 0.21/0.41  fof(f35,plain,(
% 0.21/0.41    ( ! [X0] : (k1_xboole_0 = sK1(X0)) ) | ~spl2_5),
% 0.21/0.41    inference(avatar_component_clause,[],[f34])).
% 0.21/0.41  fof(f30,plain,(
% 0.21/0.41    ( ! [X0] : (m1_subset_1(sK1(X0),k1_zfmisc_1(X0))) ) | ~spl2_4),
% 0.21/0.41    inference(avatar_component_clause,[],[f29])).
% 0.21/0.41  fof(f36,plain,(
% 0.21/0.41    spl2_5 | ~spl2_2 | ~spl2_3),
% 0.21/0.41    inference(avatar_split_clause,[],[f32,f25,f21,f34])).
% 0.21/0.41  fof(f21,plain,(
% 0.21/0.41    spl2_2 <=> ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.41  fof(f25,plain,(
% 0.21/0.41    spl2_3 <=> ! [X0] : v1_xboole_0(sK1(X0))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.41  fof(f32,plain,(
% 0.21/0.41    ( ! [X0] : (k1_xboole_0 = sK1(X0)) ) | (~spl2_2 | ~spl2_3)),
% 0.21/0.41    inference(resolution,[],[f22,f26])).
% 0.21/0.41  fof(f26,plain,(
% 0.21/0.41    ( ! [X0] : (v1_xboole_0(sK1(X0))) ) | ~spl2_3),
% 0.21/0.41    inference(avatar_component_clause,[],[f25])).
% 0.21/0.41  fof(f22,plain,(
% 0.21/0.41    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl2_2),
% 0.21/0.41    inference(avatar_component_clause,[],[f21])).
% 0.21/0.41  fof(f31,plain,(
% 0.21/0.41    spl2_4),
% 0.21/0.41    inference(avatar_split_clause,[],[f13,f29])).
% 0.21/0.41  fof(f13,plain,(
% 0.21/0.41    ( ! [X0] : (m1_subset_1(sK1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.41    inference(cnf_transformation,[],[f10])).
% 0.21/0.41  fof(f10,plain,(
% 0.21/0.41    ! [X0] : (v1_xboole_0(sK1(X0)) & m1_subset_1(sK1(X0),k1_zfmisc_1(X0)))),
% 0.21/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f2,f9])).
% 0.21/0.41  fof(f9,plain,(
% 0.21/0.41    ! [X0] : (? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (v1_xboole_0(sK1(X0)) & m1_subset_1(sK1(X0),k1_zfmisc_1(X0))))),
% 0.21/0.41    introduced(choice_axiom,[])).
% 0.21/0.41  fof(f2,axiom,(
% 0.21/0.41    ! [X0] : ? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).
% 0.21/0.41  fof(f27,plain,(
% 0.21/0.41    spl2_3),
% 0.21/0.41    inference(avatar_split_clause,[],[f14,f25])).
% 0.21/0.41  fof(f14,plain,(
% 0.21/0.41    ( ! [X0] : (v1_xboole_0(sK1(X0))) )),
% 0.21/0.41    inference(cnf_transformation,[],[f10])).
% 0.21/0.41  fof(f23,plain,(
% 0.21/0.41    spl2_2),
% 0.21/0.41    inference(avatar_split_clause,[],[f12,f21])).
% 0.21/0.41  fof(f12,plain,(
% 0.21/0.41    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f6])).
% 0.21/0.41  fof(f6,plain,(
% 0.21/0.41    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.41    inference(ennf_transformation,[],[f1])).
% 0.21/0.41  fof(f1,axiom,(
% 0.21/0.41    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.41  fof(f19,plain,(
% 0.21/0.41    ~spl2_1),
% 0.21/0.41    inference(avatar_split_clause,[],[f11,f16])).
% 0.21/0.41  fof(f11,plain,(
% 0.21/0.41    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))),
% 0.21/0.41    inference(cnf_transformation,[],[f8])).
% 0.21/0.41  fof(f8,plain,(
% 0.21/0.41    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))),
% 0.21/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f5,f7])).
% 0.21/0.41  fof(f7,plain,(
% 0.21/0.41    ? [X0] : ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) => ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))),
% 0.21/0.41    introduced(choice_axiom,[])).
% 0.21/0.41  fof(f5,plain,(
% 0.21/0.41    ? [X0] : ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.41    inference(ennf_transformation,[],[f4])).
% 0.21/0.41  fof(f4,negated_conjecture,(
% 0.21/0.41    ~! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.41    inference(negated_conjecture,[],[f3])).
% 0.21/0.41  fof(f3,conjecture,(
% 0.21/0.41    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.41  % SZS output end Proof for theBenchmark
% 0.21/0.41  % (26806)------------------------------
% 0.21/0.41  % (26806)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.41  % (26806)Termination reason: Refutation
% 0.21/0.41  
% 0.21/0.41  % (26806)Memory used [KB]: 10490
% 0.21/0.41  % (26806)Time elapsed: 0.004 s
% 0.21/0.41  % (26806)------------------------------
% 0.21/0.41  % (26806)------------------------------
% 0.21/0.42  % (26800)Success in time 0.061 s
%------------------------------------------------------------------------------
