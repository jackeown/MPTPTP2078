%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 103 expanded)
%              Number of leaves         :   19 (  49 expanded)
%              Depth                    :    6
%              Number of atoms          :  150 ( 250 expanded)
%              Number of equality atoms :   47 (  81 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f155,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f25,f30,f35,f39,f43,f47,f51,f63,f69,f92,f102,f145,f152])).

fof(f152,plain,
    ( spl2_14
    | ~ spl2_23 ),
    inference(avatar_contradiction_clause,[],[f151])).

fof(f151,plain,
    ( $false
    | spl2_14
    | ~ spl2_23 ),
    inference(trivial_inequality_removal,[],[f148])).

fof(f148,plain,
    ( k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(sK1))
    | spl2_14
    | ~ spl2_23 ),
    inference(superposition,[],[f91,f144])).

fof(f144,plain,
    ( ! [X0] : k7_relat_1(sK0,X0) = k7_relat_1(sK0,k3_xboole_0(k1_relat_1(sK0),X0))
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl2_23
  <=> ! [X0] : k7_relat_1(sK0,X0) = k7_relat_1(sK0,k3_xboole_0(k1_relat_1(sK0),X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f91,plain,
    ( k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))
    | spl2_14 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl2_14
  <=> k7_relat_1(sK0,k1_relat_1(sK1)) = k7_relat_1(sK0,k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f145,plain,
    ( spl2_23
    | ~ spl2_9
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f141,f100,f60,f143])).

fof(f60,plain,
    ( spl2_9
  <=> sK0 = k7_relat_1(sK0,k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f100,plain,
    ( spl2_16
  <=> ! [X3,X2] : k7_relat_1(k7_relat_1(sK0,X2),X3) = k7_relat_1(sK0,k3_xboole_0(X2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f141,plain,
    ( ! [X0] : k7_relat_1(sK0,X0) = k7_relat_1(sK0,k3_xboole_0(k1_relat_1(sK0),X0))
    | ~ spl2_9
    | ~ spl2_16 ),
    inference(superposition,[],[f101,f62])).

fof(f62,plain,
    ( sK0 = k7_relat_1(sK0,k1_relat_1(sK0))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f60])).

fof(f101,plain,
    ( ! [X2,X3] : k7_relat_1(k7_relat_1(sK0,X2),X3) = k7_relat_1(sK0,k3_xboole_0(X2,X3))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f100])).

fof(f102,plain,
    ( spl2_16
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f94,f49,f32,f100])).

fof(f32,plain,
    ( spl2_3
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f49,plain,
    ( spl2_7
  <=> ! [X1,X0,X2] :
        ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f94,plain,
    ( ! [X2,X3] : k7_relat_1(k7_relat_1(sK0,X2),X3) = k7_relat_1(sK0,k3_xboole_0(X2,X3))
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(resolution,[],[f50,f34])).

fof(f34,plain,
    ( v1_relat_1(sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f32])).

fof(f50,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f49])).

fof(f92,plain,
    ( ~ spl2_14
    | spl2_1
    | ~ spl2_5
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f87,f67,f41,f22,f89])).

fof(f22,plain,
    ( spl2_1
  <=> k7_relat_1(sK0,k1_relat_1(sK1)) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f41,plain,
    ( spl2_5
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f67,plain,
    ( spl2_10
  <=> ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k3_xboole_0(k1_relat_1(sK1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f87,plain,
    ( k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))
    | spl2_1
    | ~ spl2_5
    | ~ spl2_10 ),
    inference(forward_demodulation,[],[f86,f42])).

fof(f42,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f41])).

fof(f86,plain,
    ( k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k3_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0)))
    | spl2_1
    | ~ spl2_10 ),
    inference(superposition,[],[f24,f68])).

fof(f68,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k3_xboole_0(k1_relat_1(sK1),X0)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f67])).

fof(f24,plain,
    ( k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f22])).

fof(f69,plain,
    ( spl2_10
    | ~ spl2_2
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f64,f45,f27,f67])).

fof(f27,plain,
    ( spl2_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f45,plain,
    ( spl2_6
  <=> ! [X1,X0] :
        ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f64,plain,
    ( ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k3_xboole_0(k1_relat_1(sK1),X0)
    | ~ spl2_2
    | ~ spl2_6 ),
    inference(resolution,[],[f46,f29])).

fof(f29,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f27])).

fof(f46,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f45])).

fof(f63,plain,
    ( spl2_9
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f53,f37,f32,f60])).

fof(f37,plain,
    ( spl2_4
  <=> ! [X0] :
        ( k7_relat_1(X0,k1_relat_1(X0)) = X0
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f53,plain,
    ( sK0 = k7_relat_1(sK0,k1_relat_1(sK0))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(resolution,[],[f38,f34])).

fof(f38,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k7_relat_1(X0,k1_relat_1(X0)) = X0 )
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f37])).

fof(f51,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f20,f49])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

fof(f47,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f19,f45])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f43,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f18,f41])).

fof(f18,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f39,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f17,f37])).

fof(f17,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

fof(f35,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f14,f32])).

fof(f14,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f12,f11])).

fof(f11,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k7_relat_1(X0,k1_relat_1(X1)) != k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k7_relat_1(sK0,k1_relat_1(X1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(X1,k1_relat_1(sK0))))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X1] :
        ( k7_relat_1(sK0,k1_relat_1(X1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(X1,k1_relat_1(sK0))))
        & v1_relat_1(X1) )
   => ( k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k7_relat_1(X0,k1_relat_1(X1)) != k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t189_relat_1)).

fof(f30,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f15,f27])).

fof(f15,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f25,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f16,f22])).

fof(f16,plain,(
    k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:43:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (27564)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.41  % (27565)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.41  % (27564)Refutation found. Thanks to Tanya!
% 0.21/0.41  % SZS status Theorem for theBenchmark
% 0.21/0.41  % SZS output start Proof for theBenchmark
% 0.21/0.41  fof(f155,plain,(
% 0.21/0.41    $false),
% 0.21/0.41    inference(avatar_sat_refutation,[],[f25,f30,f35,f39,f43,f47,f51,f63,f69,f92,f102,f145,f152])).
% 0.21/0.41  fof(f152,plain,(
% 0.21/0.41    spl2_14 | ~spl2_23),
% 0.21/0.41    inference(avatar_contradiction_clause,[],[f151])).
% 0.21/0.41  fof(f151,plain,(
% 0.21/0.41    $false | (spl2_14 | ~spl2_23)),
% 0.21/0.41    inference(trivial_inequality_removal,[],[f148])).
% 0.21/0.41  fof(f148,plain,(
% 0.21/0.41    k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(sK1)) | (spl2_14 | ~spl2_23)),
% 0.21/0.41    inference(superposition,[],[f91,f144])).
% 0.21/0.41  fof(f144,plain,(
% 0.21/0.41    ( ! [X0] : (k7_relat_1(sK0,X0) = k7_relat_1(sK0,k3_xboole_0(k1_relat_1(sK0),X0))) ) | ~spl2_23),
% 0.21/0.41    inference(avatar_component_clause,[],[f143])).
% 0.21/0.41  fof(f143,plain,(
% 0.21/0.41    spl2_23 <=> ! [X0] : k7_relat_1(sK0,X0) = k7_relat_1(sK0,k3_xboole_0(k1_relat_1(sK0),X0))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.21/0.41  fof(f91,plain,(
% 0.21/0.41    k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) | spl2_14),
% 0.21/0.41    inference(avatar_component_clause,[],[f89])).
% 0.21/0.41  fof(f89,plain,(
% 0.21/0.41    spl2_14 <=> k7_relat_1(sK0,k1_relat_1(sK1)) = k7_relat_1(sK0,k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.21/0.41  fof(f145,plain,(
% 0.21/0.41    spl2_23 | ~spl2_9 | ~spl2_16),
% 0.21/0.41    inference(avatar_split_clause,[],[f141,f100,f60,f143])).
% 0.21/0.41  fof(f60,plain,(
% 0.21/0.41    spl2_9 <=> sK0 = k7_relat_1(sK0,k1_relat_1(sK0))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.41  fof(f100,plain,(
% 0.21/0.41    spl2_16 <=> ! [X3,X2] : k7_relat_1(k7_relat_1(sK0,X2),X3) = k7_relat_1(sK0,k3_xboole_0(X2,X3))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.21/0.41  fof(f141,plain,(
% 0.21/0.41    ( ! [X0] : (k7_relat_1(sK0,X0) = k7_relat_1(sK0,k3_xboole_0(k1_relat_1(sK0),X0))) ) | (~spl2_9 | ~spl2_16)),
% 0.21/0.41    inference(superposition,[],[f101,f62])).
% 0.21/0.41  fof(f62,plain,(
% 0.21/0.41    sK0 = k7_relat_1(sK0,k1_relat_1(sK0)) | ~spl2_9),
% 0.21/0.41    inference(avatar_component_clause,[],[f60])).
% 0.21/0.41  fof(f101,plain,(
% 0.21/0.41    ( ! [X2,X3] : (k7_relat_1(k7_relat_1(sK0,X2),X3) = k7_relat_1(sK0,k3_xboole_0(X2,X3))) ) | ~spl2_16),
% 0.21/0.41    inference(avatar_component_clause,[],[f100])).
% 0.21/0.41  fof(f102,plain,(
% 0.21/0.41    spl2_16 | ~spl2_3 | ~spl2_7),
% 0.21/0.41    inference(avatar_split_clause,[],[f94,f49,f32,f100])).
% 0.21/0.41  fof(f32,plain,(
% 0.21/0.41    spl2_3 <=> v1_relat_1(sK0)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.41  fof(f49,plain,(
% 0.21/0.41    spl2_7 <=> ! [X1,X0,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.41  fof(f94,plain,(
% 0.21/0.41    ( ! [X2,X3] : (k7_relat_1(k7_relat_1(sK0,X2),X3) = k7_relat_1(sK0,k3_xboole_0(X2,X3))) ) | (~spl2_3 | ~spl2_7)),
% 0.21/0.41    inference(resolution,[],[f50,f34])).
% 0.21/0.41  fof(f34,plain,(
% 0.21/0.41    v1_relat_1(sK0) | ~spl2_3),
% 0.21/0.41    inference(avatar_component_clause,[],[f32])).
% 0.21/0.41  fof(f50,plain,(
% 0.21/0.41    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))) ) | ~spl2_7),
% 0.21/0.41    inference(avatar_component_clause,[],[f49])).
% 0.21/0.41  fof(f92,plain,(
% 0.21/0.41    ~spl2_14 | spl2_1 | ~spl2_5 | ~spl2_10),
% 0.21/0.41    inference(avatar_split_clause,[],[f87,f67,f41,f22,f89])).
% 0.21/0.41  fof(f22,plain,(
% 0.21/0.41    spl2_1 <=> k7_relat_1(sK0,k1_relat_1(sK1)) = k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.41  fof(f41,plain,(
% 0.21/0.41    spl2_5 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.41  fof(f67,plain,(
% 0.21/0.41    spl2_10 <=> ! [X0] : k1_relat_1(k7_relat_1(sK1,X0)) = k3_xboole_0(k1_relat_1(sK1),X0)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.41  fof(f87,plain,(
% 0.21/0.41    k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) | (spl2_1 | ~spl2_5 | ~spl2_10)),
% 0.21/0.41    inference(forward_demodulation,[],[f86,f42])).
% 0.21/0.41  fof(f42,plain,(
% 0.21/0.41    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl2_5),
% 0.21/0.41    inference(avatar_component_clause,[],[f41])).
% 0.21/0.41  fof(f86,plain,(
% 0.21/0.41    k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k3_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0))) | (spl2_1 | ~spl2_10)),
% 0.21/0.41    inference(superposition,[],[f24,f68])).
% 0.21/0.41  fof(f68,plain,(
% 0.21/0.41    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k3_xboole_0(k1_relat_1(sK1),X0)) ) | ~spl2_10),
% 0.21/0.41    inference(avatar_component_clause,[],[f67])).
% 0.21/0.42  fof(f24,plain,(
% 0.21/0.42    k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))) | spl2_1),
% 0.21/0.42    inference(avatar_component_clause,[],[f22])).
% 0.21/0.42  fof(f69,plain,(
% 0.21/0.42    spl2_10 | ~spl2_2 | ~spl2_6),
% 0.21/0.42    inference(avatar_split_clause,[],[f64,f45,f27,f67])).
% 0.21/0.42  fof(f27,plain,(
% 0.21/0.42    spl2_2 <=> v1_relat_1(sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.42  fof(f45,plain,(
% 0.21/0.42    spl2_6 <=> ! [X1,X0] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.42  fof(f64,plain,(
% 0.21/0.42    ( ! [X0] : (k1_relat_1(k7_relat_1(sK1,X0)) = k3_xboole_0(k1_relat_1(sK1),X0)) ) | (~spl2_2 | ~spl2_6)),
% 0.21/0.42    inference(resolution,[],[f46,f29])).
% 0.21/0.42  fof(f29,plain,(
% 0.21/0.42    v1_relat_1(sK1) | ~spl2_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f27])).
% 0.21/0.42  fof(f46,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)) ) | ~spl2_6),
% 0.21/0.42    inference(avatar_component_clause,[],[f45])).
% 0.21/0.42  fof(f63,plain,(
% 0.21/0.42    spl2_9 | ~spl2_3 | ~spl2_4),
% 0.21/0.42    inference(avatar_split_clause,[],[f53,f37,f32,f60])).
% 0.21/0.42  fof(f37,plain,(
% 0.21/0.42    spl2_4 <=> ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.42  fof(f53,plain,(
% 0.21/0.42    sK0 = k7_relat_1(sK0,k1_relat_1(sK0)) | (~spl2_3 | ~spl2_4)),
% 0.21/0.42    inference(resolution,[],[f38,f34])).
% 0.21/0.42  fof(f38,plain,(
% 0.21/0.42    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0) ) | ~spl2_4),
% 0.21/0.42    inference(avatar_component_clause,[],[f37])).
% 0.21/0.42  fof(f51,plain,(
% 0.21/0.42    spl2_7),
% 0.21/0.42    inference(avatar_split_clause,[],[f20,f49])).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f10])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.42    inference(ennf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).
% 0.21/0.42  fof(f47,plain,(
% 0.21/0.42    spl2_6),
% 0.21/0.42    inference(avatar_split_clause,[],[f19,f45])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f9])).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 0.21/0.42  fof(f43,plain,(
% 0.21/0.42    spl2_5),
% 0.21/0.42    inference(avatar_split_clause,[],[f18,f41])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.42  fof(f39,plain,(
% 0.21/0.42    spl2_4),
% 0.21/0.42    inference(avatar_split_clause,[],[f17,f37])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    ( ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f8])).
% 0.21/0.42  fof(f8,plain,(
% 0.21/0.42    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,axiom,(
% 0.21/0.42    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).
% 0.21/0.42  fof(f35,plain,(
% 0.21/0.42    spl2_3),
% 0.21/0.42    inference(avatar_split_clause,[],[f14,f32])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    v1_relat_1(sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f13])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    (k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f12,f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ? [X0] : (? [X1] : (k7_relat_1(X0,k1_relat_1(X1)) != k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (k7_relat_1(sK0,k1_relat_1(X1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(X1,k1_relat_1(sK0)))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ? [X1] : (k7_relat_1(sK0,k1_relat_1(X1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(X1,k1_relat_1(sK0)))) & v1_relat_1(X1)) => (k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0)))) & v1_relat_1(sK1))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f7,plain,(
% 0.21/0.42    ? [X0] : (? [X1] : (k7_relat_1(X0,k1_relat_1(X1)) != k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f6])).
% 0.21/0.42  fof(f6,negated_conjecture,(
% 0.21/0.42    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))))),
% 0.21/0.42    inference(negated_conjecture,[],[f5])).
% 0.21/0.42  fof(f5,conjecture,(
% 0.21/0.42    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t189_relat_1)).
% 0.21/0.42  fof(f30,plain,(
% 0.21/0.42    spl2_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f15,f27])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    v1_relat_1(sK1)),
% 0.21/0.42    inference(cnf_transformation,[],[f13])).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    ~spl2_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f16,f22])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    k7_relat_1(sK0,k1_relat_1(sK1)) != k7_relat_1(sK0,k1_relat_1(k7_relat_1(sK1,k1_relat_1(sK0))))),
% 0.21/0.42    inference(cnf_transformation,[],[f13])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (27564)------------------------------
% 0.21/0.42  % (27564)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (27564)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (27564)Memory used [KB]: 10618
% 0.21/0.42  % (27564)Time elapsed: 0.007 s
% 0.21/0.42  % (27564)------------------------------
% 0.21/0.42  % (27564)------------------------------
% 0.21/0.42  % (27558)Success in time 0.065 s
%------------------------------------------------------------------------------
