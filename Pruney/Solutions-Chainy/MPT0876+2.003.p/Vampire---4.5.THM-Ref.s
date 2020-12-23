%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:51 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 119 expanded)
%              Number of leaves         :   14 (  45 expanded)
%              Depth                    :    8
%              Number of atoms          :  191 ( 492 expanded)
%              Number of equality atoms :  130 ( 406 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f155,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f37,f42,f55,f60,f103,f114,f138,f148,f154])).

fof(f154,plain,
    ( spl6_1
    | spl6_2
    | spl6_5
    | ~ spl6_13 ),
    inference(avatar_contradiction_clause,[],[f153])).

fof(f153,plain,
    ( $false
    | spl6_1
    | spl6_2
    | spl6_5
    | ~ spl6_13 ),
    inference(unit_resulting_resolution,[],[f36,f31,f137,f50,f20])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(f50,plain,
    ( sK1 != sK4
    | spl6_5 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl6_5
  <=> sK1 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f137,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK3,sK4)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl6_13
  <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f31,plain,
    ( k1_xboole_0 != sK0
    | spl6_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f29,plain,
    ( spl6_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f36,plain,
    ( k1_xboole_0 != sK1
    | spl6_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl6_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f148,plain,
    ( spl6_1
    | spl6_2
    | spl6_4
    | ~ spl6_13 ),
    inference(avatar_contradiction_clause,[],[f141])).

fof(f141,plain,
    ( $false
    | spl6_1
    | spl6_2
    | spl6_4
    | ~ spl6_13 ),
    inference(unit_resulting_resolution,[],[f46,f31,f36,f137,f19])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f46,plain,
    ( sK0 != sK3
    | spl6_4 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl6_4
  <=> sK0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f138,plain,
    ( spl6_13
    | spl6_11
    | spl6_3
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f133,f57,f39,f100,f135])).

fof(f100,plain,
    ( spl6_11
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f39,plain,
    ( spl6_3
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f57,plain,
    ( spl6_7
  <=> k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f133,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK3,sK4)
    | ~ spl6_7 ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,
    ( ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(sK3,sK4) = X0 )
    | ~ spl6_7 ),
    inference(superposition,[],[f19,f59])).

fof(f59,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f57])).

fof(f114,plain,
    ( spl6_1
    | spl6_2
    | ~ spl6_11 ),
    inference(avatar_contradiction_clause,[],[f104])).

fof(f104,plain,
    ( $false
    | spl6_1
    | spl6_2
    | ~ spl6_11 ),
    inference(unit_resulting_resolution,[],[f36,f31,f102,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f102,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f100])).

fof(f103,plain,
    ( spl6_6
    | spl6_11
    | spl6_3
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f98,f57,f39,f100,f52])).

fof(f52,plain,
    ( spl6_6
  <=> sK2 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f98,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | sK2 = sK5
    | ~ spl6_7 ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,
    ( ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | sK5 = X1 )
    | ~ spl6_7 ),
    inference(superposition,[],[f20,f59])).

fof(f60,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f25,f57])).

fof(f25,plain,(
    k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) ),
    inference(definition_unfolding,[],[f14,f24,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f14,plain,(
    k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ( sK2 != sK5
      | sK1 != sK4
      | sK0 != sK3 )
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f7,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ( X2 != X5
          | X1 != X4
          | X0 != X3 )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) )
   => ( ( sK2 != sK5
        | sK1 != sK4
        | sK0 != sK3 )
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,sK5) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ( X2 != X5
        | X1 != X4
        | X0 != X3 )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ( X2 != X5
        | X1 != X4
        | X0 != X3 )
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
       => ( ( X2 = X5
            & X1 = X4
            & X0 = X3 )
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
     => ( ( X2 = X5
          & X1 = X4
          & X0 = X3 )
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_mcart_1)).

fof(f55,plain,
    ( ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f18,f52,f48,f44])).

fof(f18,plain,
    ( sK2 != sK5
    | sK1 != sK4
    | sK0 != sK3 ),
    inference(cnf_transformation,[],[f11])).

fof(f42,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f17,f39])).

fof(f17,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f11])).

fof(f37,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f16,f34])).

fof(f16,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f11])).

fof(f32,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f15,f29])).

fof(f15,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:49:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (17182)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.46  % (17167)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.47  % (17182)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f155,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f32,f37,f42,f55,f60,f103,f114,f138,f148,f154])).
% 0.21/0.47  fof(f154,plain,(
% 0.21/0.47    spl6_1 | spl6_2 | spl6_5 | ~spl6_13),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f153])).
% 0.21/0.48  fof(f153,plain,(
% 0.21/0.48    $false | (spl6_1 | spl6_2 | spl6_5 | ~spl6_13)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f36,f31,f137,f50,f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | X1 = X3) )),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3))),
% 0.21/0.48    inference(flattening,[],[f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    sK1 != sK4 | spl6_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f48])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    spl6_5 <=> sK1 = sK4),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.48  fof(f137,plain,(
% 0.21/0.48    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK3,sK4) | ~spl6_13),
% 0.21/0.48    inference(avatar_component_clause,[],[f135])).
% 0.21/0.48  fof(f135,plain,(
% 0.21/0.48    spl6_13 <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK3,sK4)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    k1_xboole_0 != sK0 | spl6_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    spl6_1 <=> k1_xboole_0 = sK0),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    k1_xboole_0 != sK1 | spl6_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    spl6_2 <=> k1_xboole_0 = sK1),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.48  fof(f148,plain,(
% 0.21/0.48    spl6_1 | spl6_2 | spl6_4 | ~spl6_13),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f141])).
% 0.21/0.48  fof(f141,plain,(
% 0.21/0.48    $false | (spl6_1 | spl6_2 | spl6_4 | ~spl6_13)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f46,f31,f36,f137,f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | X0 = X2) )),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    sK0 != sK3 | spl6_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    spl6_4 <=> sK0 = sK3),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.48  fof(f138,plain,(
% 0.21/0.48    spl6_13 | spl6_11 | spl6_3 | ~spl6_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f133,f57,f39,f100,f135])).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    spl6_11 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    spl6_3 <=> k1_xboole_0 = sK2),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    spl6_7 <=> k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.48  fof(f133,plain,(
% 0.21/0.48    k1_xboole_0 = sK2 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK3,sK4) | ~spl6_7),
% 0.21/0.48    inference(equality_resolution,[],[f80])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(sK3,sK4) = X0) ) | ~spl6_7),
% 0.21/0.48    inference(superposition,[],[f19,f59])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5) | ~spl6_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f57])).
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    spl6_1 | spl6_2 | ~spl6_11),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f104])).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    $false | (spl6_1 | spl6_2 | ~spl6_11)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f36,f31,f102,f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k1_xboole_0 | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.48    inference(flattening,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.48    inference(nnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl6_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f100])).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    spl6_6 | spl6_11 | spl6_3 | ~spl6_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f98,f57,f39,f100,f52])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    spl6_6 <=> sK2 = sK5),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    k1_xboole_0 = sK2 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | sK2 = sK5 | ~spl6_7),
% 0.21/0.48    inference(equality_resolution,[],[f89])).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | sK5 = X1) ) | ~spl6_7),
% 0.21/0.48    inference(superposition,[],[f20,f59])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    spl6_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f25,f57])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)),
% 0.21/0.48    inference(definition_unfolding,[],[f14,f24,f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,sK5)),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    (sK2 != sK5 | sK1 != sK4 | sK0 != sK3) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,sK5)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f7,f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3,X4,X5] : ((X2 != X5 | X1 != X4 | X0 != X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)) => ((sK2 != sK5 | sK1 != sK4 | sK0 != sK3) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,sK5))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f7,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3,X4,X5] : ((X2 != X5 | X1 != X4 | X0 != X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5))),
% 0.21/0.48    inference(flattening,[],[f6])).
% 0.21/0.48  fof(f6,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3,X4,X5] : (((X2 != X5 | X1 != X4 | X0 != X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2,X3,X4,X5] : (k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) => ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.48    inference(negated_conjecture,[],[f4])).
% 0.21/0.48  fof(f4,conjecture,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4,X5] : (k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) => ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_mcart_1)).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ~spl6_4 | ~spl6_5 | ~spl6_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f18,f52,f48,f44])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    sK2 != sK5 | sK1 != sK4 | sK0 != sK3),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ~spl6_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f17,f39])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    k1_xboole_0 != sK2),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ~spl6_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f16,f34])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    k1_xboole_0 != sK1),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ~spl6_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f15,f29])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    k1_xboole_0 != sK0),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (17182)------------------------------
% 0.21/0.48  % (17182)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (17182)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (17182)Memory used [KB]: 10746
% 0.21/0.48  % (17182)Time elapsed: 0.071 s
% 0.21/0.48  % (17182)------------------------------
% 0.21/0.48  % (17182)------------------------------
% 0.21/0.48  % (17158)Success in time 0.124 s
%------------------------------------------------------------------------------
