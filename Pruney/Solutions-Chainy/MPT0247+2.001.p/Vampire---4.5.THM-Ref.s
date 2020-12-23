%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:49 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 141 expanded)
%              Number of leaves         :    9 (  46 expanded)
%              Depth                    :   11
%              Number of atoms          :  239 ( 677 expanded)
%              Number of equality atoms :  114 ( 433 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f117,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f39,f44,f49,f50,f56,f68,f74,f81,f89,f116])).

fof(f116,plain,
    ( ~ spl3_1
    | spl3_2
    | spl3_3
    | spl3_4
    | spl3_5 ),
    inference(avatar_contradiction_clause,[],[f115])).

fof(f115,plain,
    ( $false
    | ~ spl3_1
    | spl3_2
    | spl3_3
    | spl3_4
    | spl3_5 ),
    inference(subsumption_resolution,[],[f114,f33])).

fof(f33,plain,
    ( sK0 != k2_tarski(sK1,sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl3_2
  <=> sK0 = k2_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f114,plain,
    ( sK0 = k2_tarski(sK1,sK2)
    | ~ spl3_1
    | spl3_3
    | spl3_4
    | spl3_5 ),
    inference(subsumption_resolution,[],[f113,f48])).

fof(f48,plain,
    ( k1_xboole_0 != sK0
    | spl3_5 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl3_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f113,plain,
    ( k1_xboole_0 = sK0
    | sK0 = k2_tarski(sK1,sK2)
    | ~ spl3_1
    | spl3_3
    | spl3_4 ),
    inference(subsumption_resolution,[],[f112,f43])).

fof(f43,plain,
    ( sK0 != k1_tarski(sK1)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl3_4
  <=> sK0 = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f112,plain,
    ( sK0 = k1_tarski(sK1)
    | k1_xboole_0 = sK0
    | sK0 = k2_tarski(sK1,sK2)
    | ~ spl3_1
    | spl3_3 ),
    inference(subsumption_resolution,[],[f100,f38])).

% (5869)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f38,plain,
    ( sK0 != k1_tarski(sK2)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl3_3
  <=> sK0 = k1_tarski(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f100,plain,
    ( sK0 = k1_tarski(sK2)
    | sK0 = k1_tarski(sK1)
    | k1_xboole_0 = sK0
    | sK0 = k2_tarski(sK1,sK2)
    | ~ spl3_1 ),
    inference(resolution,[],[f17,f28])).

fof(f28,plain,
    ( r1_tarski(sK0,k2_tarski(sK1,sK2))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f27])).

fof(f27,plain,
    ( spl3_1
  <=> r1_tarski(sK0,k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | k2_tarski(X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f89,plain,
    ( ~ spl3_2
    | spl3_6 ),
    inference(avatar_contradiction_clause,[],[f88])).

fof(f88,plain,
    ( $false
    | ~ spl3_2
    | spl3_6 ),
    inference(subsumption_resolution,[],[f84,f55])).

fof(f55,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl3_6
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f84,plain,
    ( r1_tarski(sK0,sK0)
    | ~ spl3_2 ),
    inference(superposition,[],[f22,f32])).

fof(f32,plain,
    ( sK0 = k2_tarski(sK1,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f31])).

fof(f22,plain,(
    ! [X2,X1] : r1_tarski(k2_tarski(X1,X2),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k2_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f81,plain,
    ( spl3_1
    | ~ spl3_5 ),
    inference(avatar_contradiction_clause,[],[f80])).

fof(f80,plain,
    ( $false
    | spl3_1
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f75,f25])).

fof(f25,plain,(
    ! [X2,X1] : r1_tarski(k1_xboole_0,k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f18])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f75,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_tarski(sK1,sK2))
    | spl3_1
    | ~ spl3_5 ),
    inference(backward_demodulation,[],[f29,f47])).

fof(f47,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f46])).

fof(f29,plain,
    ( ~ r1_tarski(sK0,k2_tarski(sK1,sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f27])).

fof(f74,plain,
    ( spl3_1
    | ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f71])).

fof(f71,plain,
    ( $false
    | spl3_1
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f29,f70])).

fof(f70,plain,
    ( ! [X1] : r1_tarski(sK0,k2_tarski(X1,sK2))
    | ~ spl3_3 ),
    inference(superposition,[],[f23,f37])).

fof(f37,plain,
    ( sK0 = k1_tarski(sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f36])).

fof(f23,plain,(
    ! [X2,X1] : r1_tarski(k1_tarski(X2),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X2) != X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f68,plain,
    ( spl3_1
    | ~ spl3_4 ),
    inference(avatar_contradiction_clause,[],[f65])).

fof(f65,plain,
    ( $false
    | spl3_1
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f29,f64])).

fof(f64,plain,
    ( ! [X0] : r1_tarski(sK0,k2_tarski(sK1,X0))
    | ~ spl3_4 ),
    inference(superposition,[],[f24,f42])).

fof(f42,plain,
    ( sK0 = k1_tarski(sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f41])).

fof(f24,plain,(
    ! [X2,X1] : r1_tarski(k1_tarski(X1),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f56,plain,
    ( ~ spl3_6
    | spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f51,f31,f27,f53])).

fof(f51,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl3_1
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f29,f32])).

fof(f50,plain,
    ( spl3_1
    | spl3_5
    | spl3_4
    | spl3_3
    | spl3_2 ),
    inference(avatar_split_clause,[],[f12,f31,f36,f41,f46,f27])).

fof(f12,plain,
    ( sK0 = k2_tarski(sK1,sK2)
    | sK0 = k1_tarski(sK2)
    | sK0 = k1_tarski(sK1)
    | k1_xboole_0 = sK0
    | r1_tarski(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( ( ( sK0 != k2_tarski(sK1,sK2)
        & sK0 != k1_tarski(sK2)
        & sK0 != k1_tarski(sK1)
        & k1_xboole_0 != sK0 )
      | ~ r1_tarski(sK0,k2_tarski(sK1,sK2)) )
    & ( sK0 = k2_tarski(sK1,sK2)
      | sK0 = k1_tarski(sK2)
      | sK0 = k1_tarski(sK1)
      | k1_xboole_0 = sK0
      | r1_tarski(sK0,k2_tarski(sK1,sK2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2] :
        ( ( ( k2_tarski(X1,X2) != X0
            & k1_tarski(X2) != X0
            & k1_tarski(X1) != X0
            & k1_xboole_0 != X0 )
          | ~ r1_tarski(X0,k2_tarski(X1,X2)) )
        & ( k2_tarski(X1,X2) = X0
          | k1_tarski(X2) = X0
          | k1_tarski(X1) = X0
          | k1_xboole_0 = X0
          | r1_tarski(X0,k2_tarski(X1,X2)) ) )
   => ( ( ( sK0 != k2_tarski(sK1,sK2)
          & sK0 != k1_tarski(sK2)
          & sK0 != k1_tarski(sK1)
          & k1_xboole_0 != sK0 )
        | ~ r1_tarski(sK0,k2_tarski(sK1,sK2)) )
      & ( sK0 = k2_tarski(sK1,sK2)
        | sK0 = k1_tarski(sK2)
        | sK0 = k1_tarski(sK1)
        | k1_xboole_0 = sK0
        | r1_tarski(sK0,k2_tarski(sK1,sK2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ( ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 )
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ( ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 )
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,plain,(
    ? [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <~> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k2_tarski(X1,X2))
      <=> ~ ( k2_tarski(X1,X2) != X0
            & k1_tarski(X2) != X0
            & k1_tarski(X1) != X0
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_zfmisc_1)).

fof(f49,plain,
    ( ~ spl3_1
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f13,f46,f27])).

fof(f13,plain,
    ( k1_xboole_0 != sK0
    | ~ r1_tarski(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f44,plain,
    ( ~ spl3_1
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f14,f41,f27])).

fof(f14,plain,
    ( sK0 != k1_tarski(sK1)
    | ~ r1_tarski(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f39,plain,
    ( ~ spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f15,f36,f27])).

fof(f15,plain,
    ( sK0 != k1_tarski(sK2)
    | ~ r1_tarski(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f34,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f16,f31,f27])).

fof(f16,plain,
    ( sK0 != k2_tarski(sK1,sK2)
    | ~ r1_tarski(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:32:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (5872)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.48  % (5880)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.48  % (5880)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % (5878)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f117,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f34,f39,f44,f49,f50,f56,f68,f74,f81,f89,f116])).
% 0.22/0.48  fof(f116,plain,(
% 0.22/0.48    ~spl3_1 | spl3_2 | spl3_3 | spl3_4 | spl3_5),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f115])).
% 0.22/0.48  fof(f115,plain,(
% 0.22/0.48    $false | (~spl3_1 | spl3_2 | spl3_3 | spl3_4 | spl3_5)),
% 0.22/0.48    inference(subsumption_resolution,[],[f114,f33])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    sK0 != k2_tarski(sK1,sK2) | spl3_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f31])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    spl3_2 <=> sK0 = k2_tarski(sK1,sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.48  fof(f114,plain,(
% 0.22/0.48    sK0 = k2_tarski(sK1,sK2) | (~spl3_1 | spl3_3 | spl3_4 | spl3_5)),
% 0.22/0.48    inference(subsumption_resolution,[],[f113,f48])).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    k1_xboole_0 != sK0 | spl3_5),
% 0.22/0.48    inference(avatar_component_clause,[],[f46])).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    spl3_5 <=> k1_xboole_0 = sK0),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.48  fof(f113,plain,(
% 0.22/0.48    k1_xboole_0 = sK0 | sK0 = k2_tarski(sK1,sK2) | (~spl3_1 | spl3_3 | spl3_4)),
% 0.22/0.48    inference(subsumption_resolution,[],[f112,f43])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    sK0 != k1_tarski(sK1) | spl3_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f41])).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    spl3_4 <=> sK0 = k1_tarski(sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.48  fof(f112,plain,(
% 0.22/0.48    sK0 = k1_tarski(sK1) | k1_xboole_0 = sK0 | sK0 = k2_tarski(sK1,sK2) | (~spl3_1 | spl3_3)),
% 0.22/0.48    inference(subsumption_resolution,[],[f100,f38])).
% 0.22/0.49  % (5869)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    sK0 != k1_tarski(sK2) | spl3_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f36])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    spl3_3 <=> sK0 = k1_tarski(sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.49  fof(f100,plain,(
% 0.22/0.49    sK0 = k1_tarski(sK2) | sK0 = k1_tarski(sK1) | k1_xboole_0 = sK0 | sK0 = k2_tarski(sK1,sK2) | ~spl3_1),
% 0.22/0.49    inference(resolution,[],[f17,f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    r1_tarski(sK0,k2_tarski(sK1,sK2)) | ~spl3_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    spl3_1 <=> r1_tarski(sK0,k2_tarski(sK1,sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | k2_tarski(X1,X2) = X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 0.22/0.49    inference(flattening,[],[f10])).
% 0.22/0.49  fof(f10,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 0.22/0.49    inference(nnf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).
% 0.22/0.49  fof(f89,plain,(
% 0.22/0.49    ~spl3_2 | spl3_6),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f88])).
% 0.22/0.49  fof(f88,plain,(
% 0.22/0.49    $false | (~spl3_2 | spl3_6)),
% 0.22/0.49    inference(subsumption_resolution,[],[f84,f55])).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    ~r1_tarski(sK0,sK0) | spl3_6),
% 0.22/0.49    inference(avatar_component_clause,[],[f53])).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    spl3_6 <=> r1_tarski(sK0,sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.49  fof(f84,plain,(
% 0.22/0.49    r1_tarski(sK0,sK0) | ~spl3_2),
% 0.22/0.49    inference(superposition,[],[f22,f32])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    sK0 = k2_tarski(sK1,sK2) | ~spl3_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f31])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ( ! [X2,X1] : (r1_tarski(k2_tarski(X1,X2),k2_tarski(X1,X2))) )),
% 0.22/0.49    inference(equality_resolution,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k2_tarski(X1,X2) != X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f11])).
% 0.22/0.49  fof(f81,plain,(
% 0.22/0.49    spl3_1 | ~spl3_5),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f80])).
% 0.22/0.49  fof(f80,plain,(
% 0.22/0.49    $false | (spl3_1 | ~spl3_5)),
% 0.22/0.49    inference(subsumption_resolution,[],[f75,f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ( ! [X2,X1] : (r1_tarski(k1_xboole_0,k2_tarski(X1,X2))) )),
% 0.22/0.49    inference(equality_resolution,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_xboole_0 != X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f11])).
% 0.22/0.49  fof(f75,plain,(
% 0.22/0.49    ~r1_tarski(k1_xboole_0,k2_tarski(sK1,sK2)) | (spl3_1 | ~spl3_5)),
% 0.22/0.49    inference(backward_demodulation,[],[f29,f47])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    k1_xboole_0 = sK0 | ~spl3_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f46])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ~r1_tarski(sK0,k2_tarski(sK1,sK2)) | spl3_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f27])).
% 0.22/0.49  fof(f74,plain,(
% 0.22/0.49    spl3_1 | ~spl3_3),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f71])).
% 0.22/0.49  fof(f71,plain,(
% 0.22/0.49    $false | (spl3_1 | ~spl3_3)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f29,f70])).
% 0.22/0.49  fof(f70,plain,(
% 0.22/0.49    ( ! [X1] : (r1_tarski(sK0,k2_tarski(X1,sK2))) ) | ~spl3_3),
% 0.22/0.49    inference(superposition,[],[f23,f37])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    sK0 = k1_tarski(sK2) | ~spl3_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f36])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ( ! [X2,X1] : (r1_tarski(k1_tarski(X2),k2_tarski(X1,X2))) )),
% 0.22/0.49    inference(equality_resolution,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X2) != X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f11])).
% 0.22/0.49  fof(f68,plain,(
% 0.22/0.49    spl3_1 | ~spl3_4),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f65])).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    $false | (spl3_1 | ~spl3_4)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f29,f64])).
% 0.22/0.49  fof(f64,plain,(
% 0.22/0.49    ( ! [X0] : (r1_tarski(sK0,k2_tarski(sK1,X0))) ) | ~spl3_4),
% 0.22/0.49    inference(superposition,[],[f24,f42])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    sK0 = k1_tarski(sK1) | ~spl3_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f41])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ( ! [X2,X1] : (r1_tarski(k1_tarski(X1),k2_tarski(X1,X2))) )),
% 0.22/0.49    inference(equality_resolution,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X1) != X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f11])).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    ~spl3_6 | spl3_1 | ~spl3_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f51,f31,f27,f53])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    ~r1_tarski(sK0,sK0) | (spl3_1 | ~spl3_2)),
% 0.22/0.49    inference(forward_demodulation,[],[f29,f32])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    spl3_1 | spl3_5 | spl3_4 | spl3_3 | spl3_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f12,f31,f36,f41,f46,f27])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    sK0 = k2_tarski(sK1,sK2) | sK0 = k1_tarski(sK2) | sK0 = k1_tarski(sK1) | k1_xboole_0 = sK0 | r1_tarski(sK0,k2_tarski(sK1,sK2))),
% 0.22/0.49    inference(cnf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,plain,(
% 0.22/0.49    ((sK0 != k2_tarski(sK1,sK2) & sK0 != k1_tarski(sK2) & sK0 != k1_tarski(sK1) & k1_xboole_0 != sK0) | ~r1_tarski(sK0,k2_tarski(sK1,sK2))) & (sK0 = k2_tarski(sK1,sK2) | sK0 = k1_tarski(sK2) | sK0 = k1_tarski(sK1) | k1_xboole_0 = sK0 | r1_tarski(sK0,k2_tarski(sK1,sK2)))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f8])).
% 0.22/0.49  fof(f8,plain,(
% 0.22/0.49    ? [X0,X1,X2] : (((k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0) | ~r1_tarski(X0,k2_tarski(X1,X2))) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | r1_tarski(X0,k2_tarski(X1,X2)))) => (((sK0 != k2_tarski(sK1,sK2) & sK0 != k1_tarski(sK2) & sK0 != k1_tarski(sK1) & k1_xboole_0 != sK0) | ~r1_tarski(sK0,k2_tarski(sK1,sK2))) & (sK0 = k2_tarski(sK1,sK2) | sK0 = k1_tarski(sK2) | sK0 = k1_tarski(sK1) | k1_xboole_0 = sK0 | r1_tarski(sK0,k2_tarski(sK1,sK2))))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f7,plain,(
% 0.22/0.49    ? [X0,X1,X2] : (((k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0) | ~r1_tarski(X0,k2_tarski(X1,X2))) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | r1_tarski(X0,k2_tarski(X1,X2))))),
% 0.22/0.49    inference(flattening,[],[f6])).
% 0.22/0.49  fof(f6,plain,(
% 0.22/0.49    ? [X0,X1,X2] : (((k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0) | ~r1_tarski(X0,k2_tarski(X1,X2))) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | r1_tarski(X0,k2_tarski(X1,X2))))),
% 0.22/0.49    inference(nnf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,plain,(
% 0.22/0.49    ? [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <~> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 0.22/0.49    inference(negated_conjecture,[],[f2])).
% 0.22/0.49  fof(f2,conjecture,(
% 0.22/0.49    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_zfmisc_1)).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    ~spl3_1 | ~spl3_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f13,f46,f27])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    k1_xboole_0 != sK0 | ~r1_tarski(sK0,k2_tarski(sK1,sK2))),
% 0.22/0.49    inference(cnf_transformation,[],[f9])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    ~spl3_1 | ~spl3_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f14,f41,f27])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    sK0 != k1_tarski(sK1) | ~r1_tarski(sK0,k2_tarski(sK1,sK2))),
% 0.22/0.49    inference(cnf_transformation,[],[f9])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ~spl3_1 | ~spl3_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f15,f36,f27])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    sK0 != k1_tarski(sK2) | ~r1_tarski(sK0,k2_tarski(sK1,sK2))),
% 0.22/0.49    inference(cnf_transformation,[],[f9])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ~spl3_1 | ~spl3_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f16,f31,f27])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    sK0 != k2_tarski(sK1,sK2) | ~r1_tarski(sK0,k2_tarski(sK1,sK2))),
% 0.22/0.49    inference(cnf_transformation,[],[f9])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (5880)------------------------------
% 0.22/0.49  % (5880)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (5880)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (5880)Memory used [KB]: 10618
% 0.22/0.49  % (5880)Time elapsed: 0.066 s
% 0.22/0.49  % (5880)------------------------------
% 0.22/0.49  % (5880)------------------------------
% 0.22/0.50  % (5863)Success in time 0.132 s
%------------------------------------------------------------------------------
