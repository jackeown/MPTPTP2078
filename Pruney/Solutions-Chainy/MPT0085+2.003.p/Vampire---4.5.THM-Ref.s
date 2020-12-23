%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:21 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   62 (  83 expanded)
%              Number of leaves         :   19 (  37 expanded)
%              Depth                    :    6
%              Number of atoms          :  136 ( 184 expanded)
%              Number of equality atoms :   35 (  51 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f173,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f43,f47,f64,f68,f72,f92,f106,f120,f124,f172])).

fof(f172,plain,
    ( spl5_2
    | ~ spl5_14
    | ~ spl5_15
    | ~ spl5_16 ),
    inference(avatar_contradiction_clause,[],[f171])).

fof(f171,plain,
    ( $false
    | spl5_2
    | ~ spl5_14
    | ~ spl5_15
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f42,f170])).

fof(f170,plain,
    ( ! [X2] : k3_xboole_0(sK0,k2_xboole_0(sK1,X2)) = k3_xboole_0(sK0,X2)
    | ~ spl5_14
    | ~ spl5_15
    | ~ spl5_16 ),
    inference(forward_demodulation,[],[f166,f123])).

fof(f123,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl5_16
  <=> ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f166,plain,
    ( ! [X2] : k3_xboole_0(sK0,k2_xboole_0(sK1,X2)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X2))
    | ~ spl5_14
    | ~ spl5_15 ),
    inference(superposition,[],[f105,f119])).

fof(f119,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl5_15
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f105,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl5_14
  <=> ! [X1,X0,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f42,plain,
    ( k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,sK2)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl5_2
  <=> k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f124,plain,
    ( spl5_16
    | ~ spl5_3
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f73,f66,f45,f122])).

fof(f45,plain,
    ( spl5_3
  <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f66,plain,
    ( spl5_8
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f73,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl5_3
    | ~ spl5_8 ),
    inference(superposition,[],[f67,f46])).

fof(f46,plain,
    ( ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f45])).

fof(f67,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f66])).

fof(f120,plain,
    ( spl5_15
    | ~ spl5_7
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f112,f90,f62,f117])).

fof(f62,plain,
    ( spl5_7
  <=> ! [X0] :
        ( r2_hidden(sK3(X0),X0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f90,plain,
    ( spl5_12
  <=> ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f112,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl5_7
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f91,f63])).

fof(f63,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(X0),X0)
        | k1_xboole_0 = X0 )
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f62])).

fof(f91,plain,
    ( ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK0,sK1))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f90])).

fof(f106,plain,(
    spl5_14 ),
    inference(avatar_split_clause,[],[f33,f104])).

fof(f33,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f92,plain,
    ( spl5_12
    | ~ spl5_1
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f87,f70,f35,f90])).

fof(f35,plain,
    ( spl5_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f70,plain,
    ( spl5_9
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f87,plain,
    ( ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK0,sK1))
    | ~ spl5_1
    | ~ spl5_9 ),
    inference(unit_resulting_resolution,[],[f37,f71])).

fof(f71,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f70])).

fof(f37,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f72,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f32,f70])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f15,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f68,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f28,f66])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f64,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f25,f62])).

fof(f25,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f18])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f47,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f24,f45])).

fof(f24,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f43,plain,(
    ~ spl5_2 ),
    inference(avatar_split_clause,[],[f23,f40])).

fof(f23,plain,(
    k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,sK2)
    & r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2] :
        ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(X0,X2)
        & r1_xboole_0(X0,X1) )
   => ( k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,sK2)
      & r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(X0,X2)
      & r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
       => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).

fof(f38,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f22,f35])).

fof(f22,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:53:23 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.20/0.40  % (24366)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.46  % (24363)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.46  % (24365)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.46  % (24363)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f173,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f38,f43,f47,f64,f68,f72,f92,f106,f120,f124,f172])).
% 0.20/0.46  fof(f172,plain,(
% 0.20/0.46    spl5_2 | ~spl5_14 | ~spl5_15 | ~spl5_16),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f171])).
% 0.20/0.46  fof(f171,plain,(
% 0.20/0.46    $false | (spl5_2 | ~spl5_14 | ~spl5_15 | ~spl5_16)),
% 0.20/0.46    inference(subsumption_resolution,[],[f42,f170])).
% 0.20/0.46  fof(f170,plain,(
% 0.20/0.46    ( ! [X2] : (k3_xboole_0(sK0,k2_xboole_0(sK1,X2)) = k3_xboole_0(sK0,X2)) ) | (~spl5_14 | ~spl5_15 | ~spl5_16)),
% 0.20/0.46    inference(forward_demodulation,[],[f166,f123])).
% 0.20/0.46  fof(f123,plain,(
% 0.20/0.46    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) ) | ~spl5_16),
% 0.20/0.46    inference(avatar_component_clause,[],[f122])).
% 0.20/0.46  fof(f122,plain,(
% 0.20/0.46    spl5_16 <=> ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.20/0.46  fof(f166,plain,(
% 0.20/0.46    ( ! [X2] : (k3_xboole_0(sK0,k2_xboole_0(sK1,X2)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X2))) ) | (~spl5_14 | ~spl5_15)),
% 0.20/0.46    inference(superposition,[],[f105,f119])).
% 0.20/0.46  fof(f119,plain,(
% 0.20/0.46    k1_xboole_0 = k3_xboole_0(sK0,sK1) | ~spl5_15),
% 0.20/0.46    inference(avatar_component_clause,[],[f117])).
% 0.20/0.46  fof(f117,plain,(
% 0.20/0.46    spl5_15 <=> k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.20/0.46  fof(f105,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) ) | ~spl5_14),
% 0.20/0.46    inference(avatar_component_clause,[],[f104])).
% 0.20/0.46  fof(f104,plain,(
% 0.20/0.46    spl5_14 <=> ! [X1,X0,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.20/0.46  fof(f42,plain,(
% 0.20/0.46    k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,sK2) | spl5_2),
% 0.20/0.46    inference(avatar_component_clause,[],[f40])).
% 0.20/0.46  fof(f40,plain,(
% 0.20/0.46    spl5_2 <=> k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k3_xboole_0(sK0,sK2)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.46  fof(f124,plain,(
% 0.20/0.46    spl5_16 | ~spl5_3 | ~spl5_8),
% 0.20/0.46    inference(avatar_split_clause,[],[f73,f66,f45,f122])).
% 0.20/0.46  fof(f45,plain,(
% 0.20/0.46    spl5_3 <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.46  fof(f66,plain,(
% 0.20/0.46    spl5_8 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.20/0.46  fof(f73,plain,(
% 0.20/0.46    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) ) | (~spl5_3 | ~spl5_8)),
% 0.20/0.46    inference(superposition,[],[f67,f46])).
% 0.20/0.46  fof(f46,plain,(
% 0.20/0.46    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl5_3),
% 0.20/0.46    inference(avatar_component_clause,[],[f45])).
% 0.20/0.46  fof(f67,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl5_8),
% 0.20/0.46    inference(avatar_component_clause,[],[f66])).
% 0.20/0.46  fof(f120,plain,(
% 0.20/0.46    spl5_15 | ~spl5_7 | ~spl5_12),
% 0.20/0.46    inference(avatar_split_clause,[],[f112,f90,f62,f117])).
% 0.20/0.46  fof(f62,plain,(
% 0.20/0.46    spl5_7 <=> ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.20/0.46  fof(f90,plain,(
% 0.20/0.46    spl5_12 <=> ! [X0] : ~r2_hidden(X0,k3_xboole_0(sK0,sK1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.20/0.46  fof(f112,plain,(
% 0.20/0.46    k1_xboole_0 = k3_xboole_0(sK0,sK1) | (~spl5_7 | ~spl5_12)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f91,f63])).
% 0.20/0.46  fof(f63,plain,(
% 0.20/0.46    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) ) | ~spl5_7),
% 0.20/0.46    inference(avatar_component_clause,[],[f62])).
% 0.20/0.46  fof(f91,plain,(
% 0.20/0.46    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK0,sK1))) ) | ~spl5_12),
% 0.20/0.46    inference(avatar_component_clause,[],[f90])).
% 0.20/0.46  fof(f106,plain,(
% 0.20/0.46    spl5_14),
% 0.20/0.46    inference(avatar_split_clause,[],[f33,f104])).
% 0.20/0.46  fof(f33,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).
% 0.20/0.46  fof(f92,plain,(
% 0.20/0.46    spl5_12 | ~spl5_1 | ~spl5_9),
% 0.20/0.46    inference(avatar_split_clause,[],[f87,f70,f35,f90])).
% 0.20/0.46  fof(f35,plain,(
% 0.20/0.46    spl5_1 <=> r1_xboole_0(sK0,sK1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.46  fof(f70,plain,(
% 0.20/0.46    spl5_9 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.20/0.46  fof(f87,plain,(
% 0.20/0.46    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK0,sK1))) ) | (~spl5_1 | ~spl5_9)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f37,f71])).
% 0.20/0.46  fof(f71,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) ) | ~spl5_9),
% 0.20/0.46    inference(avatar_component_clause,[],[f70])).
% 0.20/0.46  fof(f37,plain,(
% 0.20/0.46    r1_xboole_0(sK0,sK1) | ~spl5_1),
% 0.20/0.46    inference(avatar_component_clause,[],[f35])).
% 0.20/0.46  fof(f72,plain,(
% 0.20/0.46    spl5_9),
% 0.20/0.46    inference(avatar_split_clause,[],[f32,f70])).
% 0.20/0.46  fof(f32,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f21])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f15,f20])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.46    inference(ennf_transformation,[],[f12])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.46    inference(rectify,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.20/0.46  fof(f68,plain,(
% 0.20/0.46    spl5_8),
% 0.20/0.46    inference(avatar_split_clause,[],[f28,f66])).
% 0.20/0.46  fof(f28,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.20/0.46  fof(f64,plain,(
% 0.20/0.46    spl5_7),
% 0.20/0.46    inference(avatar_split_clause,[],[f25,f62])).
% 0.20/0.46  fof(f25,plain,(
% 0.20/0.46    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.46    inference(cnf_transformation,[],[f19])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f18])).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.20/0.46    inference(ennf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.20/0.46  fof(f47,plain,(
% 0.20/0.46    spl5_3),
% 0.20/0.46    inference(avatar_split_clause,[],[f24,f45])).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.46    inference(cnf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.20/0.46  fof(f43,plain,(
% 0.20/0.46    ~spl5_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f23,f40])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,sK2)),
% 0.20/0.46    inference(cnf_transformation,[],[f17])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,sK2) & r1_xboole_0(sK0,sK1)),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f16])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ? [X0,X1,X2] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(X0,X2) & r1_xboole_0(X0,X1)) => (k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,sK2) & r1_xboole_0(sK0,sK1))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    ? [X0,X1,X2] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(X0,X2) & r1_xboole_0(X0,X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f11])).
% 0.20/0.46  fof(f11,negated_conjecture,(
% 0.20/0.46    ~! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2))),
% 0.20/0.46    inference(negated_conjecture,[],[f10])).
% 0.20/0.46  fof(f10,conjecture,(
% 0.20/0.46    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).
% 0.20/0.46  fof(f38,plain,(
% 0.20/0.46    spl5_1),
% 0.20/0.46    inference(avatar_split_clause,[],[f22,f35])).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    r1_xboole_0(sK0,sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f17])).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (24363)------------------------------
% 0.20/0.46  % (24363)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (24363)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (24363)Memory used [KB]: 6140
% 0.20/0.46  % (24363)Time elapsed: 0.030 s
% 0.20/0.46  % (24363)------------------------------
% 0.20/0.46  % (24363)------------------------------
% 0.20/0.47  % (24357)Success in time 0.118 s
%------------------------------------------------------------------------------
