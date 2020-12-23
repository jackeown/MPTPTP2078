%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:11 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 144 expanded)
%              Number of leaves         :   25 (  69 expanded)
%              Depth                    :    6
%              Number of atoms          :  214 ( 348 expanded)
%              Number of equality atoms :   32 (  62 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1802,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f42,f49,f61,f65,f69,f73,f77,f81,f104,f150,f243,f356,f393,f417,f435,f1139,f1665,f1791])).

fof(f1791,plain,
    ( ~ spl3_9
    | ~ spl3_31
    | spl3_62
    | ~ spl3_83 ),
    inference(avatar_contradiction_clause,[],[f1790])).

fof(f1790,plain,
    ( $false
    | ~ spl3_9
    | ~ spl3_31
    | spl3_62
    | ~ spl3_83 ),
    inference(subsumption_resolution,[],[f1143,f1774])).

fof(f1774,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,X0),sK1)
    | ~ spl3_31
    | ~ spl3_83 ),
    inference(unit_resulting_resolution,[],[f1664,f355])).

fof(f355,plain,
    ( ! [X4,X3] :
        ( k1_xboole_0 = k3_xboole_0(X4,X3)
        | ~ r1_xboole_0(X3,X4) )
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f354])).

fof(f354,plain,
    ( spl3_31
  <=> ! [X3,X4] :
        ( k1_xboole_0 = k3_xboole_0(X4,X3)
        | ~ r1_xboole_0(X3,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f1664,plain,
    ( ! [X0] : r1_xboole_0(sK1,k3_xboole_0(sK0,X0))
    | ~ spl3_83 ),
    inference(avatar_component_clause,[],[f1663])).

fof(f1663,plain,
    ( spl3_83
  <=> ! [X0] : r1_xboole_0(sK1,k3_xboole_0(sK0,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_83])])).

fof(f1143,plain,
    ( k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK0,sK2),sK1)
    | ~ spl3_9
    | spl3_62 ),
    inference(unit_resulting_resolution,[],[f1138,f72])).

fof(f72,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) != k1_xboole_0
        | r1_xboole_0(X0,X1) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl3_9
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f1138,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK0,sK2),sK1)
    | spl3_62 ),
    inference(avatar_component_clause,[],[f1136])).

fof(f1136,plain,
    ( spl3_62
  <=> r1_xboole_0(k3_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).

fof(f1665,plain,
    ( spl3_83
    | ~ spl3_33
    | ~ spl3_34 ),
    inference(avatar_split_clause,[],[f517,f432,f415,f1663])).

fof(f415,plain,
    ( spl3_33
  <=> ! [X7,X8,X6] :
        ( ~ r1_xboole_0(X8,X6)
        | r1_xboole_0(X8,k3_xboole_0(X6,X7)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f432,plain,
    ( spl3_34
  <=> r1_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f517,plain,
    ( ! [X0] : r1_xboole_0(sK1,k3_xboole_0(sK0,X0))
    | ~ spl3_33
    | ~ spl3_34 ),
    inference(unit_resulting_resolution,[],[f434,f416])).

fof(f416,plain,
    ( ! [X6,X8,X7] :
        ( r1_xboole_0(X8,k3_xboole_0(X6,X7))
        | ~ r1_xboole_0(X8,X6) )
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f415])).

fof(f434,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f432])).

fof(f1139,plain,
    ( ~ spl3_62
    | ~ spl3_15
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f250,f241,f102,f1136])).

fof(f102,plain,
    ( spl3_15
  <=> ! [X1,X0] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f241,plain,
    ( spl3_24
  <=> ! [X0] : ~ r1_xboole_0(k3_xboole_0(sK0,sK2),k2_xboole_0(k3_xboole_0(sK1,sK2),X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f250,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK0,sK2),sK1)
    | ~ spl3_15
    | ~ spl3_24 ),
    inference(superposition,[],[f242,f103])).

fof(f103,plain,
    ( ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f102])).

fof(f242,plain,
    ( ! [X0] : ~ r1_xboole_0(k3_xboole_0(sK0,sK2),k2_xboole_0(k3_xboole_0(sK1,sK2),X0))
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f241])).

fof(f435,plain,
    ( spl3_34
    | ~ spl3_16
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f401,f391,f147,f432])).

fof(f147,plain,
    ( spl3_16
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f391,plain,
    ( spl3_32
  <=> ! [X3,X4] :
        ( k1_xboole_0 != k3_xboole_0(X4,X3)
        | r1_xboole_0(X3,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f401,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl3_16
    | ~ spl3_32 ),
    inference(unit_resulting_resolution,[],[f149,f392])).

fof(f392,plain,
    ( ! [X4,X3] :
        ( k1_xboole_0 != k3_xboole_0(X4,X3)
        | r1_xboole_0(X3,X4) )
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f391])).

fof(f149,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f147])).

fof(f417,plain,
    ( spl3_33
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f128,f79,f63,f415])).

fof(f63,plain,
    ( spl3_7
  <=> ! [X1,X0] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f79,plain,
    ( spl3_11
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | r1_xboole_0(X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f128,plain,
    ( ! [X6,X8,X7] :
        ( ~ r1_xboole_0(X8,X6)
        | r1_xboole_0(X8,k3_xboole_0(X6,X7)) )
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(superposition,[],[f80,f64])).

fof(f64,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f63])).

fof(f80,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | r1_xboole_0(X0,X2) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f79])).

fof(f393,plain,
    ( spl3_32
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f117,f71,f59,f391])).

fof(f59,plain,
    ( spl3_6
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f117,plain,
    ( ! [X4,X3] :
        ( k1_xboole_0 != k3_xboole_0(X4,X3)
        | r1_xboole_0(X3,X4) )
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(superposition,[],[f72,f60])).

fof(f60,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f59])).

fof(f356,plain,
    ( spl3_31
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f106,f67,f59,f354])).

fof(f67,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f106,plain,
    ( ! [X4,X3] :
        ( k1_xboole_0 = k3_xboole_0(X4,X3)
        | ~ r1_xboole_0(X3,X4) )
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(superposition,[],[f68,f60])).

fof(f68,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f67])).

fof(f243,plain,
    ( spl3_24
    | spl3_3
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f121,f75,f46,f241])).

fof(f46,plain,
    ( spl3_3
  <=> r1_xboole_0(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f75,plain,
    ( spl3_10
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f121,plain,
    ( ! [X0] : ~ r1_xboole_0(k3_xboole_0(sK0,sK2),k2_xboole_0(k3_xboole_0(sK1,sK2),X0))
    | spl3_3
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f48,f76])).

fof(f76,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | r1_xboole_0(X0,X1) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f75])).

fof(f48,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK2))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f46])).

fof(f150,plain,
    ( spl3_16
    | ~ spl3_1
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f105,f67,f34,f147])).

fof(f34,plain,
    ( spl3_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f105,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_1
    | ~ spl3_8 ),
    inference(unit_resulting_resolution,[],[f36,f68])).

fof(f36,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f104,plain,(
    spl3_15 ),
    inference(avatar_split_clause,[],[f26,f102])).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f81,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f32,f79])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f77,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f31,f75])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f73,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f28,f71])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f69,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f27,f67])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f65,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f23,f63])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f61,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f22,f59])).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f49,plain,
    ( ~ spl3_3
    | spl3_2 ),
    inference(avatar_split_clause,[],[f44,f39,f46])).

fof(f39,plain,
    ( spl3_2
  <=> r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f44,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK2))
    | spl3_2 ),
    inference(forward_demodulation,[],[f43,f22])).

fof(f43,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK1,sK2))
    | spl3_2 ),
    inference(forward_demodulation,[],[f41,f22])).

fof(f41,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f42,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f19,f39])).

fof(f19,plain,(
    ~ r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1))
    & r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1))
        & r1_xboole_0(X0,X1) )
   => ( ~ r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1))
      & r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1))
      & r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
       => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_xboole_1)).

fof(f37,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f18,f34])).

fof(f18,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:35:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.42  % (28082)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.45  % (28082)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f1802,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f37,f42,f49,f61,f65,f69,f73,f77,f81,f104,f150,f243,f356,f393,f417,f435,f1139,f1665,f1791])).
% 0.21/0.45  fof(f1791,plain,(
% 0.21/0.45    ~spl3_9 | ~spl3_31 | spl3_62 | ~spl3_83),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f1790])).
% 0.21/0.45  fof(f1790,plain,(
% 0.21/0.45    $false | (~spl3_9 | ~spl3_31 | spl3_62 | ~spl3_83)),
% 0.21/0.45    inference(subsumption_resolution,[],[f1143,f1774])).
% 0.21/0.45  fof(f1774,plain,(
% 0.21/0.45    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,X0),sK1)) ) | (~spl3_31 | ~spl3_83)),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f1664,f355])).
% 0.21/0.45  fof(f355,plain,(
% 0.21/0.45    ( ! [X4,X3] : (k1_xboole_0 = k3_xboole_0(X4,X3) | ~r1_xboole_0(X3,X4)) ) | ~spl3_31),
% 0.21/0.45    inference(avatar_component_clause,[],[f354])).
% 0.21/0.45  fof(f354,plain,(
% 0.21/0.45    spl3_31 <=> ! [X3,X4] : (k1_xboole_0 = k3_xboole_0(X4,X3) | ~r1_xboole_0(X3,X4))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.21/0.45  fof(f1664,plain,(
% 0.21/0.45    ( ! [X0] : (r1_xboole_0(sK1,k3_xboole_0(sK0,X0))) ) | ~spl3_83),
% 0.21/0.45    inference(avatar_component_clause,[],[f1663])).
% 0.21/0.45  fof(f1663,plain,(
% 0.21/0.45    spl3_83 <=> ! [X0] : r1_xboole_0(sK1,k3_xboole_0(sK0,X0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_83])])).
% 0.21/0.45  fof(f1143,plain,(
% 0.21/0.45    k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK0,sK2),sK1) | (~spl3_9 | spl3_62)),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f1138,f72])).
% 0.21/0.45  fof(f72,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) ) | ~spl3_9),
% 0.21/0.45    inference(avatar_component_clause,[],[f71])).
% 0.21/0.45  fof(f71,plain,(
% 0.21/0.45    spl3_9 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.45  fof(f1138,plain,(
% 0.21/0.45    ~r1_xboole_0(k3_xboole_0(sK0,sK2),sK1) | spl3_62),
% 0.21/0.45    inference(avatar_component_clause,[],[f1136])).
% 0.21/0.45  fof(f1136,plain,(
% 0.21/0.45    spl3_62 <=> r1_xboole_0(k3_xboole_0(sK0,sK2),sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).
% 0.21/0.45  fof(f1665,plain,(
% 0.21/0.45    spl3_83 | ~spl3_33 | ~spl3_34),
% 0.21/0.45    inference(avatar_split_clause,[],[f517,f432,f415,f1663])).
% 0.21/0.45  fof(f415,plain,(
% 0.21/0.45    spl3_33 <=> ! [X7,X8,X6] : (~r1_xboole_0(X8,X6) | r1_xboole_0(X8,k3_xboole_0(X6,X7)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.21/0.45  fof(f432,plain,(
% 0.21/0.45    spl3_34 <=> r1_xboole_0(sK1,sK0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.21/0.45  fof(f517,plain,(
% 0.21/0.45    ( ! [X0] : (r1_xboole_0(sK1,k3_xboole_0(sK0,X0))) ) | (~spl3_33 | ~spl3_34)),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f434,f416])).
% 0.21/0.45  fof(f416,plain,(
% 0.21/0.45    ( ! [X6,X8,X7] : (r1_xboole_0(X8,k3_xboole_0(X6,X7)) | ~r1_xboole_0(X8,X6)) ) | ~spl3_33),
% 0.21/0.45    inference(avatar_component_clause,[],[f415])).
% 0.21/0.45  fof(f434,plain,(
% 0.21/0.45    r1_xboole_0(sK1,sK0) | ~spl3_34),
% 0.21/0.45    inference(avatar_component_clause,[],[f432])).
% 0.21/0.45  fof(f1139,plain,(
% 0.21/0.45    ~spl3_62 | ~spl3_15 | ~spl3_24),
% 0.21/0.45    inference(avatar_split_clause,[],[f250,f241,f102,f1136])).
% 0.21/0.45  fof(f102,plain,(
% 0.21/0.45    spl3_15 <=> ! [X1,X0] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.45  fof(f241,plain,(
% 0.21/0.45    spl3_24 <=> ! [X0] : ~r1_xboole_0(k3_xboole_0(sK0,sK2),k2_xboole_0(k3_xboole_0(sK1,sK2),X0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.21/0.45  fof(f250,plain,(
% 0.21/0.45    ~r1_xboole_0(k3_xboole_0(sK0,sK2),sK1) | (~spl3_15 | ~spl3_24)),
% 0.21/0.45    inference(superposition,[],[f242,f103])).
% 0.21/0.45  fof(f103,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) ) | ~spl3_15),
% 0.21/0.45    inference(avatar_component_clause,[],[f102])).
% 0.21/0.45  fof(f242,plain,(
% 0.21/0.45    ( ! [X0] : (~r1_xboole_0(k3_xboole_0(sK0,sK2),k2_xboole_0(k3_xboole_0(sK1,sK2),X0))) ) | ~spl3_24),
% 0.21/0.45    inference(avatar_component_clause,[],[f241])).
% 0.21/0.45  fof(f435,plain,(
% 0.21/0.45    spl3_34 | ~spl3_16 | ~spl3_32),
% 0.21/0.45    inference(avatar_split_clause,[],[f401,f391,f147,f432])).
% 0.21/0.45  fof(f147,plain,(
% 0.21/0.45    spl3_16 <=> k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.45  fof(f391,plain,(
% 0.21/0.45    spl3_32 <=> ! [X3,X4] : (k1_xboole_0 != k3_xboole_0(X4,X3) | r1_xboole_0(X3,X4))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.21/0.45  fof(f401,plain,(
% 0.21/0.45    r1_xboole_0(sK1,sK0) | (~spl3_16 | ~spl3_32)),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f149,f392])).
% 0.21/0.45  fof(f392,plain,(
% 0.21/0.45    ( ! [X4,X3] : (k1_xboole_0 != k3_xboole_0(X4,X3) | r1_xboole_0(X3,X4)) ) | ~spl3_32),
% 0.21/0.45    inference(avatar_component_clause,[],[f391])).
% 0.21/0.45  fof(f149,plain,(
% 0.21/0.45    k1_xboole_0 = k3_xboole_0(sK0,sK1) | ~spl3_16),
% 0.21/0.45    inference(avatar_component_clause,[],[f147])).
% 0.21/0.45  fof(f417,plain,(
% 0.21/0.45    spl3_33 | ~spl3_7 | ~spl3_11),
% 0.21/0.45    inference(avatar_split_clause,[],[f128,f79,f63,f415])).
% 0.21/0.45  fof(f63,plain,(
% 0.21/0.45    spl3_7 <=> ! [X1,X0] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.45  fof(f79,plain,(
% 0.21/0.45    spl3_11 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X2))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.45  fof(f128,plain,(
% 0.21/0.45    ( ! [X6,X8,X7] : (~r1_xboole_0(X8,X6) | r1_xboole_0(X8,k3_xboole_0(X6,X7))) ) | (~spl3_7 | ~spl3_11)),
% 0.21/0.45    inference(superposition,[],[f80,f64])).
% 0.21/0.45  fof(f64,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) ) | ~spl3_7),
% 0.21/0.45    inference(avatar_component_clause,[],[f63])).
% 0.21/0.45  fof(f80,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) ) | ~spl3_11),
% 0.21/0.45    inference(avatar_component_clause,[],[f79])).
% 0.21/0.45  fof(f393,plain,(
% 0.21/0.45    spl3_32 | ~spl3_6 | ~spl3_9),
% 0.21/0.45    inference(avatar_split_clause,[],[f117,f71,f59,f391])).
% 0.21/0.45  fof(f59,plain,(
% 0.21/0.45    spl3_6 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.45  fof(f117,plain,(
% 0.21/0.45    ( ! [X4,X3] : (k1_xboole_0 != k3_xboole_0(X4,X3) | r1_xboole_0(X3,X4)) ) | (~spl3_6 | ~spl3_9)),
% 0.21/0.45    inference(superposition,[],[f72,f60])).
% 0.21/0.45  fof(f60,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl3_6),
% 0.21/0.45    inference(avatar_component_clause,[],[f59])).
% 0.21/0.45  fof(f356,plain,(
% 0.21/0.45    spl3_31 | ~spl3_6 | ~spl3_8),
% 0.21/0.45    inference(avatar_split_clause,[],[f106,f67,f59,f354])).
% 0.21/0.45  fof(f67,plain,(
% 0.21/0.45    spl3_8 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.45  fof(f106,plain,(
% 0.21/0.45    ( ! [X4,X3] : (k1_xboole_0 = k3_xboole_0(X4,X3) | ~r1_xboole_0(X3,X4)) ) | (~spl3_6 | ~spl3_8)),
% 0.21/0.45    inference(superposition,[],[f68,f60])).
% 0.21/0.45  fof(f68,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) ) | ~spl3_8),
% 0.21/0.45    inference(avatar_component_clause,[],[f67])).
% 0.21/0.45  fof(f243,plain,(
% 0.21/0.45    spl3_24 | spl3_3 | ~spl3_10),
% 0.21/0.45    inference(avatar_split_clause,[],[f121,f75,f46,f241])).
% 0.21/0.45  fof(f46,plain,(
% 0.21/0.45    spl3_3 <=> r1_xboole_0(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK2))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.45  fof(f75,plain,(
% 0.21/0.45    spl3_10 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.45  fof(f121,plain,(
% 0.21/0.45    ( ! [X0] : (~r1_xboole_0(k3_xboole_0(sK0,sK2),k2_xboole_0(k3_xboole_0(sK1,sK2),X0))) ) | (spl3_3 | ~spl3_10)),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f48,f76])).
% 0.21/0.45  fof(f76,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X1)) ) | ~spl3_10),
% 0.21/0.45    inference(avatar_component_clause,[],[f75])).
% 0.21/0.45  fof(f48,plain,(
% 0.21/0.45    ~r1_xboole_0(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK2)) | spl3_3),
% 0.21/0.45    inference(avatar_component_clause,[],[f46])).
% 0.21/0.45  fof(f150,plain,(
% 0.21/0.45    spl3_16 | ~spl3_1 | ~spl3_8),
% 0.21/0.45    inference(avatar_split_clause,[],[f105,f67,f34,f147])).
% 0.21/0.45  fof(f34,plain,(
% 0.21/0.45    spl3_1 <=> r1_xboole_0(sK0,sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.45  fof(f105,plain,(
% 0.21/0.45    k1_xboole_0 = k3_xboole_0(sK0,sK1) | (~spl3_1 | ~spl3_8)),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f36,f68])).
% 0.21/0.45  fof(f36,plain,(
% 0.21/0.45    r1_xboole_0(sK0,sK1) | ~spl3_1),
% 0.21/0.45    inference(avatar_component_clause,[],[f34])).
% 0.21/0.45  fof(f104,plain,(
% 0.21/0.45    spl3_15),
% 0.21/0.45    inference(avatar_split_clause,[],[f26,f102])).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f8])).
% 0.21/0.45  fof(f8,axiom,(
% 0.21/0.45    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.21/0.45  fof(f81,plain,(
% 0.21/0.45    spl3_11),
% 0.21/0.45    inference(avatar_split_clause,[],[f32,f79])).
% 0.21/0.45  fof(f32,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f14])).
% 0.21/0.45  fof(f14,plain,(
% 0.21/0.45    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.21/0.45    inference(ennf_transformation,[],[f10])).
% 0.21/0.45  fof(f10,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
% 0.21/0.45  fof(f77,plain,(
% 0.21/0.45    spl3_10),
% 0.21/0.45    inference(avatar_split_clause,[],[f31,f75])).
% 0.21/0.45  fof(f31,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f14])).
% 0.21/0.45  fof(f73,plain,(
% 0.21/0.45    spl3_9),
% 0.21/0.45    inference(avatar_split_clause,[],[f28,f71])).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f17])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.45    inference(nnf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.45  fof(f69,plain,(
% 0.21/0.45    spl3_8),
% 0.21/0.45    inference(avatar_split_clause,[],[f27,f67])).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f17])).
% 0.21/0.45  fof(f65,plain,(
% 0.21/0.45    spl3_7),
% 0.21/0.45    inference(avatar_split_clause,[],[f23,f63])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.21/0.45  fof(f61,plain,(
% 0.21/0.45    spl3_6),
% 0.21/0.45    inference(avatar_split_clause,[],[f22,f59])).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.45  fof(f49,plain,(
% 0.21/0.45    ~spl3_3 | spl3_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f44,f39,f46])).
% 0.21/0.45  fof(f39,plain,(
% 0.21/0.45    spl3_2 <=> r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.45  fof(f44,plain,(
% 0.21/0.45    ~r1_xboole_0(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK2)) | spl3_2),
% 0.21/0.45    inference(forward_demodulation,[],[f43,f22])).
% 0.21/0.45  fof(f43,plain,(
% 0.21/0.45    ~r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK1,sK2)) | spl3_2),
% 0.21/0.45    inference(forward_demodulation,[],[f41,f22])).
% 0.21/0.45  fof(f41,plain,(
% 0.21/0.45    ~r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1)) | spl3_2),
% 0.21/0.45    inference(avatar_component_clause,[],[f39])).
% 0.21/0.45  fof(f42,plain,(
% 0.21/0.45    ~spl3_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f19,f39])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    ~r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1))),
% 0.21/0.45    inference(cnf_transformation,[],[f16])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    ~r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1)) & r1_xboole_0(sK0,sK1)),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f15])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    ? [X0,X1,X2] : (~r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) & r1_xboole_0(X0,X1)) => (~r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1)) & r1_xboole_0(sK0,sK1))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f13,plain,(
% 0.21/0.45    ? [X0,X1,X2] : (~r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) & r1_xboole_0(X0,X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f12])).
% 0.21/0.45  fof(f12,negated_conjecture,(
% 0.21/0.45    ~! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)))),
% 0.21/0.45    inference(negated_conjecture,[],[f11])).
% 0.21/0.45  fof(f11,conjecture,(
% 0.21/0.45    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_xboole_1)).
% 0.21/0.45  fof(f37,plain,(
% 0.21/0.45    spl3_1),
% 0.21/0.45    inference(avatar_split_clause,[],[f18,f34])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    r1_xboole_0(sK0,sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f16])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (28082)------------------------------
% 0.21/0.45  % (28082)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (28082)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (28082)Memory used [KB]: 7291
% 0.21/0.45  % (28082)Time elapsed: 0.028 s
% 0.21/0.45  % (28082)------------------------------
% 0.21/0.45  % (28082)------------------------------
% 0.21/0.45  % (28069)Success in time 0.096 s
%------------------------------------------------------------------------------
