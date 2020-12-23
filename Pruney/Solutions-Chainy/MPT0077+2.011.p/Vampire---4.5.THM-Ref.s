%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:45 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 314 expanded)
%              Number of leaves         :   39 ( 144 expanded)
%              Depth                    :   10
%              Number of atoms          :  469 ( 835 expanded)
%              Number of equality atoms :  110 ( 230 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1028,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f65,f69,f73,f77,f81,f89,f93,f101,f105,f138,f142,f168,f180,f234,f242,f261,f358,f395,f437,f493,f588,f603,f622,f629,f636,f656,f711,f723,f822,f924,f998,f1027])).

fof(f1027,plain,
    ( ~ spl4_8
    | ~ spl4_9
    | ~ spl4_24
    | ~ spl4_25
    | spl4_31
    | ~ spl4_33
    | ~ spl4_35
    | ~ spl4_36
    | ~ spl4_45 ),
    inference(avatar_contradiction_clause,[],[f1026])).

fof(f1026,plain,
    ( $false
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_24
    | ~ spl4_25
    | spl4_31
    | ~ spl4_33
    | ~ spl4_35
    | ~ spl4_36
    | ~ spl4_45 ),
    inference(subsumption_resolution,[],[f1009,f356])).

fof(f356,plain,
    ( sK0 != k4_xboole_0(sK0,sK1)
    | spl4_31 ),
    inference(avatar_component_clause,[],[f355])).

fof(f355,plain,
    ( spl4_31
  <=> sK0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f1009,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_24
    | ~ spl4_25
    | ~ spl4_33
    | ~ spl4_35
    | ~ spl4_36
    | ~ spl4_45 ),
    inference(forward_demodulation,[],[f1008,f233])).

fof(f233,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f232])).

fof(f232,plain,
    ( spl4_24
  <=> ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f1008,plain,
    ( k4_xboole_0(sK0,sK1) = k2_xboole_0(k1_xboole_0,sK0)
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_25
    | ~ spl4_33
    | ~ spl4_35
    | ~ spl4_36
    | ~ spl4_45 ),
    inference(forward_demodulation,[],[f591,f975])).

fof(f975,plain,
    ( k1_xboole_0 = k3_xboole_0(k4_xboole_0(sK0,sK1),sK2)
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_25
    | ~ spl4_35
    | ~ spl4_36
    | ~ spl4_45 ),
    inference(forward_demodulation,[],[f589,f855])).

fof(f855,plain,
    ( ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X3,X2))
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_25
    | ~ spl4_45 ),
    inference(forward_demodulation,[],[f825,f854])).

fof(f854,plain,
    ( ! [X1] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1)
    | ~ spl4_8
    | ~ spl4_25
    | ~ spl4_45 ),
    inference(forward_demodulation,[],[f824,f241])).

fof(f241,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f240])).

fof(f240,plain,
    ( spl4_25
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f824,plain,
    ( ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k4_xboole_0(X1,X1)
    | ~ spl4_8
    | ~ spl4_45 ),
    inference(superposition,[],[f821,f76])).

fof(f76,plain,
    ( ! [X0] : k2_xboole_0(X0,X0) = X0
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl4_8
  <=> ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f821,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1)
    | ~ spl4_45 ),
    inference(avatar_component_clause,[],[f820])).

fof(f820,plain,
    ( spl4_45
  <=> ! [X1,X0] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f825,plain,
    ( ! [X2,X3] : k4_xboole_0(k1_xboole_0,X3) = k4_xboole_0(X2,k2_xboole_0(X3,X2))
    | ~ spl4_9
    | ~ spl4_45 ),
    inference(superposition,[],[f821,f80])).

fof(f80,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl4_9
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f589,plain,
    ( k3_xboole_0(k4_xboole_0(sK0,sK1),sK2) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK0))
    | ~ spl4_35
    | ~ spl4_36 ),
    inference(superposition,[],[f492,f587])).

fof(f587,plain,
    ( sK0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f585])).

fof(f585,plain,
    ( spl4_36
  <=> sK0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f492,plain,
    ( ! [X6,X7,X5] : k3_xboole_0(k4_xboole_0(X5,X6),X7) = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,k2_xboole_0(X6,X7))))
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f491])).

fof(f491,plain,
    ( spl4_35
  <=> ! [X5,X7,X6] : k3_xboole_0(k4_xboole_0(X5,X6),X7) = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,k2_xboole_0(X6,X7)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f591,plain,
    ( k4_xboole_0(sK0,sK1) = k2_xboole_0(k3_xboole_0(k4_xboole_0(sK0,sK1),sK2),sK0)
    | ~ spl4_33
    | ~ spl4_36 ),
    inference(superposition,[],[f394,f587])).

fof(f394,plain,
    ( ! [X4,X2,X3] : k4_xboole_0(X2,X3) = k2_xboole_0(k3_xboole_0(k4_xboole_0(X2,X3),X4),k4_xboole_0(X2,k2_xboole_0(X3,X4)))
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f393])).

fof(f393,plain,
    ( spl4_33
  <=> ! [X3,X2,X4] : k4_xboole_0(X2,X3) = k2_xboole_0(k3_xboole_0(k4_xboole_0(X2,X3),X4),k4_xboole_0(X2,k2_xboole_0(X3,X4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f998,plain,
    ( spl4_16
    | ~ spl4_31
    | ~ spl4_43 ),
    inference(avatar_contradiction_clause,[],[f997])).

fof(f997,plain,
    ( $false
    | spl4_16
    | ~ spl4_31
    | ~ spl4_43 ),
    inference(subsumption_resolution,[],[f735,f137])).

fof(f137,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,sK1)
    | spl4_16 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl4_16
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f735,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl4_31
    | ~ spl4_43 ),
    inference(superposition,[],[f722,f357])).

fof(f357,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f355])).

fof(f722,plain,
    ( ! [X2,X3] : k1_xboole_0 = k3_xboole_0(k4_xboole_0(X3,X2),X2)
    | ~ spl4_43 ),
    inference(avatar_component_clause,[],[f721])).

fof(f721,plain,
    ( spl4_43
  <=> ! [X3,X2] : k1_xboole_0 = k3_xboole_0(k4_xboole_0(X3,X2),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f924,plain,
    ( spl4_36
    | ~ spl4_37
    | ~ spl4_41 ),
    inference(avatar_contradiction_clause,[],[f923])).

fof(f923,plain,
    ( $false
    | spl4_36
    | ~ spl4_37
    | ~ spl4_41 ),
    inference(subsumption_resolution,[],[f655,f903])).

fof(f903,plain,
    ( sK0 != k4_xboole_0(sK0,sK2)
    | spl4_36
    | ~ spl4_41 ),
    inference(superposition,[],[f586,f710])).

fof(f710,plain,
    ( ! [X0] : k4_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK0,X0)
    | ~ spl4_41 ),
    inference(avatar_component_clause,[],[f709])).

fof(f709,plain,
    ( spl4_41
  <=> ! [X0] : k4_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f586,plain,
    ( sK0 != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | spl4_36 ),
    inference(avatar_component_clause,[],[f585])).

fof(f655,plain,
    ( sK0 = k4_xboole_0(sK0,sK2)
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f653])).

fof(f653,plain,
    ( spl4_37
  <=> sK0 = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f822,plain,
    ( spl4_45
    | ~ spl4_17
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f244,f240,f140,f820])).

fof(f140,plain,
    ( spl4_17
  <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f244,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1)
    | ~ spl4_17
    | ~ spl4_25 ),
    inference(superposition,[],[f141,f241])).

fof(f141,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f140])).

fof(f723,plain,
    ( spl4_43
    | ~ spl4_8
    | ~ spl4_25
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f481,f435,f240,f75,f721])).

fof(f435,plain,
    ( spl4_34
  <=> ! [X5,X7,X6] : k3_xboole_0(k4_xboole_0(X5,X6),X7) = k4_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,k2_xboole_0(X6,X7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f481,plain,
    ( ! [X2,X3] : k1_xboole_0 = k3_xboole_0(k4_xboole_0(X3,X2),X2)
    | ~ spl4_8
    | ~ spl4_25
    | ~ spl4_34 ),
    inference(forward_demodulation,[],[f448,f241])).

fof(f448,plain,
    ( ! [X2,X3] : k3_xboole_0(k4_xboole_0(X3,X2),X2) = k4_xboole_0(k4_xboole_0(X3,X2),k4_xboole_0(X3,X2))
    | ~ spl4_8
    | ~ spl4_34 ),
    inference(superposition,[],[f436,f76])).

fof(f436,plain,
    ( ! [X6,X7,X5] : k3_xboole_0(k4_xboole_0(X5,X6),X7) = k4_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,k2_xboole_0(X6,X7)))
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f435])).

fof(f711,plain,
    ( spl4_41
    | ~ spl4_17
    | ~ spl4_31 ),
    inference(avatar_split_clause,[],[f557,f355,f140,f709])).

fof(f557,plain,
    ( ! [X0] : k4_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK0,X0)
    | ~ spl4_17
    | ~ spl4_31 ),
    inference(superposition,[],[f141,f357])).

fof(f656,plain,
    ( spl4_37
    | ~ spl4_3
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f630,f259,f53,f653])).

fof(f53,plain,
    ( spl4_3
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f259,plain,
    ( spl4_28
  <=> ! [X1,X2] :
        ( k4_xboole_0(X1,X2) = X1
        | ~ r1_xboole_0(X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f630,plain,
    ( sK0 = k4_xboole_0(sK0,sK2)
    | ~ spl4_3
    | ~ spl4_28 ),
    inference(unit_resulting_resolution,[],[f54,f260])).

fof(f260,plain,
    ( ! [X2,X1] :
        ( k4_xboole_0(X1,X2) = X1
        | ~ r1_xboole_0(X1,X2) )
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f259])).

fof(f54,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f53])).

fof(f636,plain,
    ( ~ spl4_2
    | ~ spl4_1
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f23,f53,f43,f47])).

fof(f47,plain,
    ( spl4_2
  <=> r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f43,plain,
    ( spl4_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f23,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_xboole_0(sK0,sK1)
    | ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
      & ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_xboole_0(sK0,sK1) ) )
    | ( r1_xboole_0(sK0,sK2)
      & r1_xboole_0(sK0,sK1)
      & ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ( ~ r1_xboole_0(X0,X2)
            | ~ r1_xboole_0(X0,X1) ) )
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) )
   => ( ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
        & ( ~ r1_xboole_0(sK0,sK2)
          | ~ r1_xboole_0(sK0,sK1) ) )
      | ( r1_xboole_0(sK0,sK2)
        & r1_xboole_0(sK0,sK1)
        & ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
        & ( ~ r1_xboole_0(X0,X2)
          | ~ r1_xboole_0(X0,X1) ) )
      | ( r1_xboole_0(X0,X2)
        & r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
            & ~ ( r1_xboole_0(X0,X2)
                & r1_xboole_0(X0,X1) ) )
        & ~ ( r1_xboole_0(X0,X2)
            & r1_xboole_0(X0,X1)
            & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f629,plain,
    ( ~ spl4_13
    | spl4_20
    | ~ spl4_25
    | ~ spl4_36 ),
    inference(avatar_contradiction_clause,[],[f628])).

fof(f628,plain,
    ( $false
    | ~ spl4_13
    | spl4_20
    | ~ spl4_25
    | ~ spl4_36 ),
    inference(subsumption_resolution,[],[f608,f191])).

fof(f191,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | spl4_20 ),
    inference(avatar_component_clause,[],[f190])).

fof(f190,plain,
    ( spl4_20
  <=> k1_xboole_0 = k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f608,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl4_13
    | ~ spl4_25
    | ~ spl4_36 ),
    inference(forward_demodulation,[],[f592,f241])).

fof(f592,plain,
    ( k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,sK0)
    | ~ spl4_13
    | ~ spl4_36 ),
    inference(superposition,[],[f100,f587])).

fof(f100,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl4_13
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f622,plain,
    ( spl4_2
    | ~ spl4_12
    | ~ spl4_20 ),
    inference(avatar_contradiction_clause,[],[f621])).

fof(f621,plain,
    ( $false
    | spl4_2
    | ~ spl4_12
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f200,f48])).

fof(f48,plain,
    ( ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f200,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl4_12
    | ~ spl4_20 ),
    inference(trivial_inequality_removal,[],[f198])).

fof(f198,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl4_12
    | ~ spl4_20 ),
    inference(superposition,[],[f92,f192])).

fof(f192,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f190])).

fof(f92,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) != k1_xboole_0
        | r1_xboole_0(X0,X1) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl4_12
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f603,plain,
    ( ~ spl4_17
    | spl4_18
    | ~ spl4_25
    | ~ spl4_31
    | ~ spl4_35
    | ~ spl4_36 ),
    inference(avatar_contradiction_clause,[],[f602])).

fof(f602,plain,
    ( $false
    | ~ spl4_17
    | spl4_18
    | ~ spl4_25
    | ~ spl4_31
    | ~ spl4_35
    | ~ spl4_36 ),
    inference(subsumption_resolution,[],[f167,f601])).

fof(f601,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK2)
    | ~ spl4_17
    | ~ spl4_25
    | ~ spl4_31
    | ~ spl4_35
    | ~ spl4_36 ),
    inference(forward_demodulation,[],[f600,f241])).

fof(f600,plain,
    ( k3_xboole_0(sK0,sK2) = k4_xboole_0(sK0,sK0)
    | ~ spl4_17
    | ~ spl4_31
    | ~ spl4_35
    | ~ spl4_36 ),
    inference(forward_demodulation,[],[f599,f357])).

fof(f599,plain,
    ( k4_xboole_0(sK0,sK0) = k3_xboole_0(k4_xboole_0(sK0,sK1),sK2)
    | ~ spl4_17
    | ~ spl4_31
    | ~ spl4_35
    | ~ spl4_36 ),
    inference(forward_demodulation,[],[f589,f557])).

fof(f167,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,sK2)
    | spl4_18 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl4_18
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f588,plain,
    ( spl4_36
    | ~ spl4_2
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f263,f259,f47,f585])).

fof(f263,plain,
    ( sK0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl4_2
    | ~ spl4_28 ),
    inference(unit_resulting_resolution,[],[f49,f260])).

fof(f49,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f493,plain,
    ( spl4_35
    | ~ spl4_13
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f159,f140,f99,f491])).

fof(f159,plain,
    ( ! [X6,X7,X5] : k3_xboole_0(k4_xboole_0(X5,X6),X7) = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,k2_xboole_0(X6,X7))))
    | ~ spl4_13
    | ~ spl4_17 ),
    inference(forward_demodulation,[],[f152,f141])).

fof(f152,plain,
    ( ! [X6,X7,X5] : k3_xboole_0(k4_xboole_0(X5,X6),X7) = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(k4_xboole_0(X5,X6),X7)))
    | ~ spl4_13
    | ~ spl4_17 ),
    inference(superposition,[],[f141,f100])).

fof(f437,plain,
    ( spl4_34
    | ~ spl4_13
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f155,f140,f99,f435])).

fof(f155,plain,
    ( ! [X6,X7,X5] : k3_xboole_0(k4_xboole_0(X5,X6),X7) = k4_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,k2_xboole_0(X6,X7)))
    | ~ spl4_13
    | ~ spl4_17 ),
    inference(superposition,[],[f100,f141])).

fof(f395,plain,
    ( spl4_33
    | ~ spl4_14
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f154,f140,f103,f393])).

fof(f103,plain,
    ( spl4_14
  <=> ! [X1,X0] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f154,plain,
    ( ! [X4,X2,X3] : k4_xboole_0(X2,X3) = k2_xboole_0(k3_xboole_0(k4_xboole_0(X2,X3),X4),k4_xboole_0(X2,k2_xboole_0(X3,X4)))
    | ~ spl4_14
    | ~ spl4_17 ),
    inference(superposition,[],[f104,f141])).

fof(f104,plain,
    ( ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f103])).

fof(f358,plain,
    ( spl4_31
    | ~ spl4_1
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f264,f259,f43,f355])).

fof(f264,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl4_1
    | ~ spl4_28 ),
    inference(unit_resulting_resolution,[],[f45,f260])).

fof(f45,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f261,plain,
    ( spl4_28
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_11
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f132,f103,f87,f79,f71,f259])).

fof(f71,plain,
    ( spl4_7
  <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f87,plain,
    ( spl4_11
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f132,plain,
    ( ! [X2,X1] :
        ( k4_xboole_0(X1,X2) = X1
        | ~ r1_xboole_0(X1,X2) )
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_11
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f128,f94])).

fof(f94,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(superposition,[],[f80,f72])).

fof(f72,plain,
    ( ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f71])).

fof(f128,plain,
    ( ! [X2,X1] :
        ( k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2)) = X1
        | ~ r1_xboole_0(X1,X2) )
    | ~ spl4_11
    | ~ spl4_14 ),
    inference(superposition,[],[f104,f88])).

fof(f88,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f87])).

fof(f242,plain,
    ( spl4_25
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f126,f99,f67,f63,f240])).

fof(f63,plain,
    ( spl4_5
  <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f67,plain,
    ( spl4_6
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f126,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f124,f64])).

fof(f64,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f63])).

fof(f124,plain,
    ( ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)
    | ~ spl4_6
    | ~ spl4_13 ),
    inference(superposition,[],[f100,f68])).

fof(f68,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f67])).

fof(f234,plain,
    ( spl4_24
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f94,f79,f71,f232])).

fof(f180,plain,
    ( spl4_2
    | spl4_3 ),
    inference(avatar_split_clause,[],[f57,f53,f47])).

fof(f57,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | spl4_3 ),
    inference(subsumption_resolution,[],[f28,f55])).

fof(f55,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f53])).

fof(f28,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f168,plain,
    ( ~ spl4_18
    | spl4_3
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f115,f91,f53,f165])).

fof(f115,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,sK2)
    | spl4_3
    | ~ spl4_12 ),
    inference(unit_resulting_resolution,[],[f55,f92])).

fof(f142,plain,(
    spl4_17 ),
    inference(avatar_split_clause,[],[f41,f140])).

fof(f41,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f138,plain,
    ( ~ spl4_16
    | spl4_1
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f114,f91,f43,f135])).

fof(f114,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,sK1)
    | spl4_1
    | ~ spl4_12 ),
    inference(unit_resulting_resolution,[],[f44,f92])).

fof(f44,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f105,plain,(
    spl4_14 ),
    inference(avatar_split_clause,[],[f36,f103])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f101,plain,(
    spl4_13 ),
    inference(avatar_split_clause,[],[f35,f99])).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f93,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f40,f91])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f89,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f39,f87])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f81,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f34,f79])).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f77,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f33,f75])).

fof(f33,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f73,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f32,f71])).

fof(f32,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f69,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f31,f67])).

fof(f31,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f65,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f30,f63])).

fof(f30,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f50,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f27,f47,f43])).

fof(f27,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.15  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n006.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 10:44:52 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.22/0.47  % (10325)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.48  % (10322)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.49  % (10321)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.49  % (10323)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.49  % (10317)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.49  % (10323)Refutation not found, incomplete strategy% (10323)------------------------------
% 0.22/0.49  % (10323)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (10323)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (10323)Memory used [KB]: 10618
% 0.22/0.49  % (10323)Time elapsed: 0.065 s
% 0.22/0.49  % (10323)------------------------------
% 0.22/0.49  % (10323)------------------------------
% 0.22/0.49  % (10314)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.49  % (10318)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.50  % (10320)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.50  % (10315)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.50  % (10312)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.50  % (10326)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.50  % (10327)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.50  % (10329)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.50  % (10328)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.50  % (10313)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.50  % (10319)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.51  % (10324)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.51  % (10316)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.52  % (10317)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f1028,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f50,f65,f69,f73,f77,f81,f89,f93,f101,f105,f138,f142,f168,f180,f234,f242,f261,f358,f395,f437,f493,f588,f603,f622,f629,f636,f656,f711,f723,f822,f924,f998,f1027])).
% 0.22/0.52  fof(f1027,plain,(
% 0.22/0.52    ~spl4_8 | ~spl4_9 | ~spl4_24 | ~spl4_25 | spl4_31 | ~spl4_33 | ~spl4_35 | ~spl4_36 | ~spl4_45),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f1026])).
% 0.22/0.52  fof(f1026,plain,(
% 0.22/0.52    $false | (~spl4_8 | ~spl4_9 | ~spl4_24 | ~spl4_25 | spl4_31 | ~spl4_33 | ~spl4_35 | ~spl4_36 | ~spl4_45)),
% 0.22/0.52    inference(subsumption_resolution,[],[f1009,f356])).
% 0.22/0.52  fof(f356,plain,(
% 0.22/0.52    sK0 != k4_xboole_0(sK0,sK1) | spl4_31),
% 0.22/0.52    inference(avatar_component_clause,[],[f355])).
% 0.22/0.52  fof(f355,plain,(
% 0.22/0.52    spl4_31 <=> sK0 = k4_xboole_0(sK0,sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 0.22/0.52  fof(f1009,plain,(
% 0.22/0.52    sK0 = k4_xboole_0(sK0,sK1) | (~spl4_8 | ~spl4_9 | ~spl4_24 | ~spl4_25 | ~spl4_33 | ~spl4_35 | ~spl4_36 | ~spl4_45)),
% 0.22/0.52    inference(forward_demodulation,[],[f1008,f233])).
% 0.22/0.52  fof(f233,plain,(
% 0.22/0.52    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) ) | ~spl4_24),
% 0.22/0.52    inference(avatar_component_clause,[],[f232])).
% 0.22/0.52  fof(f232,plain,(
% 0.22/0.52    spl4_24 <=> ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.22/0.52  fof(f1008,plain,(
% 0.22/0.52    k4_xboole_0(sK0,sK1) = k2_xboole_0(k1_xboole_0,sK0) | (~spl4_8 | ~spl4_9 | ~spl4_25 | ~spl4_33 | ~spl4_35 | ~spl4_36 | ~spl4_45)),
% 0.22/0.52    inference(forward_demodulation,[],[f591,f975])).
% 0.22/0.52  fof(f975,plain,(
% 0.22/0.52    k1_xboole_0 = k3_xboole_0(k4_xboole_0(sK0,sK1),sK2) | (~spl4_8 | ~spl4_9 | ~spl4_25 | ~spl4_35 | ~spl4_36 | ~spl4_45)),
% 0.22/0.52    inference(forward_demodulation,[],[f589,f855])).
% 0.22/0.52  fof(f855,plain,(
% 0.22/0.52    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X3,X2))) ) | (~spl4_8 | ~spl4_9 | ~spl4_25 | ~spl4_45)),
% 0.22/0.52    inference(forward_demodulation,[],[f825,f854])).
% 0.22/0.52  fof(f854,plain,(
% 0.22/0.52    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1)) ) | (~spl4_8 | ~spl4_25 | ~spl4_45)),
% 0.22/0.52    inference(forward_demodulation,[],[f824,f241])).
% 0.22/0.52  fof(f241,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | ~spl4_25),
% 0.22/0.52    inference(avatar_component_clause,[],[f240])).
% 0.22/0.52  fof(f240,plain,(
% 0.22/0.52    spl4_25 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.22/0.52  fof(f824,plain,(
% 0.22/0.52    ( ! [X1] : (k4_xboole_0(k1_xboole_0,X1) = k4_xboole_0(X1,X1)) ) | (~spl4_8 | ~spl4_45)),
% 0.22/0.52    inference(superposition,[],[f821,f76])).
% 0.22/0.52  fof(f76,plain,(
% 0.22/0.52    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) ) | ~spl4_8),
% 0.22/0.52    inference(avatar_component_clause,[],[f75])).
% 0.22/0.52  fof(f75,plain,(
% 0.22/0.52    spl4_8 <=> ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.52  fof(f821,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1)) ) | ~spl4_45),
% 0.22/0.52    inference(avatar_component_clause,[],[f820])).
% 0.22/0.52  fof(f820,plain,(
% 0.22/0.52    spl4_45 <=> ! [X1,X0] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).
% 0.22/0.52  fof(f825,plain,(
% 0.22/0.52    ( ! [X2,X3] : (k4_xboole_0(k1_xboole_0,X3) = k4_xboole_0(X2,k2_xboole_0(X3,X2))) ) | (~spl4_9 | ~spl4_45)),
% 0.22/0.52    inference(superposition,[],[f821,f80])).
% 0.22/0.52  fof(f80,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl4_9),
% 0.22/0.52    inference(avatar_component_clause,[],[f79])).
% 0.22/0.52  fof(f79,plain,(
% 0.22/0.52    spl4_9 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.22/0.52  fof(f589,plain,(
% 0.22/0.52    k3_xboole_0(k4_xboole_0(sK0,sK1),sK2) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK0)) | (~spl4_35 | ~spl4_36)),
% 0.22/0.52    inference(superposition,[],[f492,f587])).
% 0.22/0.52  fof(f587,plain,(
% 0.22/0.52    sK0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~spl4_36),
% 0.22/0.52    inference(avatar_component_clause,[],[f585])).
% 0.22/0.52  fof(f585,plain,(
% 0.22/0.52    spl4_36 <=> sK0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 0.22/0.52  fof(f492,plain,(
% 0.22/0.52    ( ! [X6,X7,X5] : (k3_xboole_0(k4_xboole_0(X5,X6),X7) = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,k2_xboole_0(X6,X7))))) ) | ~spl4_35),
% 0.22/0.52    inference(avatar_component_clause,[],[f491])).
% 0.22/0.52  fof(f491,plain,(
% 0.22/0.52    spl4_35 <=> ! [X5,X7,X6] : k3_xboole_0(k4_xboole_0(X5,X6),X7) = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,k2_xboole_0(X6,X7))))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 0.22/0.52  fof(f591,plain,(
% 0.22/0.52    k4_xboole_0(sK0,sK1) = k2_xboole_0(k3_xboole_0(k4_xboole_0(sK0,sK1),sK2),sK0) | (~spl4_33 | ~spl4_36)),
% 0.22/0.52    inference(superposition,[],[f394,f587])).
% 0.22/0.52  fof(f394,plain,(
% 0.22/0.52    ( ! [X4,X2,X3] : (k4_xboole_0(X2,X3) = k2_xboole_0(k3_xboole_0(k4_xboole_0(X2,X3),X4),k4_xboole_0(X2,k2_xboole_0(X3,X4)))) ) | ~spl4_33),
% 0.22/0.52    inference(avatar_component_clause,[],[f393])).
% 0.22/0.52  fof(f393,plain,(
% 0.22/0.52    spl4_33 <=> ! [X3,X2,X4] : k4_xboole_0(X2,X3) = k2_xboole_0(k3_xboole_0(k4_xboole_0(X2,X3),X4),k4_xboole_0(X2,k2_xboole_0(X3,X4)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 0.22/0.52  fof(f998,plain,(
% 0.22/0.52    spl4_16 | ~spl4_31 | ~spl4_43),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f997])).
% 0.22/0.52  fof(f997,plain,(
% 0.22/0.52    $false | (spl4_16 | ~spl4_31 | ~spl4_43)),
% 0.22/0.52    inference(subsumption_resolution,[],[f735,f137])).
% 0.22/0.52  fof(f137,plain,(
% 0.22/0.52    k1_xboole_0 != k3_xboole_0(sK0,sK1) | spl4_16),
% 0.22/0.52    inference(avatar_component_clause,[],[f135])).
% 0.22/0.52  fof(f135,plain,(
% 0.22/0.52    spl4_16 <=> k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.22/0.52  fof(f735,plain,(
% 0.22/0.52    k1_xboole_0 = k3_xboole_0(sK0,sK1) | (~spl4_31 | ~spl4_43)),
% 0.22/0.52    inference(superposition,[],[f722,f357])).
% 0.22/0.52  fof(f357,plain,(
% 0.22/0.52    sK0 = k4_xboole_0(sK0,sK1) | ~spl4_31),
% 0.22/0.52    inference(avatar_component_clause,[],[f355])).
% 0.22/0.52  fof(f722,plain,(
% 0.22/0.52    ( ! [X2,X3] : (k1_xboole_0 = k3_xboole_0(k4_xboole_0(X3,X2),X2)) ) | ~spl4_43),
% 0.22/0.52    inference(avatar_component_clause,[],[f721])).
% 0.22/0.52  fof(f721,plain,(
% 0.22/0.52    spl4_43 <=> ! [X3,X2] : k1_xboole_0 = k3_xboole_0(k4_xboole_0(X3,X2),X2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 0.22/0.52  fof(f924,plain,(
% 0.22/0.52    spl4_36 | ~spl4_37 | ~spl4_41),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f923])).
% 0.22/0.52  fof(f923,plain,(
% 0.22/0.52    $false | (spl4_36 | ~spl4_37 | ~spl4_41)),
% 0.22/0.52    inference(subsumption_resolution,[],[f655,f903])).
% 0.22/0.52  fof(f903,plain,(
% 0.22/0.52    sK0 != k4_xboole_0(sK0,sK2) | (spl4_36 | ~spl4_41)),
% 0.22/0.52    inference(superposition,[],[f586,f710])).
% 0.22/0.52  fof(f710,plain,(
% 0.22/0.52    ( ! [X0] : (k4_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK0,X0)) ) | ~spl4_41),
% 0.22/0.52    inference(avatar_component_clause,[],[f709])).
% 0.22/0.52  fof(f709,plain,(
% 0.22/0.52    spl4_41 <=> ! [X0] : k4_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK0,X0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 0.22/0.52  fof(f586,plain,(
% 0.22/0.52    sK0 != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | spl4_36),
% 0.22/0.52    inference(avatar_component_clause,[],[f585])).
% 0.22/0.52  fof(f655,plain,(
% 0.22/0.52    sK0 = k4_xboole_0(sK0,sK2) | ~spl4_37),
% 0.22/0.52    inference(avatar_component_clause,[],[f653])).
% 0.22/0.52  fof(f653,plain,(
% 0.22/0.52    spl4_37 <=> sK0 = k4_xboole_0(sK0,sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 0.22/0.52  fof(f822,plain,(
% 0.22/0.52    spl4_45 | ~spl4_17 | ~spl4_25),
% 0.22/0.52    inference(avatar_split_clause,[],[f244,f240,f140,f820])).
% 0.22/0.53  fof(f140,plain,(
% 0.22/0.53    spl4_17 <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.22/0.53  fof(f244,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1)) ) | (~spl4_17 | ~spl4_25)),
% 0.22/0.53    inference(superposition,[],[f141,f241])).
% 0.22/0.53  fof(f141,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl4_17),
% 0.22/0.53    inference(avatar_component_clause,[],[f140])).
% 0.22/0.53  fof(f723,plain,(
% 0.22/0.53    spl4_43 | ~spl4_8 | ~spl4_25 | ~spl4_34),
% 0.22/0.53    inference(avatar_split_clause,[],[f481,f435,f240,f75,f721])).
% 0.22/0.53  fof(f435,plain,(
% 0.22/0.53    spl4_34 <=> ! [X5,X7,X6] : k3_xboole_0(k4_xboole_0(X5,X6),X7) = k4_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,k2_xboole_0(X6,X7)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 0.22/0.53  fof(f481,plain,(
% 0.22/0.53    ( ! [X2,X3] : (k1_xboole_0 = k3_xboole_0(k4_xboole_0(X3,X2),X2)) ) | (~spl4_8 | ~spl4_25 | ~spl4_34)),
% 0.22/0.53    inference(forward_demodulation,[],[f448,f241])).
% 0.22/0.53  fof(f448,plain,(
% 0.22/0.53    ( ! [X2,X3] : (k3_xboole_0(k4_xboole_0(X3,X2),X2) = k4_xboole_0(k4_xboole_0(X3,X2),k4_xboole_0(X3,X2))) ) | (~spl4_8 | ~spl4_34)),
% 0.22/0.53    inference(superposition,[],[f436,f76])).
% 0.22/0.53  fof(f436,plain,(
% 0.22/0.53    ( ! [X6,X7,X5] : (k3_xboole_0(k4_xboole_0(X5,X6),X7) = k4_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,k2_xboole_0(X6,X7)))) ) | ~spl4_34),
% 0.22/0.53    inference(avatar_component_clause,[],[f435])).
% 0.22/0.53  fof(f711,plain,(
% 0.22/0.53    spl4_41 | ~spl4_17 | ~spl4_31),
% 0.22/0.53    inference(avatar_split_clause,[],[f557,f355,f140,f709])).
% 0.22/0.53  fof(f557,plain,(
% 0.22/0.53    ( ! [X0] : (k4_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK0,X0)) ) | (~spl4_17 | ~spl4_31)),
% 0.22/0.53    inference(superposition,[],[f141,f357])).
% 0.22/0.53  fof(f656,plain,(
% 0.22/0.53    spl4_37 | ~spl4_3 | ~spl4_28),
% 0.22/0.53    inference(avatar_split_clause,[],[f630,f259,f53,f653])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    spl4_3 <=> r1_xboole_0(sK0,sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.53  fof(f259,plain,(
% 0.22/0.53    spl4_28 <=> ! [X1,X2] : (k4_xboole_0(X1,X2) = X1 | ~r1_xboole_0(X1,X2))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.22/0.53  fof(f630,plain,(
% 0.22/0.53    sK0 = k4_xboole_0(sK0,sK2) | (~spl4_3 | ~spl4_28)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f54,f260])).
% 0.22/0.53  fof(f260,plain,(
% 0.22/0.53    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = X1 | ~r1_xboole_0(X1,X2)) ) | ~spl4_28),
% 0.22/0.53    inference(avatar_component_clause,[],[f259])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    r1_xboole_0(sK0,sK2) | ~spl4_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f53])).
% 0.22/0.53  fof(f636,plain,(
% 0.22/0.53    ~spl4_2 | ~spl4_1 | ~spl4_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f23,f53,f43,f47])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    spl4_2 <=> r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    spl4_1 <=> r1_xboole_0(sK0,sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1) | ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 0.22/0.53    inference(cnf_transformation,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    (r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) & (~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1))) | (r1_xboole_0(sK0,sK2) & r1_xboole_0(sK0,sK1) & ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ? [X0,X1,X2] : ((r1_xboole_0(X0,k2_xboole_0(X1,X2)) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2)))) => ((r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) & (~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1))) | (r1_xboole_0(sK0,sK2) & r1_xboole_0(sK0,sK1) & ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ? [X0,X1,X2] : ((r1_xboole_0(X0,k2_xboole_0(X1,X2)) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.22/0.53    inference(ennf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.22/0.53    inference(negated_conjecture,[],[f12])).
% 0.22/0.53  fof(f12,conjecture,(
% 0.22/0.53    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
% 0.22/0.53  fof(f629,plain,(
% 0.22/0.53    ~spl4_13 | spl4_20 | ~spl4_25 | ~spl4_36),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f628])).
% 0.22/0.53  fof(f628,plain,(
% 0.22/0.53    $false | (~spl4_13 | spl4_20 | ~spl4_25 | ~spl4_36)),
% 0.22/0.53    inference(subsumption_resolution,[],[f608,f191])).
% 0.22/0.53  fof(f191,plain,(
% 0.22/0.53    k1_xboole_0 != k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | spl4_20),
% 0.22/0.53    inference(avatar_component_clause,[],[f190])).
% 0.22/0.53  fof(f190,plain,(
% 0.22/0.53    spl4_20 <=> k1_xboole_0 = k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.22/0.53  fof(f608,plain,(
% 0.22/0.53    k1_xboole_0 = k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | (~spl4_13 | ~spl4_25 | ~spl4_36)),
% 0.22/0.53    inference(forward_demodulation,[],[f592,f241])).
% 0.22/0.53  fof(f592,plain,(
% 0.22/0.53    k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,sK0) | (~spl4_13 | ~spl4_36)),
% 0.22/0.53    inference(superposition,[],[f100,f587])).
% 0.22/0.53  fof(f100,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl4_13),
% 0.22/0.53    inference(avatar_component_clause,[],[f99])).
% 0.22/0.53  fof(f99,plain,(
% 0.22/0.53    spl4_13 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.22/0.53  fof(f622,plain,(
% 0.22/0.53    spl4_2 | ~spl4_12 | ~spl4_20),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f621])).
% 0.22/0.53  fof(f621,plain,(
% 0.22/0.53    $false | (spl4_2 | ~spl4_12 | ~spl4_20)),
% 0.22/0.53    inference(subsumption_resolution,[],[f200,f48])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | spl4_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f47])).
% 0.22/0.53  fof(f200,plain,(
% 0.22/0.53    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | (~spl4_12 | ~spl4_20)),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f198])).
% 0.22/0.53  fof(f198,plain,(
% 0.22/0.53    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | (~spl4_12 | ~spl4_20)),
% 0.22/0.53    inference(superposition,[],[f92,f192])).
% 0.22/0.53  fof(f192,plain,(
% 0.22/0.53    k1_xboole_0 = k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~spl4_20),
% 0.22/0.53    inference(avatar_component_clause,[],[f190])).
% 0.22/0.53  fof(f92,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) ) | ~spl4_12),
% 0.22/0.53    inference(avatar_component_clause,[],[f91])).
% 0.22/0.53  fof(f91,plain,(
% 0.22/0.53    spl4_12 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.22/0.53  fof(f603,plain,(
% 0.22/0.53    ~spl4_17 | spl4_18 | ~spl4_25 | ~spl4_31 | ~spl4_35 | ~spl4_36),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f602])).
% 0.22/0.53  fof(f602,plain,(
% 0.22/0.53    $false | (~spl4_17 | spl4_18 | ~spl4_25 | ~spl4_31 | ~spl4_35 | ~spl4_36)),
% 0.22/0.53    inference(subsumption_resolution,[],[f167,f601])).
% 0.22/0.53  fof(f601,plain,(
% 0.22/0.53    k1_xboole_0 = k3_xboole_0(sK0,sK2) | (~spl4_17 | ~spl4_25 | ~spl4_31 | ~spl4_35 | ~spl4_36)),
% 0.22/0.53    inference(forward_demodulation,[],[f600,f241])).
% 0.22/0.53  fof(f600,plain,(
% 0.22/0.53    k3_xboole_0(sK0,sK2) = k4_xboole_0(sK0,sK0) | (~spl4_17 | ~spl4_31 | ~spl4_35 | ~spl4_36)),
% 0.22/0.53    inference(forward_demodulation,[],[f599,f357])).
% 0.22/0.53  fof(f599,plain,(
% 0.22/0.53    k4_xboole_0(sK0,sK0) = k3_xboole_0(k4_xboole_0(sK0,sK1),sK2) | (~spl4_17 | ~spl4_31 | ~spl4_35 | ~spl4_36)),
% 0.22/0.53    inference(forward_demodulation,[],[f589,f557])).
% 0.22/0.53  fof(f167,plain,(
% 0.22/0.53    k1_xboole_0 != k3_xboole_0(sK0,sK2) | spl4_18),
% 0.22/0.53    inference(avatar_component_clause,[],[f165])).
% 0.22/0.53  fof(f165,plain,(
% 0.22/0.53    spl4_18 <=> k1_xboole_0 = k3_xboole_0(sK0,sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.22/0.53  fof(f588,plain,(
% 0.22/0.53    spl4_36 | ~spl4_2 | ~spl4_28),
% 0.22/0.53    inference(avatar_split_clause,[],[f263,f259,f47,f585])).
% 0.22/0.53  fof(f263,plain,(
% 0.22/0.53    sK0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | (~spl4_2 | ~spl4_28)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f49,f260])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~spl4_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f47])).
% 0.22/0.53  fof(f493,plain,(
% 0.22/0.53    spl4_35 | ~spl4_13 | ~spl4_17),
% 0.22/0.53    inference(avatar_split_clause,[],[f159,f140,f99,f491])).
% 0.22/0.53  fof(f159,plain,(
% 0.22/0.53    ( ! [X6,X7,X5] : (k3_xboole_0(k4_xboole_0(X5,X6),X7) = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,k2_xboole_0(X6,X7))))) ) | (~spl4_13 | ~spl4_17)),
% 0.22/0.53    inference(forward_demodulation,[],[f152,f141])).
% 0.22/0.53  fof(f152,plain,(
% 0.22/0.53    ( ! [X6,X7,X5] : (k3_xboole_0(k4_xboole_0(X5,X6),X7) = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(k4_xboole_0(X5,X6),X7)))) ) | (~spl4_13 | ~spl4_17)),
% 0.22/0.53    inference(superposition,[],[f141,f100])).
% 0.22/0.53  fof(f437,plain,(
% 0.22/0.53    spl4_34 | ~spl4_13 | ~spl4_17),
% 0.22/0.53    inference(avatar_split_clause,[],[f155,f140,f99,f435])).
% 0.22/0.53  fof(f155,plain,(
% 0.22/0.53    ( ! [X6,X7,X5] : (k3_xboole_0(k4_xboole_0(X5,X6),X7) = k4_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,k2_xboole_0(X6,X7)))) ) | (~spl4_13 | ~spl4_17)),
% 0.22/0.53    inference(superposition,[],[f100,f141])).
% 0.22/0.53  fof(f395,plain,(
% 0.22/0.53    spl4_33 | ~spl4_14 | ~spl4_17),
% 0.22/0.53    inference(avatar_split_clause,[],[f154,f140,f103,f393])).
% 0.22/0.53  fof(f103,plain,(
% 0.22/0.53    spl4_14 <=> ! [X1,X0] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.22/0.53  fof(f154,plain,(
% 0.22/0.53    ( ! [X4,X2,X3] : (k4_xboole_0(X2,X3) = k2_xboole_0(k3_xboole_0(k4_xboole_0(X2,X3),X4),k4_xboole_0(X2,k2_xboole_0(X3,X4)))) ) | (~spl4_14 | ~spl4_17)),
% 0.22/0.53    inference(superposition,[],[f104,f141])).
% 0.22/0.53  fof(f104,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) ) | ~spl4_14),
% 0.22/0.53    inference(avatar_component_clause,[],[f103])).
% 0.22/0.53  fof(f358,plain,(
% 0.22/0.53    spl4_31 | ~spl4_1 | ~spl4_28),
% 0.22/0.53    inference(avatar_split_clause,[],[f264,f259,f43,f355])).
% 0.22/0.53  fof(f264,plain,(
% 0.22/0.53    sK0 = k4_xboole_0(sK0,sK1) | (~spl4_1 | ~spl4_28)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f45,f260])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    r1_xboole_0(sK0,sK1) | ~spl4_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f43])).
% 0.22/0.53  fof(f261,plain,(
% 0.22/0.53    spl4_28 | ~spl4_7 | ~spl4_9 | ~spl4_11 | ~spl4_14),
% 0.22/0.53    inference(avatar_split_clause,[],[f132,f103,f87,f79,f71,f259])).
% 0.22/0.53  fof(f71,plain,(
% 0.22/0.53    spl4_7 <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.53  fof(f87,plain,(
% 0.22/0.53    spl4_11 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.22/0.53  fof(f132,plain,(
% 0.22/0.53    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = X1 | ~r1_xboole_0(X1,X2)) ) | (~spl4_7 | ~spl4_9 | ~spl4_11 | ~spl4_14)),
% 0.22/0.53    inference(forward_demodulation,[],[f128,f94])).
% 0.22/0.53  fof(f94,plain,(
% 0.22/0.53    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) ) | (~spl4_7 | ~spl4_9)),
% 0.22/0.53    inference(superposition,[],[f80,f72])).
% 0.22/0.53  fof(f72,plain,(
% 0.22/0.53    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl4_7),
% 0.22/0.53    inference(avatar_component_clause,[],[f71])).
% 0.22/0.53  fof(f128,plain,(
% 0.22/0.53    ( ! [X2,X1] : (k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2)) = X1 | ~r1_xboole_0(X1,X2)) ) | (~spl4_11 | ~spl4_14)),
% 0.22/0.53    inference(superposition,[],[f104,f88])).
% 0.22/0.53  fof(f88,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) ) | ~spl4_11),
% 0.22/0.53    inference(avatar_component_clause,[],[f87])).
% 0.22/0.53  fof(f242,plain,(
% 0.22/0.53    spl4_25 | ~spl4_5 | ~spl4_6 | ~spl4_13),
% 0.22/0.53    inference(avatar_split_clause,[],[f126,f99,f67,f63,f240])).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    spl4_5 <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    spl4_6 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.53  fof(f126,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | (~spl4_5 | ~spl4_6 | ~spl4_13)),
% 0.22/0.53    inference(forward_demodulation,[],[f124,f64])).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) ) | ~spl4_5),
% 0.22/0.53    inference(avatar_component_clause,[],[f63])).
% 0.22/0.53  fof(f124,plain,(
% 0.22/0.53    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) ) | (~spl4_6 | ~spl4_13)),
% 0.22/0.53    inference(superposition,[],[f100,f68])).
% 0.22/0.53  fof(f68,plain,(
% 0.22/0.53    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl4_6),
% 0.22/0.53    inference(avatar_component_clause,[],[f67])).
% 0.22/0.53  fof(f234,plain,(
% 0.22/0.53    spl4_24 | ~spl4_7 | ~spl4_9),
% 0.22/0.53    inference(avatar_split_clause,[],[f94,f79,f71,f232])).
% 0.22/0.53  fof(f180,plain,(
% 0.22/0.53    spl4_2 | spl4_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f57,f53,f47])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | spl4_3),
% 0.22/0.53    inference(subsumption_resolution,[],[f28,f55])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    ~r1_xboole_0(sK0,sK2) | spl4_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f53])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | r1_xboole_0(sK0,sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f19])).
% 0.22/0.53  fof(f168,plain,(
% 0.22/0.53    ~spl4_18 | spl4_3 | ~spl4_12),
% 0.22/0.53    inference(avatar_split_clause,[],[f115,f91,f53,f165])).
% 0.22/0.53  fof(f115,plain,(
% 0.22/0.53    k1_xboole_0 != k3_xboole_0(sK0,sK2) | (spl4_3 | ~spl4_12)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f55,f92])).
% 0.22/0.53  fof(f142,plain,(
% 0.22/0.53    spl4_17),
% 0.22/0.53    inference(avatar_split_clause,[],[f41,f140])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.22/0.53  fof(f138,plain,(
% 0.22/0.53    ~spl4_16 | spl4_1 | ~spl4_12),
% 0.22/0.53    inference(avatar_split_clause,[],[f114,f91,f43,f135])).
% 0.22/0.53  fof(f114,plain,(
% 0.22/0.53    k1_xboole_0 != k3_xboole_0(sK0,sK1) | (spl4_1 | ~spl4_12)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f44,f92])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ~r1_xboole_0(sK0,sK1) | spl4_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f43])).
% 0.22/0.53  fof(f105,plain,(
% 0.22/0.53    spl4_14),
% 0.22/0.53    inference(avatar_split_clause,[],[f36,f103])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,axiom,(
% 0.22/0.53    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.22/0.53  fof(f101,plain,(
% 0.22/0.53    spl4_13),
% 0.22/0.53    inference(avatar_split_clause,[],[f35,f99])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,axiom,(
% 0.22/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.53  fof(f93,plain,(
% 0.22/0.53    spl4_12),
% 0.22/0.53    inference(avatar_split_clause,[],[f40,f91])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.53    inference(nnf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.22/0.53  fof(f89,plain,(
% 0.22/0.53    spl4_11),
% 0.22/0.53    inference(avatar_split_clause,[],[f39,f87])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f22])).
% 0.22/0.53  fof(f81,plain,(
% 0.22/0.53    spl4_9),
% 0.22/0.53    inference(avatar_split_clause,[],[f34,f79])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.53  fof(f77,plain,(
% 0.22/0.53    spl4_8),
% 0.22/0.53    inference(avatar_split_clause,[],[f33,f75])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.22/0.53    inference(rectify,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.22/0.53  fof(f73,plain,(
% 0.22/0.53    spl4_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f32,f71])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    spl4_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f31,f67])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    spl4_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f30,f63])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    spl4_1 | spl4_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f27,f47,f43])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | r1_xboole_0(sK0,sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f19])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (10317)------------------------------
% 0.22/0.53  % (10317)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (10317)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (10317)Memory used [KB]: 6908
% 0.22/0.53  % (10317)Time elapsed: 0.081 s
% 0.22/0.53  % (10317)------------------------------
% 0.22/0.53  % (10317)------------------------------
% 0.22/0.53  % (10311)Success in time 0.156 s
%------------------------------------------------------------------------------
