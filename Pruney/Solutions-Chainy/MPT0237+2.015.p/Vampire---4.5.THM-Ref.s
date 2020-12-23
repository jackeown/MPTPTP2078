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
% DateTime   : Thu Dec  3 12:37:31 EST 2020

% Result     : Theorem 6.89s
% Output     : Refutation 6.89s
% Verified   : 
% Statistics : Number of formulae       :  185 ( 584 expanded)
%              Number of leaves         :   48 ( 230 expanded)
%              Depth                    :   10
%              Number of atoms          :  504 (1085 expanded)
%              Number of equality atoms :  153 ( 588 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2535,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f90,f94,f102,f106,f110,f124,f139,f143,f157,f172,f177,f189,f193,f496,f600,f732,f745,f824,f1035,f1793,f1810,f1817,f2305,f2526,f2534])).

fof(f2534,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_15
    | ~ spl5_18
    | ~ spl5_27
    | ~ spl5_30
    | ~ spl5_36
    | ~ spl5_57
    | ~ spl5_71
    | spl5_74 ),
    inference(avatar_contradiction_clause,[],[f2533])).

fof(f2533,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_15
    | ~ spl5_18
    | ~ spl5_27
    | ~ spl5_30
    | ~ spl5_36
    | ~ spl5_57
    | ~ spl5_71
    | spl5_74 ),
    inference(subsumption_resolution,[],[f2532,f93])).

fof(f93,plain,
    ( ! [X2,X3,X1] : sP0(X1,X1,X2,X3)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl5_2
  <=> ! [X1,X3,X2] : sP0(X1,X1,X2,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f2532,plain,
    ( ~ sP0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | ~ spl5_1
    | ~ spl5_5
    | ~ spl5_15
    | ~ spl5_18
    | ~ spl5_27
    | ~ spl5_30
    | ~ spl5_36
    | ~ spl5_57
    | ~ spl5_71
    | spl5_74 ),
    inference(forward_demodulation,[],[f2531,f538])).

fof(f538,plain,
    ( ! [X2,X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | ~ spl5_15
    | ~ spl5_27 ),
    inference(unit_resulting_resolution,[],[f171,f495])).

fof(f495,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f494])).

fof(f494,plain,
    ( spl5_27
  <=> ! [X1,X0] :
        ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f171,plain,
    ( ! [X2,X0,X1] : r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl5_15
  <=> ! [X1,X0,X2] : r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f2531,plain,
    ( ~ sP0(k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | ~ spl5_1
    | ~ spl5_5
    | ~ spl5_18
    | ~ spl5_30
    | ~ spl5_36
    | ~ spl5_57
    | ~ spl5_71
    | spl5_74 ),
    inference(forward_demodulation,[],[f2530,f2444])).

fof(f2444,plain,
    ( ! [X0] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k5_xboole_0(k1_xboole_0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | ~ spl5_1
    | ~ spl5_36
    | ~ spl5_71 ),
    inference(forward_demodulation,[],[f2426,f89])).

fof(f89,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl5_1
  <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f2426,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_xboole_0)
    | ~ spl5_36
    | ~ spl5_71 ),
    inference(superposition,[],[f2304,f744])).

fof(f744,plain,
    ( ! [X0] : k1_xboole_0 = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | ~ spl5_36 ),
    inference(avatar_component_clause,[],[f743])).

fof(f743,plain,
    ( spl5_36
  <=> ! [X0] : k1_xboole_0 = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f2304,plain,
    ( ! [X17,X16] : k5_xboole_0(k1_xboole_0,X17) = k5_xboole_0(k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X16),k5_xboole_0(k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X16),X17))
    | ~ spl5_71 ),
    inference(avatar_component_clause,[],[f2303])).

fof(f2303,plain,
    ( spl5_71
  <=> ! [X16,X17] : k5_xboole_0(k1_xboole_0,X17) = k5_xboole_0(k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X16),k5_xboole_0(k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X16),X17)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_71])])).

fof(f2530,plain,
    ( ~ sP0(k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | ~ spl5_5
    | ~ spl5_18
    | ~ spl5_30
    | ~ spl5_57
    | ~ spl5_71
    | spl5_74 ),
    inference(forward_demodulation,[],[f2529,f2304])).

fof(f2529,plain,
    ( ~ sP0(k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | ~ spl5_5
    | ~ spl5_18
    | ~ spl5_30
    | ~ spl5_57
    | spl5_74 ),
    inference(forward_demodulation,[],[f2528,f105])).

fof(f105,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl5_5
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f2528,plain,
    ( ~ sP0(k3_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | ~ spl5_18
    | ~ spl5_30
    | ~ spl5_57
    | spl5_74 ),
    inference(forward_demodulation,[],[f2527,f652])).

fof(f652,plain,
    ( ! [X21,X19,X20] : k3_xboole_0(k5_xboole_0(k6_enumset1(X19,X19,X19,X19,X19,X19,X19,X19),X21),k6_enumset1(X19,X19,X19,X19,X19,X19,X19,X20)) = k5_xboole_0(k6_enumset1(X19,X19,X19,X19,X19,X19,X19,X19),k3_xboole_0(k6_enumset1(X19,X19,X19,X19,X19,X19,X19,X20),X21))
    | ~ spl5_18
    | ~ spl5_30 ),
    inference(superposition,[],[f188,f599])).

fof(f599,plain,
    ( ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f598])).

fof(f598,plain,
    ( spl5_30
  <=> ! [X1,X0] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f188,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(k5_xboole_0(X2,X0),X1) = k5_xboole_0(k3_xboole_0(X2,X1),k3_xboole_0(X1,X0))
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl5_18
  <=> ! [X1,X0,X2] : k3_xboole_0(k5_xboole_0(X2,X0),X1) = k5_xboole_0(k3_xboole_0(X2,X1),k3_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f2527,plain,
    ( ~ sP0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | ~ spl5_57
    | spl5_74 ),
    inference(forward_demodulation,[],[f2525,f1806])).

fof(f1806,plain,
    ( sK2 = sK3
    | ~ spl5_57 ),
    inference(avatar_component_clause,[],[f1805])).

fof(f1805,plain,
    ( spl5_57
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_57])])).

fof(f2525,plain,
    ( ~ sP0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
    | spl5_74 ),
    inference(avatar_component_clause,[],[f2524])).

fof(f2524,plain,
    ( spl5_74
  <=> sP0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_74])])).

fof(f2526,plain,
    ( ~ spl5_74
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_12
    | ~ spl5_19
    | ~ spl5_30
    | spl5_42 ),
    inference(avatar_split_clause,[],[f1069,f1033,f598,f191,f155,f122,f108,f104,f2524])).

fof(f108,plain,
    ( spl5_6
  <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f122,plain,
    ( spl5_8
  <=> ! [X1,X0,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f155,plain,
    ( spl5_12
  <=> ! [X1,X3,X0,X2] :
        ( X0 = X1
        | X0 = X2
        | X0 = X3
        | ~ sP0(X0,X1,X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f191,plain,
    ( spl5_19
  <=> ! [X1,X0] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f1033,plain,
    ( spl5_42
  <=> k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k3_tarski(k6_enumset1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f1069,plain,
    ( ~ sP0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_12
    | ~ spl5_19
    | ~ spl5_30
    | spl5_42 ),
    inference(forward_demodulation,[],[f1068,f105])).

fof(f1068,plain,
    ( ~ sP0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_12
    | ~ spl5_19
    | ~ spl5_30
    | spl5_42 ),
    inference(forward_demodulation,[],[f1067,f647])).

fof(f647,plain,
    ( ! [X6,X4,X5] : k3_xboole_0(k5_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X4),X6),k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)) = k5_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X4),k3_xboole_0(X6,k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)))
    | ~ spl5_8
    | ~ spl5_30 ),
    inference(superposition,[],[f123,f599])).

fof(f123,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f122])).

fof(f1067,plain,
    ( ~ sP0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
    | ~ spl5_6
    | ~ spl5_12
    | ~ spl5_19
    | spl5_42 ),
    inference(forward_demodulation,[],[f1066,f109])).

fof(f109,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f108])).

fof(f1066,plain,
    ( ~ sP0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
    | ~ spl5_12
    | ~ spl5_19
    | spl5_42 ),
    inference(forward_demodulation,[],[f1062,f192])).

fof(f192,plain,
    ( ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f191])).

fof(f1062,plain,
    ( ~ sP0(k3_tarski(k6_enumset1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
    | ~ spl5_12
    | spl5_42 ),
    inference(unit_resulting_resolution,[],[f1034,f1034,f1034,f156])).

fof(f156,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ sP0(X0,X1,X2,X3)
        | X0 = X2
        | X0 = X3
        | X0 = X1 )
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f155])).

fof(f1034,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) != k3_tarski(k6_enumset1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))
    | spl5_42 ),
    inference(avatar_component_clause,[],[f1033])).

fof(f2305,plain,
    ( spl5_71
    | ~ spl5_6
    | ~ spl5_36 ),
    inference(avatar_split_clause,[],[f763,f743,f108,f2303])).

fof(f763,plain,
    ( ! [X17,X16] : k5_xboole_0(k1_xboole_0,X17) = k5_xboole_0(k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X16),k5_xboole_0(k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X16),X17))
    | ~ spl5_6
    | ~ spl5_36 ),
    inference(superposition,[],[f109,f744])).

fof(f1817,plain,
    ( spl5_57
    | ~ spl5_11
    | ~ spl5_40
    | spl5_58 ),
    inference(avatar_split_clause,[],[f1812,f1808,f822,f141,f1805])).

fof(f141,plain,
    ( spl5_11
  <=> ! [X1,X0,X2] : sP1(X0,X1,X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f822,plain,
    ( spl5_40
  <=> ! [X1,X0] :
        ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
        | X0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f1808,plain,
    ( spl5_58
  <=> sP1(sK2,sK2,sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_58])])).

fof(f1812,plain,
    ( sK2 = sK3
    | ~ spl5_11
    | ~ spl5_40
    | spl5_58 ),
    inference(subsumption_resolution,[],[f1811,f142])).

fof(f142,plain,
    ( ! [X2,X0,X1] : sP1(X0,X1,X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f141])).

fof(f1811,plain,
    ( ~ sP1(sK2,sK2,sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))
    | sK2 = sK3
    | ~ spl5_40
    | spl5_58 ),
    inference(superposition,[],[f1809,f823])).

fof(f823,plain,
    ( ! [X0,X1] :
        ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
        | X0 = X1 )
    | ~ spl5_40 ),
    inference(avatar_component_clause,[],[f822])).

fof(f1809,plain,
    ( ~ sP1(sK2,sK2,sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))
    | spl5_58 ),
    inference(avatar_component_clause,[],[f1808])).

fof(f1810,plain,
    ( spl5_57
    | ~ spl5_58
    | ~ spl5_30
    | ~ spl5_40
    | spl5_54 ),
    inference(avatar_split_clause,[],[f1803,f1791,f822,f598,f1808,f1805])).

fof(f1791,plain,
    ( spl5_54
  <=> sP1(sK2,sK2,sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).

fof(f1803,plain,
    ( ~ sP1(sK2,sK2,sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))
    | sK2 = sK3
    | ~ spl5_30
    | ~ spl5_40
    | spl5_54 ),
    inference(forward_demodulation,[],[f1802,f599])).

fof(f1802,plain,
    ( ~ sP1(sK2,sK2,sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2))))
    | sK2 = sK3
    | ~ spl5_40
    | spl5_54 ),
    inference(superposition,[],[f1792,f823])).

fof(f1792,plain,
    ( ~ sP1(sK2,sK2,sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))
    | spl5_54 ),
    inference(avatar_component_clause,[],[f1791])).

fof(f1793,plain,
    ( ~ spl5_54
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_16
    | ~ spl5_19
    | ~ spl5_30
    | spl5_42 ),
    inference(avatar_split_clause,[],[f1101,f1033,f598,f191,f175,f122,f108,f104,f1791])).

fof(f175,plain,
    ( spl5_16
  <=> ! [X1,X3,X0,X2] :
        ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = X3
        | ~ sP1(X0,X1,X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f1101,plain,
    ( ~ sP1(sK2,sK2,sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_16
    | ~ spl5_19
    | ~ spl5_30
    | spl5_42 ),
    inference(forward_demodulation,[],[f1100,f105])).

fof(f1100,plain,
    ( ~ sP1(sK2,sK2,sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_16
    | ~ spl5_19
    | ~ spl5_30
    | spl5_42 ),
    inference(forward_demodulation,[],[f1099,f647])).

fof(f1099,plain,
    ( ~ sP1(sK2,sK2,sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))))
    | ~ spl5_6
    | ~ spl5_16
    | ~ spl5_19
    | spl5_42 ),
    inference(forward_demodulation,[],[f1098,f109])).

fof(f1098,plain,
    ( ~ sP1(sK2,sK2,sK3,k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))
    | ~ spl5_16
    | ~ spl5_19
    | spl5_42 ),
    inference(forward_demodulation,[],[f1044,f192])).

fof(f1044,plain,
    ( ~ sP1(sK2,sK2,sK3,k3_tarski(k6_enumset1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))
    | ~ spl5_16
    | spl5_42 ),
    inference(unit_resulting_resolution,[],[f1034,f176])).

fof(f176,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ sP1(X0,X1,X2,X3)
        | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = X3 )
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f175])).

fof(f1035,plain,(
    ~ spl5_42 ),
    inference(avatar_split_clause,[],[f75,f1033])).

fof(f75,plain,(
    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) != k3_tarski(k6_enumset1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) ),
    inference(definition_unfolding,[],[f39,f72,f72,f74,f74])).

fof(f74,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f41,f72])).

fof(f41,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f72,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f45,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f51,f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f54,f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f65,f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f66,f67])).

fof(f67,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f51,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f45,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f39,plain,(
    k2_tarski(sK2,sK3) != k3_tarski(k2_tarski(k1_tarski(sK2),k1_tarski(sK3))) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    k2_tarski(sK2,sK3) != k3_tarski(k2_tarski(k1_tarski(sK2),k1_tarski(sK3))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f22,f29])).

fof(f29,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))
   => k2_tarski(sK2,sK3) != k3_tarski(k2_tarski(k1_tarski(sK2),k1_tarski(sK3))) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_zfmisc_1)).

fof(f824,plain,(
    spl5_40 ),
    inference(avatar_split_clause,[],[f79,f822])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f49,f72,f74,f74])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_zfmisc_1)).

fof(f745,plain,
    ( spl5_36
    | ~ spl5_30
    | ~ spl5_33 ),
    inference(avatar_split_clause,[],[f733,f730,f598,f743])).

fof(f730,plain,
    ( spl5_33
  <=> ! [X1,X0] : k1_xboole_0 = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f733,plain,
    ( ! [X0] : k1_xboole_0 = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | ~ spl5_30
    | ~ spl5_33 ),
    inference(forward_demodulation,[],[f731,f599])).

fof(f731,plain,
    ( ! [X0,X1] : k1_xboole_0 = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
    | ~ spl5_33 ),
    inference(avatar_component_clause,[],[f730])).

fof(f732,plain,(
    spl5_33 ),
    inference(avatar_split_clause,[],[f76,f730])).

fof(f76,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f43,f47,f74,f72])).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f43,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_zfmisc_1)).

fof(f600,plain,(
    spl5_30 ),
    inference(avatar_split_clause,[],[f77,f598])).

fof(f77,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f46,f74,f74,f72])).

fof(f46,plain,(
    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_zfmisc_1)).

fof(f496,plain,(
    spl5_27 ),
    inference(avatar_split_clause,[],[f80,f494])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f50,f74,f74])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

fof(f193,plain,(
    spl5_19 ),
    inference(avatar_split_clause,[],[f78,f191])).

fof(f78,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f48,f73])).

fof(f73,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f44,f72])).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f189,plain,
    ( spl5_18
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f146,f122,f104,f187])).

fof(f146,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(k5_xboole_0(X2,X0),X1) = k5_xboole_0(k3_xboole_0(X2,X1),k3_xboole_0(X1,X0))
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(superposition,[],[f123,f105])).

fof(f177,plain,(
    spl5_16 ),
    inference(avatar_split_clause,[],[f81,f175])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = X3
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(definition_unfolding,[],[f64,f71])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP1(X0,X1,X2,X3) )
      & ( sP1(X0,X1,X2,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP1(X0,X1,X2,X3) ) ),
    inference(definition_folding,[],[f25,f27,f26])).

fof(f26,plain,(
    ! [X4,X2,X1,X0] :
      ( sP0(X4,X2,X1,X0)
    <=> ( X2 = X4
        | X1 = X4
        | X0 = X4 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( sP1(X0,X1,X2,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> sP0(X4,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f172,plain,
    ( spl5_15
    | ~ spl5_4
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f151,f141,f137,f100,f170])).

fof(f100,plain,
    ( spl5_4
  <=> ! [X1,X3,X2] : sP0(X3,X1,X2,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f137,plain,
    ( spl5_10
  <=> ! [X1,X3,X5,X0,X2] :
        ( r2_hidden(X5,X3)
        | ~ sP0(X5,X2,X1,X0)
        | ~ sP1(X0,X1,X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f151,plain,
    ( ! [X2,X0,X1] : r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))
    | ~ spl5_4
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f101,f142,f138])).

fof(f138,plain,
    ( ! [X2,X0,X5,X3,X1] :
        ( ~ sP1(X0,X1,X2,X3)
        | ~ sP0(X5,X2,X1,X0)
        | r2_hidden(X5,X3) )
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f137])).

fof(f101,plain,
    ( ! [X2,X3,X1] : sP0(X3,X1,X2,X3)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f100])).

fof(f157,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f59,f155])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X1
      | X0 = X2
      | X0 = X3
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X4,X2,X1,X0] :
      ( ( sP0(X4,X2,X1,X0)
        | ( X2 != X4
          & X1 != X4
          & X0 != X4 ) )
      & ( X2 = X4
        | X1 = X4
        | X0 = X4
        | ~ sP0(X4,X2,X1,X0) ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X4,X2,X1,X0] :
      ( ( sP0(X4,X2,X1,X0)
        | ( X2 != X4
          & X1 != X4
          & X0 != X4 ) )
      & ( X2 = X4
        | X1 = X4
        | X0 = X4
        | ~ sP0(X4,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f143,plain,(
    spl5_11 ),
    inference(avatar_split_clause,[],[f86,f141])).

fof(f86,plain,(
    ! [X2,X0,X1] : sP1(X0,X1,X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X0,X1,X2,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f63,f71])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X0,X1,X2,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f139,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f56,f137])).

fof(f56,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | ~ sP0(X5,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ( ( ~ sP0(sK4(X0,X1,X2,X3),X2,X1,X0)
            | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
          & ( sP0(sK4(X0,X1,X2,X3),X2,X1,X0)
            | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ~ sP0(X5,X2,X1,X0) )
            & ( sP0(X5,X2,X1,X0)
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f33])).

fof(f33,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ~ sP0(X4,X2,X1,X0)
            | ~ r2_hidden(X4,X3) )
          & ( sP0(X4,X2,X1,X0)
            | r2_hidden(X4,X3) ) )
     => ( ( ~ sP0(sK4(X0,X1,X2,X3),X2,X1,X0)
          | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
        & ( sP0(sK4(X0,X1,X2,X3),X2,X1,X0)
          | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ~ sP0(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) )
            & ( sP0(X4,X2,X1,X0)
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ~ sP0(X5,X2,X1,X0) )
            & ( sP0(X5,X2,X1,X0)
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ~ sP0(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) )
            & ( sP0(X4,X2,X1,X0)
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ~ sP0(X4,X2,X1,X0) )
            & ( sP0(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f124,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f53,f122])).

fof(f53,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f110,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f52,f108])).

fof(f52,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f106,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f42,f104])).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f102,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f85,f100])).

fof(f85,plain,(
    ! [X2,X3,X1] : sP0(X3,X1,X2,X3) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | X0 != X3 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f94,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f83,f92])).

fof(f83,plain,(
    ! [X2,X3,X1] : sP0(X1,X1,X2,X3) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f90,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f40,f88])).

fof(f40,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:02:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (26123)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.50  % (26132)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.51  % (26124)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.51  % (26120)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (26119)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (26116)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (26128)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (26141)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.51  % (26138)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.51  % (26117)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (26129)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.51  % (26116)Refutation not found, incomplete strategy% (26116)------------------------------
% 0.20/0.51  % (26116)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (26116)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (26116)Memory used [KB]: 1663
% 0.20/0.51  % (26116)Time elapsed: 0.093 s
% 0.20/0.51  % (26116)------------------------------
% 0.20/0.51  % (26116)------------------------------
% 0.20/0.51  % (26131)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  % (26124)Refutation not found, incomplete strategy% (26124)------------------------------
% 0.20/0.51  % (26124)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (26139)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.51  % (26130)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.51  % (26139)Refutation not found, incomplete strategy% (26139)------------------------------
% 0.20/0.51  % (26139)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (26131)Refutation not found, incomplete strategy% (26131)------------------------------
% 0.20/0.52  % (26131)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (26139)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (26139)Memory used [KB]: 1663
% 0.20/0.52  % (26139)Time elapsed: 0.114 s
% 0.20/0.52  % (26139)------------------------------
% 0.20/0.52  % (26139)------------------------------
% 0.20/0.52  % (26131)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (26131)Memory used [KB]: 6140
% 0.20/0.52  % (26131)Time elapsed: 0.115 s
% 0.20/0.52  % (26131)------------------------------
% 0.20/0.52  % (26131)------------------------------
% 0.20/0.52  % (26122)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (26124)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (26124)Memory used [KB]: 10746
% 0.20/0.52  % (26124)Time elapsed: 0.119 s
% 0.20/0.52  % (26124)------------------------------
% 0.20/0.52  % (26124)------------------------------
% 0.20/0.52  % (26145)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.53  % (26118)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (26118)Refutation not found, incomplete strategy% (26118)------------------------------
% 0.20/0.53  % (26118)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (26118)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (26118)Memory used [KB]: 10746
% 0.20/0.53  % (26118)Time elapsed: 0.125 s
% 0.20/0.53  % (26118)------------------------------
% 0.20/0.53  % (26118)------------------------------
% 0.20/0.53  % (26136)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.53  % (26142)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.53  % (26144)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.53  % (26136)Refutation not found, incomplete strategy% (26136)------------------------------
% 0.20/0.53  % (26136)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (26136)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (26136)Memory used [KB]: 10746
% 0.20/0.53  % (26136)Time elapsed: 0.134 s
% 0.20/0.53  % (26136)------------------------------
% 0.20/0.53  % (26136)------------------------------
% 0.20/0.53  % (26134)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.53  % (26121)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (26133)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.53  % (26133)Refutation not found, incomplete strategy% (26133)------------------------------
% 0.20/0.53  % (26133)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (26133)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (26133)Memory used [KB]: 10618
% 0.20/0.53  % (26133)Time elapsed: 0.138 s
% 0.20/0.53  % (26133)------------------------------
% 0.20/0.53  % (26133)------------------------------
% 0.20/0.54  % (26143)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.54  % (26135)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (26125)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.54  % (26126)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.54  % (26126)Refutation not found, incomplete strategy% (26126)------------------------------
% 0.20/0.54  % (26126)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (26126)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (26126)Memory used [KB]: 10618
% 0.20/0.54  % (26126)Time elapsed: 0.149 s
% 0.20/0.54  % (26126)------------------------------
% 0.20/0.54  % (26126)------------------------------
% 0.20/0.54  % (26140)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  % (26127)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.55  % (26127)Refutation not found, incomplete strategy% (26127)------------------------------
% 0.20/0.55  % (26127)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (26127)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (26127)Memory used [KB]: 10618
% 0.20/0.55  % (26127)Time elapsed: 0.149 s
% 0.20/0.55  % (26127)------------------------------
% 0.20/0.55  % (26127)------------------------------
% 0.20/0.55  % (26137)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.55  % (26137)Refutation not found, incomplete strategy% (26137)------------------------------
% 0.20/0.55  % (26137)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (26137)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (26137)Memory used [KB]: 1791
% 0.20/0.55  % (26137)Time elapsed: 0.162 s
% 0.20/0.55  % (26137)------------------------------
% 0.20/0.55  % (26137)------------------------------
% 2.14/0.64  % (26148)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.14/0.65  % (26146)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.14/0.65  % (26147)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.14/0.66  % (26150)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.14/0.67  % (26149)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.14/0.67  % (26151)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.14/0.67  % (26146)Refutation not found, incomplete strategy% (26146)------------------------------
% 2.14/0.67  % (26146)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.14/0.67  % (26146)Termination reason: Refutation not found, incomplete strategy
% 2.14/0.67  
% 2.14/0.67  % (26146)Memory used [KB]: 6140
% 2.14/0.67  % (26146)Time elapsed: 0.130 s
% 2.14/0.67  % (26146)------------------------------
% 2.14/0.67  % (26146)------------------------------
% 2.14/0.68  % (26152)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.14/0.68  % (26153)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 2.14/0.69  % (26154)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 2.14/0.69  % (26155)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 3.31/0.81  % (26121)Time limit reached!
% 3.31/0.81  % (26121)------------------------------
% 3.31/0.81  % (26121)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.31/0.81  % (26121)Termination reason: Time limit
% 3.31/0.81  
% 3.31/0.81  % (26121)Memory used [KB]: 9083
% 3.31/0.81  % (26121)Time elapsed: 0.408 s
% 3.31/0.81  % (26121)------------------------------
% 3.31/0.81  % (26121)------------------------------
% 3.31/0.83  % (26156)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 4.12/0.91  % (26117)Time limit reached!
% 4.12/0.91  % (26117)------------------------------
% 4.12/0.91  % (26117)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.12/0.91  % (26117)Termination reason: Time limit
% 4.12/0.91  
% 4.12/0.91  % (26117)Memory used [KB]: 9210
% 4.12/0.91  % (26117)Time elapsed: 0.508 s
% 4.12/0.91  % (26117)------------------------------
% 4.12/0.91  % (26117)------------------------------
% 4.39/0.92  % (26128)Time limit reached!
% 4.39/0.92  % (26128)------------------------------
% 4.39/0.92  % (26128)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.39/0.92  % (26128)Termination reason: Time limit
% 4.39/0.92  % (26128)Termination phase: Saturation
% 4.39/0.92  
% 4.39/0.92  % (26128)Memory used [KB]: 9722
% 4.39/0.92  % (26128)Time elapsed: 0.529 s
% 4.39/0.92  % (26128)------------------------------
% 4.39/0.92  % (26128)------------------------------
% 4.39/0.95  % (26157)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 4.39/0.97  % (26149)Time limit reached!
% 4.39/0.97  % (26149)------------------------------
% 4.39/0.97  % (26149)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.39/0.97  % (26149)Termination reason: Time limit
% 4.39/0.97  
% 4.39/0.97  % (26149)Memory used [KB]: 8059
% 4.39/0.97  % (26149)Time elapsed: 0.420 s
% 4.39/0.97  % (26149)------------------------------
% 4.39/0.97  % (26149)------------------------------
% 4.39/0.98  % (26150)Time limit reached!
% 4.39/0.98  % (26150)------------------------------
% 4.39/0.98  % (26150)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.39/0.98  % (26150)Termination reason: Time limit
% 4.39/0.98  
% 4.39/0.98  % (26150)Memory used [KB]: 15095
% 4.39/0.98  % (26150)Time elapsed: 0.424 s
% 4.39/0.98  % (26150)------------------------------
% 4.39/0.98  % (26150)------------------------------
% 4.39/1.00  % (26123)Time limit reached!
% 4.39/1.00  % (26123)------------------------------
% 4.39/1.00  % (26123)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.39/1.00  % (26123)Termination reason: Time limit
% 4.39/1.00  % (26123)Termination phase: Saturation
% 4.39/1.00  
% 4.39/1.00  % (26123)Memory used [KB]: 13816
% 4.39/1.00  % (26123)Time elapsed: 0.600 s
% 4.39/1.00  % (26123)------------------------------
% 4.39/1.00  % (26123)------------------------------
% 4.96/1.01  % (26132)Time limit reached!
% 4.96/1.01  % (26132)------------------------------
% 4.96/1.01  % (26132)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.96/1.01  % (26132)Termination reason: Time limit
% 4.96/1.01  % (26132)Termination phase: Saturation
% 4.96/1.01  
% 4.96/1.01  % (26132)Memory used [KB]: 16758
% 4.96/1.01  % (26132)Time elapsed: 0.600 s
% 4.96/1.01  % (26132)------------------------------
% 4.96/1.01  % (26132)------------------------------
% 4.96/1.04  % (26158)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 4.96/1.07  % (26159)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 4.96/1.07  % (26159)Refutation not found, incomplete strategy% (26159)------------------------------
% 4.96/1.07  % (26159)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.96/1.07  % (26159)Termination reason: Refutation not found, incomplete strategy
% 4.96/1.07  
% 4.96/1.07  % (26159)Memory used [KB]: 1663
% 4.96/1.07  % (26159)Time elapsed: 0.121 s
% 4.96/1.07  % (26159)------------------------------
% 4.96/1.07  % (26159)------------------------------
% 5.44/1.08  % (26144)Time limit reached!
% 5.44/1.08  % (26144)------------------------------
% 5.44/1.08  % (26144)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.44/1.08  % (26144)Termination reason: Time limit
% 5.44/1.08  
% 5.44/1.08  % (26144)Memory used [KB]: 9083
% 5.44/1.08  % (26144)Time elapsed: 0.680 s
% 5.44/1.08  % (26144)------------------------------
% 5.44/1.08  % (26144)------------------------------
% 5.44/1.09  % (26160)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 5.44/1.11  % (26161)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 5.44/1.12  % (26162)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 5.44/1.14  % (26163)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 6.70/1.21  % (26164)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 6.70/1.22  % (26165)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 6.89/1.28  % (26160)Refutation found. Thanks to Tanya!
% 6.89/1.28  % SZS status Theorem for theBenchmark
% 6.89/1.28  % SZS output start Proof for theBenchmark
% 6.89/1.28  fof(f2535,plain,(
% 6.89/1.28    $false),
% 6.89/1.28    inference(avatar_sat_refutation,[],[f90,f94,f102,f106,f110,f124,f139,f143,f157,f172,f177,f189,f193,f496,f600,f732,f745,f824,f1035,f1793,f1810,f1817,f2305,f2526,f2534])).
% 6.89/1.28  fof(f2534,plain,(
% 6.89/1.28    ~spl5_1 | ~spl5_2 | ~spl5_5 | ~spl5_15 | ~spl5_18 | ~spl5_27 | ~spl5_30 | ~spl5_36 | ~spl5_57 | ~spl5_71 | spl5_74),
% 6.89/1.28    inference(avatar_contradiction_clause,[],[f2533])).
% 6.89/1.28  fof(f2533,plain,(
% 6.89/1.28    $false | (~spl5_1 | ~spl5_2 | ~spl5_5 | ~spl5_15 | ~spl5_18 | ~spl5_27 | ~spl5_30 | ~spl5_36 | ~spl5_57 | ~spl5_71 | spl5_74)),
% 6.89/1.28    inference(subsumption_resolution,[],[f2532,f93])).
% 6.89/1.28  fof(f93,plain,(
% 6.89/1.28    ( ! [X2,X3,X1] : (sP0(X1,X1,X2,X3)) ) | ~spl5_2),
% 6.89/1.28    inference(avatar_component_clause,[],[f92])).
% 6.89/1.28  fof(f92,plain,(
% 6.89/1.28    spl5_2 <=> ! [X1,X3,X2] : sP0(X1,X1,X2,X3)),
% 6.89/1.28    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 6.89/1.28  fof(f2532,plain,(
% 6.89/1.28    ~sP0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | (~spl5_1 | ~spl5_5 | ~spl5_15 | ~spl5_18 | ~spl5_27 | ~spl5_30 | ~spl5_36 | ~spl5_57 | ~spl5_71 | spl5_74)),
% 6.89/1.28    inference(forward_demodulation,[],[f2531,f538])).
% 6.89/1.28  fof(f538,plain,(
% 6.89/1.28    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) ) | (~spl5_15 | ~spl5_27)),
% 6.89/1.28    inference(unit_resulting_resolution,[],[f171,f495])).
% 6.89/1.28  fof(f495,plain,(
% 6.89/1.28    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) ) | ~spl5_27),
% 6.89/1.28    inference(avatar_component_clause,[],[f494])).
% 6.89/1.28  fof(f494,plain,(
% 6.89/1.28    spl5_27 <=> ! [X1,X0] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) | ~r2_hidden(X0,X1))),
% 6.89/1.28    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 6.89/1.28  fof(f171,plain,(
% 6.89/1.28    ( ! [X2,X0,X1] : (r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))) ) | ~spl5_15),
% 6.89/1.28    inference(avatar_component_clause,[],[f170])).
% 6.89/1.28  fof(f170,plain,(
% 6.89/1.28    spl5_15 <=> ! [X1,X0,X2] : r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))),
% 6.89/1.28    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 6.89/1.28  fof(f2531,plain,(
% 6.89/1.28    ~sP0(k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | (~spl5_1 | ~spl5_5 | ~spl5_18 | ~spl5_30 | ~spl5_36 | ~spl5_57 | ~spl5_71 | spl5_74)),
% 6.89/1.28    inference(forward_demodulation,[],[f2530,f2444])).
% 6.89/1.28  fof(f2444,plain,(
% 6.89/1.28    ( ! [X0] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k5_xboole_0(k1_xboole_0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) ) | (~spl5_1 | ~spl5_36 | ~spl5_71)),
% 6.89/1.28    inference(forward_demodulation,[],[f2426,f89])).
% 6.89/1.28  fof(f89,plain,(
% 6.89/1.28    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl5_1),
% 6.89/1.28    inference(avatar_component_clause,[],[f88])).
% 6.89/1.28  fof(f88,plain,(
% 6.89/1.28    spl5_1 <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 6.89/1.28    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 6.89/1.28  fof(f2426,plain,(
% 6.89/1.28    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_xboole_0)) ) | (~spl5_36 | ~spl5_71)),
% 6.89/1.28    inference(superposition,[],[f2304,f744])).
% 6.89/1.28  fof(f744,plain,(
% 6.89/1.28    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) ) | ~spl5_36),
% 6.89/1.28    inference(avatar_component_clause,[],[f743])).
% 6.89/1.28  fof(f743,plain,(
% 6.89/1.28    spl5_36 <=> ! [X0] : k1_xboole_0 = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))),
% 6.89/1.28    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).
% 6.89/1.28  fof(f2304,plain,(
% 6.89/1.28    ( ! [X17,X16] : (k5_xboole_0(k1_xboole_0,X17) = k5_xboole_0(k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X16),k5_xboole_0(k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X16),X17))) ) | ~spl5_71),
% 6.89/1.28    inference(avatar_component_clause,[],[f2303])).
% 6.89/1.28  fof(f2303,plain,(
% 6.89/1.28    spl5_71 <=> ! [X16,X17] : k5_xboole_0(k1_xboole_0,X17) = k5_xboole_0(k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X16),k5_xboole_0(k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X16),X17))),
% 6.89/1.28    introduced(avatar_definition,[new_symbols(naming,[spl5_71])])).
% 6.89/1.28  fof(f2530,plain,(
% 6.89/1.28    ~sP0(k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k1_xboole_0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | (~spl5_5 | ~spl5_18 | ~spl5_30 | ~spl5_57 | ~spl5_71 | spl5_74)),
% 6.89/1.28    inference(forward_demodulation,[],[f2529,f2304])).
% 6.89/1.28  fof(f2529,plain,(
% 6.89/1.28    ~sP0(k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | (~spl5_5 | ~spl5_18 | ~spl5_30 | ~spl5_57 | spl5_74)),
% 6.89/1.28    inference(forward_demodulation,[],[f2528,f105])).
% 6.89/1.28  fof(f105,plain,(
% 6.89/1.28    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl5_5),
% 6.89/1.28    inference(avatar_component_clause,[],[f104])).
% 6.89/1.28  fof(f104,plain,(
% 6.89/1.28    spl5_5 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 6.89/1.28    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 6.89/1.28  fof(f2528,plain,(
% 6.89/1.28    ~sP0(k3_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | (~spl5_18 | ~spl5_30 | ~spl5_57 | spl5_74)),
% 6.89/1.28    inference(forward_demodulation,[],[f2527,f652])).
% 6.89/1.28  fof(f652,plain,(
% 6.89/1.28    ( ! [X21,X19,X20] : (k3_xboole_0(k5_xboole_0(k6_enumset1(X19,X19,X19,X19,X19,X19,X19,X19),X21),k6_enumset1(X19,X19,X19,X19,X19,X19,X19,X20)) = k5_xboole_0(k6_enumset1(X19,X19,X19,X19,X19,X19,X19,X19),k3_xboole_0(k6_enumset1(X19,X19,X19,X19,X19,X19,X19,X20),X21))) ) | (~spl5_18 | ~spl5_30)),
% 6.89/1.28    inference(superposition,[],[f188,f599])).
% 6.89/1.28  fof(f599,plain,(
% 6.89/1.28    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ) | ~spl5_30),
% 6.89/1.28    inference(avatar_component_clause,[],[f598])).
% 6.89/1.28  fof(f598,plain,(
% 6.89/1.28    spl5_30 <=> ! [X1,X0] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),
% 6.89/1.28    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 6.89/1.28  fof(f188,plain,(
% 6.89/1.28    ( ! [X2,X0,X1] : (k3_xboole_0(k5_xboole_0(X2,X0),X1) = k5_xboole_0(k3_xboole_0(X2,X1),k3_xboole_0(X1,X0))) ) | ~spl5_18),
% 6.89/1.28    inference(avatar_component_clause,[],[f187])).
% 6.89/1.28  fof(f187,plain,(
% 6.89/1.28    spl5_18 <=> ! [X1,X0,X2] : k3_xboole_0(k5_xboole_0(X2,X0),X1) = k5_xboole_0(k3_xboole_0(X2,X1),k3_xboole_0(X1,X0))),
% 6.89/1.28    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 6.89/1.28  fof(f2527,plain,(
% 6.89/1.28    ~sP0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | (~spl5_57 | spl5_74)),
% 6.89/1.28    inference(forward_demodulation,[],[f2525,f1806])).
% 6.89/1.28  fof(f1806,plain,(
% 6.89/1.28    sK2 = sK3 | ~spl5_57),
% 6.89/1.28    inference(avatar_component_clause,[],[f1805])).
% 6.89/1.28  fof(f1805,plain,(
% 6.89/1.28    spl5_57 <=> sK2 = sK3),
% 6.89/1.28    introduced(avatar_definition,[new_symbols(naming,[spl5_57])])).
% 6.89/1.28  fof(f2525,plain,(
% 6.89/1.28    ~sP0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) | spl5_74),
% 6.89/1.28    inference(avatar_component_clause,[],[f2524])).
% 6.89/1.28  fof(f2524,plain,(
% 6.89/1.28    spl5_74 <=> sP0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3))),
% 6.89/1.28    introduced(avatar_definition,[new_symbols(naming,[spl5_74])])).
% 6.89/1.28  fof(f2526,plain,(
% 6.89/1.28    ~spl5_74 | ~spl5_5 | ~spl5_6 | ~spl5_8 | ~spl5_12 | ~spl5_19 | ~spl5_30 | spl5_42),
% 6.89/1.28    inference(avatar_split_clause,[],[f1069,f1033,f598,f191,f155,f122,f108,f104,f2524])).
% 6.89/1.28  fof(f108,plain,(
% 6.89/1.28    spl5_6 <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 6.89/1.28    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 6.89/1.28  fof(f122,plain,(
% 6.89/1.28    spl5_8 <=> ! [X1,X0,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 6.89/1.28    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 6.89/1.28  fof(f155,plain,(
% 6.89/1.28    spl5_12 <=> ! [X1,X3,X0,X2] : (X0 = X1 | X0 = X2 | X0 = X3 | ~sP0(X0,X1,X2,X3))),
% 6.89/1.28    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 6.89/1.28  fof(f191,plain,(
% 6.89/1.28    spl5_19 <=> ! [X1,X0] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),
% 6.89/1.28    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 6.89/1.28  fof(f1033,plain,(
% 6.89/1.28    spl5_42 <=> k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) = k3_tarski(k6_enumset1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))),
% 6.89/1.28    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).
% 6.89/1.28  fof(f1069,plain,(
% 6.89/1.28    ~sP0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) | (~spl5_5 | ~spl5_6 | ~spl5_8 | ~spl5_12 | ~spl5_19 | ~spl5_30 | spl5_42)),
% 6.89/1.28    inference(forward_demodulation,[],[f1068,f105])).
% 6.89/1.28  fof(f1068,plain,(
% 6.89/1.28    ~sP0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) | (~spl5_6 | ~spl5_8 | ~spl5_12 | ~spl5_19 | ~spl5_30 | spl5_42)),
% 6.89/1.28    inference(forward_demodulation,[],[f1067,f647])).
% 6.89/1.28  fof(f647,plain,(
% 6.89/1.28    ( ! [X6,X4,X5] : (k3_xboole_0(k5_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X4),X6),k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)) = k5_xboole_0(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X4),k3_xboole_0(X6,k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)))) ) | (~spl5_8 | ~spl5_30)),
% 6.89/1.28    inference(superposition,[],[f123,f599])).
% 6.89/1.28  fof(f123,plain,(
% 6.89/1.28    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) ) | ~spl5_8),
% 6.89/1.28    inference(avatar_component_clause,[],[f122])).
% 6.89/1.28  fof(f1067,plain,(
% 6.89/1.28    ~sP0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) | (~spl5_6 | ~spl5_12 | ~spl5_19 | spl5_42)),
% 6.89/1.28    inference(forward_demodulation,[],[f1066,f109])).
% 6.89/1.28  fof(f109,plain,(
% 6.89/1.28    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) ) | ~spl5_6),
% 6.89/1.28    inference(avatar_component_clause,[],[f108])).
% 6.89/1.28  fof(f1066,plain,(
% 6.89/1.28    ~sP0(k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) | (~spl5_12 | ~spl5_19 | spl5_42)),
% 6.89/1.28    inference(forward_demodulation,[],[f1062,f192])).
% 6.89/1.28  fof(f192,plain,(
% 6.89/1.28    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ) | ~spl5_19),
% 6.89/1.28    inference(avatar_component_clause,[],[f191])).
% 6.89/1.28  fof(f1062,plain,(
% 6.89/1.28    ~sP0(k3_tarski(k6_enumset1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) | (~spl5_12 | spl5_42)),
% 6.89/1.28    inference(unit_resulting_resolution,[],[f1034,f1034,f1034,f156])).
% 6.89/1.28  fof(f156,plain,(
% 6.89/1.28    ( ! [X2,X0,X3,X1] : (~sP0(X0,X1,X2,X3) | X0 = X2 | X0 = X3 | X0 = X1) ) | ~spl5_12),
% 6.89/1.28    inference(avatar_component_clause,[],[f155])).
% 6.89/1.28  fof(f1034,plain,(
% 6.89/1.28    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) != k3_tarski(k6_enumset1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) | spl5_42),
% 6.89/1.28    inference(avatar_component_clause,[],[f1033])).
% 6.89/1.28  fof(f2305,plain,(
% 6.89/1.28    spl5_71 | ~spl5_6 | ~spl5_36),
% 6.89/1.28    inference(avatar_split_clause,[],[f763,f743,f108,f2303])).
% 6.89/1.28  fof(f763,plain,(
% 6.89/1.28    ( ! [X17,X16] : (k5_xboole_0(k1_xboole_0,X17) = k5_xboole_0(k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X16),k5_xboole_0(k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X16),X17))) ) | (~spl5_6 | ~spl5_36)),
% 6.89/1.28    inference(superposition,[],[f109,f744])).
% 6.89/1.28  fof(f1817,plain,(
% 6.89/1.28    spl5_57 | ~spl5_11 | ~spl5_40 | spl5_58),
% 6.89/1.28    inference(avatar_split_clause,[],[f1812,f1808,f822,f141,f1805])).
% 6.89/1.28  fof(f141,plain,(
% 6.89/1.28    spl5_11 <=> ! [X1,X0,X2] : sP1(X0,X1,X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))),
% 6.89/1.28    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 6.89/1.28  fof(f822,plain,(
% 6.89/1.28    spl5_40 <=> ! [X1,X0] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | X0 = X1)),
% 6.89/1.28    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).
% 6.89/1.28  fof(f1808,plain,(
% 6.89/1.28    spl5_58 <=> sP1(sK2,sK2,sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))),
% 6.89/1.28    introduced(avatar_definition,[new_symbols(naming,[spl5_58])])).
% 6.89/1.28  fof(f1812,plain,(
% 6.89/1.28    sK2 = sK3 | (~spl5_11 | ~spl5_40 | spl5_58)),
% 6.89/1.28    inference(subsumption_resolution,[],[f1811,f142])).
% 6.89/1.28  fof(f142,plain,(
% 6.89/1.28    ( ! [X2,X0,X1] : (sP1(X0,X1,X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))) ) | ~spl5_11),
% 6.89/1.28    inference(avatar_component_clause,[],[f141])).
% 6.89/1.28  fof(f1811,plain,(
% 6.89/1.28    ~sP1(sK2,sK2,sK3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3)) | sK2 = sK3 | (~spl5_40 | spl5_58)),
% 6.89/1.28    inference(superposition,[],[f1809,f823])).
% 6.89/1.28  fof(f823,plain,(
% 6.89/1.28    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | X0 = X1) ) | ~spl5_40),
% 6.89/1.28    inference(avatar_component_clause,[],[f822])).
% 6.89/1.28  fof(f1809,plain,(
% 6.89/1.28    ~sP1(sK2,sK2,sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) | spl5_58),
% 6.89/1.28    inference(avatar_component_clause,[],[f1808])).
% 6.89/1.28  fof(f1810,plain,(
% 6.89/1.28    spl5_57 | ~spl5_58 | ~spl5_30 | ~spl5_40 | spl5_54),
% 6.89/1.28    inference(avatar_split_clause,[],[f1803,f1791,f822,f598,f1808,f1805])).
% 6.89/1.28  fof(f1791,plain,(
% 6.89/1.28    spl5_54 <=> sP1(sK2,sK2,sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))),
% 6.89/1.28    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).
% 6.89/1.28  fof(f1803,plain,(
% 6.89/1.28    ~sP1(sK2,sK2,sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))) | sK2 = sK3 | (~spl5_30 | ~spl5_40 | spl5_54)),
% 6.89/1.28    inference(forward_demodulation,[],[f1802,f599])).
% 6.89/1.28  fof(f1802,plain,(
% 6.89/1.28    ~sP1(sK2,sK2,sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2)))) | sK2 = sK3 | (~spl5_40 | spl5_54)),
% 6.89/1.28    inference(superposition,[],[f1792,f823])).
% 6.89/1.28  fof(f1792,plain,(
% 6.89/1.28    ~sP1(sK2,sK2,sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))) | spl5_54),
% 6.89/1.28    inference(avatar_component_clause,[],[f1791])).
% 6.89/1.28  fof(f1793,plain,(
% 6.89/1.28    ~spl5_54 | ~spl5_5 | ~spl5_6 | ~spl5_8 | ~spl5_16 | ~spl5_19 | ~spl5_30 | spl5_42),
% 6.89/1.28    inference(avatar_split_clause,[],[f1101,f1033,f598,f191,f175,f122,f108,f104,f1791])).
% 6.89/1.28  fof(f175,plain,(
% 6.89/1.28    spl5_16 <=> ! [X1,X3,X0,X2] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = X3 | ~sP1(X0,X1,X2,X3))),
% 6.89/1.28    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 6.89/1.28  fof(f1101,plain,(
% 6.89/1.28    ~sP1(sK2,sK2,sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))) | (~spl5_5 | ~spl5_6 | ~spl5_8 | ~spl5_16 | ~spl5_19 | ~spl5_30 | spl5_42)),
% 6.89/1.28    inference(forward_demodulation,[],[f1100,f105])).
% 6.89/1.28  fof(f1100,plain,(
% 6.89/1.28    ~sP1(sK2,sK2,sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) | (~spl5_6 | ~spl5_8 | ~spl5_16 | ~spl5_19 | ~spl5_30 | spl5_42)),
% 6.89/1.28    inference(forward_demodulation,[],[f1099,f647])).
% 6.89/1.28  fof(f1099,plain,(
% 6.89/1.28    ~sP1(sK2,sK2,sK3,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3))))) | (~spl5_6 | ~spl5_16 | ~spl5_19 | spl5_42)),
% 6.89/1.28    inference(forward_demodulation,[],[f1098,f109])).
% 6.89/1.28  fof(f1098,plain,(
% 6.89/1.28    ~sP1(sK2,sK2,sK3,k5_xboole_0(k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) | (~spl5_16 | ~spl5_19 | spl5_42)),
% 6.89/1.28    inference(forward_demodulation,[],[f1044,f192])).
% 6.89/1.28  fof(f1044,plain,(
% 6.89/1.28    ~sP1(sK2,sK2,sK3,k3_tarski(k6_enumset1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))) | (~spl5_16 | spl5_42)),
% 6.89/1.28    inference(unit_resulting_resolution,[],[f1034,f176])).
% 6.89/1.28  fof(f176,plain,(
% 6.89/1.28    ( ! [X2,X0,X3,X1] : (~sP1(X0,X1,X2,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = X3) ) | ~spl5_16),
% 6.89/1.28    inference(avatar_component_clause,[],[f175])).
% 6.89/1.28  fof(f1035,plain,(
% 6.89/1.28    ~spl5_42),
% 6.89/1.28    inference(avatar_split_clause,[],[f75,f1033])).
% 6.89/1.28  fof(f75,plain,(
% 6.89/1.28    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK3) != k3_tarski(k6_enumset1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3)))),
% 6.89/1.28    inference(definition_unfolding,[],[f39,f72,f72,f74,f74])).
% 6.89/1.28  fof(f74,plain,(
% 6.89/1.28    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 6.89/1.28    inference(definition_unfolding,[],[f41,f72])).
% 6.89/1.28  fof(f41,plain,(
% 6.89/1.28    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 6.89/1.28    inference(cnf_transformation,[],[f8])).
% 6.89/1.28  fof(f8,axiom,(
% 6.89/1.28    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 6.89/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 6.89/1.28  fof(f72,plain,(
% 6.89/1.28    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 6.89/1.28    inference(definition_unfolding,[],[f45,f71])).
% 6.89/1.28  fof(f71,plain,(
% 6.89/1.28    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 6.89/1.28    inference(definition_unfolding,[],[f51,f70])).
% 6.89/1.28  fof(f70,plain,(
% 6.89/1.28    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 6.89/1.28    inference(definition_unfolding,[],[f54,f69])).
% 6.89/1.28  fof(f69,plain,(
% 6.89/1.28    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 6.89/1.28    inference(definition_unfolding,[],[f65,f68])).
% 6.89/1.28  fof(f68,plain,(
% 6.89/1.28    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 6.89/1.28    inference(definition_unfolding,[],[f66,f67])).
% 6.89/1.28  fof(f67,plain,(
% 6.89/1.28    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 6.89/1.28    inference(cnf_transformation,[],[f14])).
% 6.89/1.28  fof(f14,axiom,(
% 6.89/1.28    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 6.89/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 6.89/1.28  fof(f66,plain,(
% 6.89/1.28    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 6.89/1.28    inference(cnf_transformation,[],[f13])).
% 6.89/1.28  fof(f13,axiom,(
% 6.89/1.28    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 6.89/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 6.89/1.28  fof(f65,plain,(
% 6.89/1.28    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 6.89/1.28    inference(cnf_transformation,[],[f12])).
% 6.89/1.28  fof(f12,axiom,(
% 6.89/1.28    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 6.89/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 6.89/1.28  fof(f54,plain,(
% 6.89/1.28    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 6.89/1.28    inference(cnf_transformation,[],[f11])).
% 6.89/1.28  fof(f11,axiom,(
% 6.89/1.28    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 6.89/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 6.89/1.28  fof(f51,plain,(
% 6.89/1.28    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 6.89/1.28    inference(cnf_transformation,[],[f10])).
% 6.89/1.28  fof(f10,axiom,(
% 6.89/1.28    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 6.89/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 6.89/1.28  fof(f45,plain,(
% 6.89/1.28    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 6.89/1.28    inference(cnf_transformation,[],[f9])).
% 6.89/1.28  fof(f9,axiom,(
% 6.89/1.28    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 6.89/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 6.89/1.28  fof(f39,plain,(
% 6.89/1.28    k2_tarski(sK2,sK3) != k3_tarski(k2_tarski(k1_tarski(sK2),k1_tarski(sK3)))),
% 6.89/1.28    inference(cnf_transformation,[],[f30])).
% 6.89/1.28  fof(f30,plain,(
% 6.89/1.28    k2_tarski(sK2,sK3) != k3_tarski(k2_tarski(k1_tarski(sK2),k1_tarski(sK3)))),
% 6.89/1.28    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f22,f29])).
% 6.89/1.28  fof(f29,plain,(
% 6.89/1.28    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) => k2_tarski(sK2,sK3) != k3_tarski(k2_tarski(k1_tarski(sK2),k1_tarski(sK3)))),
% 6.89/1.28    introduced(choice_axiom,[])).
% 6.89/1.28  fof(f22,plain,(
% 6.89/1.28    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 6.89/1.28    inference(ennf_transformation,[],[f21])).
% 6.89/1.28  fof(f21,negated_conjecture,(
% 6.89/1.28    ~! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 6.89/1.28    inference(negated_conjecture,[],[f20])).
% 6.89/1.28  fof(f20,conjecture,(
% 6.89/1.28    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 6.89/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_zfmisc_1)).
% 6.89/1.28  fof(f824,plain,(
% 6.89/1.28    spl5_40),
% 6.89/1.28    inference(avatar_split_clause,[],[f79,f822])).
% 6.89/1.28  fof(f79,plain,(
% 6.89/1.28    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | X0 = X1) )),
% 6.89/1.28    inference(definition_unfolding,[],[f49,f72,f74,f74])).
% 6.89/1.28  fof(f49,plain,(
% 6.89/1.28    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 6.89/1.28    inference(cnf_transformation,[],[f23])).
% 6.89/1.28  fof(f23,plain,(
% 6.89/1.28    ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 6.89/1.28    inference(ennf_transformation,[],[f19])).
% 6.89/1.28  fof(f19,axiom,(
% 6.89/1.28    ! [X0,X1] : (X0 != X1 => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 6.89/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_zfmisc_1)).
% 6.89/1.28  fof(f745,plain,(
% 6.89/1.28    spl5_36 | ~spl5_30 | ~spl5_33),
% 6.89/1.28    inference(avatar_split_clause,[],[f733,f730,f598,f743])).
% 6.89/1.28  fof(f730,plain,(
% 6.89/1.28    spl5_33 <=> ! [X1,X0] : k1_xboole_0 = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),
% 6.89/1.28    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 6.89/1.28  fof(f733,plain,(
% 6.89/1.28    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) ) | (~spl5_30 | ~spl5_33)),
% 6.89/1.28    inference(forward_demodulation,[],[f731,f599])).
% 6.89/1.28  fof(f731,plain,(
% 6.89/1.28    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ) | ~spl5_33),
% 6.89/1.28    inference(avatar_component_clause,[],[f730])).
% 6.89/1.28  fof(f732,plain,(
% 6.89/1.28    spl5_33),
% 6.89/1.28    inference(avatar_split_clause,[],[f76,f730])).
% 6.89/1.28  fof(f76,plain,(
% 6.89/1.28    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 6.89/1.28    inference(definition_unfolding,[],[f43,f47,f74,f72])).
% 6.89/1.28  fof(f47,plain,(
% 6.89/1.28    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 6.89/1.28    inference(cnf_transformation,[],[f2])).
% 6.89/1.28  fof(f2,axiom,(
% 6.89/1.28    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 6.89/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 6.89/1.28  fof(f43,plain,(
% 6.89/1.28    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 6.89/1.28    inference(cnf_transformation,[],[f18])).
% 6.89/1.28  fof(f18,axiom,(
% 6.89/1.28    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 6.89/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_zfmisc_1)).
% 6.89/1.28  fof(f600,plain,(
% 6.89/1.28    spl5_30),
% 6.89/1.28    inference(avatar_split_clause,[],[f77,f598])).
% 6.89/1.28  fof(f77,plain,(
% 6.89/1.28    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 6.89/1.28    inference(definition_unfolding,[],[f46,f74,f74,f72])).
% 6.89/1.28  fof(f46,plain,(
% 6.89/1.28    ( ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 6.89/1.28    inference(cnf_transformation,[],[f17])).
% 6.89/1.28  fof(f17,axiom,(
% 6.89/1.28    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 6.89/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_zfmisc_1)).
% 6.89/1.28  fof(f496,plain,(
% 6.89/1.28    spl5_27),
% 6.89/1.28    inference(avatar_split_clause,[],[f80,f494])).
% 6.89/1.28  fof(f80,plain,(
% 6.89/1.28    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) | ~r2_hidden(X0,X1)) )),
% 6.89/1.28    inference(definition_unfolding,[],[f50,f74,f74])).
% 6.89/1.28  fof(f50,plain,(
% 6.89/1.28    ( ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1)) )),
% 6.89/1.28    inference(cnf_transformation,[],[f24])).
% 6.89/1.28  fof(f24,plain,(
% 6.89/1.28    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1))),
% 6.89/1.28    inference(ennf_transformation,[],[f15])).
% 6.89/1.28  fof(f15,axiom,(
% 6.89/1.28    ! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 6.89/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).
% 6.89/1.28  fof(f193,plain,(
% 6.89/1.28    spl5_19),
% 6.89/1.28    inference(avatar_split_clause,[],[f78,f191])).
% 6.89/1.28  fof(f78,plain,(
% 6.89/1.28    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 6.89/1.28    inference(definition_unfolding,[],[f48,f73])).
% 6.89/1.28  fof(f73,plain,(
% 6.89/1.28    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 6.89/1.28    inference(definition_unfolding,[],[f44,f72])).
% 6.89/1.28  fof(f44,plain,(
% 6.89/1.28    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 6.89/1.28    inference(cnf_transformation,[],[f16])).
% 6.89/1.28  fof(f16,axiom,(
% 6.89/1.28    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 6.89/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 6.89/1.28  fof(f48,plain,(
% 6.89/1.28    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 6.89/1.28    inference(cnf_transformation,[],[f6])).
% 6.89/1.28  fof(f6,axiom,(
% 6.89/1.28    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 6.89/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 6.89/1.28  fof(f189,plain,(
% 6.89/1.28    spl5_18 | ~spl5_5 | ~spl5_8),
% 6.89/1.28    inference(avatar_split_clause,[],[f146,f122,f104,f187])).
% 6.89/1.28  fof(f146,plain,(
% 6.89/1.28    ( ! [X2,X0,X1] : (k3_xboole_0(k5_xboole_0(X2,X0),X1) = k5_xboole_0(k3_xboole_0(X2,X1),k3_xboole_0(X1,X0))) ) | (~spl5_5 | ~spl5_8)),
% 6.89/1.28    inference(superposition,[],[f123,f105])).
% 6.89/1.28  fof(f177,plain,(
% 6.89/1.28    spl5_16),
% 6.89/1.28    inference(avatar_split_clause,[],[f81,f175])).
% 6.89/1.28  fof(f81,plain,(
% 6.89/1.28    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = X3 | ~sP1(X0,X1,X2,X3)) )),
% 6.89/1.28    inference(definition_unfolding,[],[f64,f71])).
% 6.89/1.28  fof(f64,plain,(
% 6.89/1.28    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | ~sP1(X0,X1,X2,X3)) )),
% 6.89/1.28    inference(cnf_transformation,[],[f38])).
% 6.89/1.28  fof(f38,plain,(
% 6.89/1.28    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP1(X0,X1,X2,X3)) & (sP1(X0,X1,X2,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 6.89/1.28    inference(nnf_transformation,[],[f28])).
% 6.89/1.28  fof(f28,plain,(
% 6.89/1.28    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP1(X0,X1,X2,X3))),
% 6.89/1.28    inference(definition_folding,[],[f25,f27,f26])).
% 6.89/1.28  fof(f26,plain,(
% 6.89/1.28    ! [X4,X2,X1,X0] : (sP0(X4,X2,X1,X0) <=> (X2 = X4 | X1 = X4 | X0 = X4))),
% 6.89/1.28    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 6.89/1.28  fof(f27,plain,(
% 6.89/1.28    ! [X0,X1,X2,X3] : (sP1(X0,X1,X2,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> sP0(X4,X2,X1,X0)))),
% 6.89/1.28    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 6.89/1.28  fof(f25,plain,(
% 6.89/1.28    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 6.89/1.28    inference(ennf_transformation,[],[f7])).
% 6.89/1.28  fof(f7,axiom,(
% 6.89/1.28    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 6.89/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 6.89/1.28  fof(f172,plain,(
% 6.89/1.28    spl5_15 | ~spl5_4 | ~spl5_10 | ~spl5_11),
% 6.89/1.28    inference(avatar_split_clause,[],[f151,f141,f137,f100,f170])).
% 6.89/1.28  fof(f100,plain,(
% 6.89/1.28    spl5_4 <=> ! [X1,X3,X2] : sP0(X3,X1,X2,X3)),
% 6.89/1.28    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 6.89/1.28  fof(f137,plain,(
% 6.89/1.28    spl5_10 <=> ! [X1,X3,X5,X0,X2] : (r2_hidden(X5,X3) | ~sP0(X5,X2,X1,X0) | ~sP1(X0,X1,X2,X3))),
% 6.89/1.28    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 6.89/1.28  fof(f151,plain,(
% 6.89/1.28    ( ! [X2,X0,X1] : (r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))) ) | (~spl5_4 | ~spl5_10 | ~spl5_11)),
% 6.89/1.28    inference(unit_resulting_resolution,[],[f101,f142,f138])).
% 6.89/1.28  fof(f138,plain,(
% 6.89/1.28    ( ! [X2,X0,X5,X3,X1] : (~sP1(X0,X1,X2,X3) | ~sP0(X5,X2,X1,X0) | r2_hidden(X5,X3)) ) | ~spl5_10),
% 6.89/1.28    inference(avatar_component_clause,[],[f137])).
% 6.89/1.28  fof(f101,plain,(
% 6.89/1.28    ( ! [X2,X3,X1] : (sP0(X3,X1,X2,X3)) ) | ~spl5_4),
% 6.89/1.28    inference(avatar_component_clause,[],[f100])).
% 6.89/1.28  fof(f157,plain,(
% 6.89/1.28    spl5_12),
% 6.89/1.28    inference(avatar_split_clause,[],[f59,f155])).
% 6.89/1.28  fof(f59,plain,(
% 6.89/1.28    ( ! [X2,X0,X3,X1] : (X0 = X1 | X0 = X2 | X0 = X3 | ~sP0(X0,X1,X2,X3)) )),
% 6.89/1.28    inference(cnf_transformation,[],[f37])).
% 6.89/1.28  fof(f37,plain,(
% 6.89/1.28    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | (X0 != X1 & X0 != X2 & X0 != X3)) & (X0 = X1 | X0 = X2 | X0 = X3 | ~sP0(X0,X1,X2,X3)))),
% 6.89/1.28    inference(rectify,[],[f36])).
% 6.89/1.28  fof(f36,plain,(
% 6.89/1.28    ! [X4,X2,X1,X0] : ((sP0(X4,X2,X1,X0) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~sP0(X4,X2,X1,X0)))),
% 6.89/1.28    inference(flattening,[],[f35])).
% 6.89/1.28  fof(f35,plain,(
% 6.89/1.28    ! [X4,X2,X1,X0] : ((sP0(X4,X2,X1,X0) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~sP0(X4,X2,X1,X0)))),
% 6.89/1.28    inference(nnf_transformation,[],[f26])).
% 6.89/1.28  fof(f143,plain,(
% 6.89/1.28    spl5_11),
% 6.89/1.28    inference(avatar_split_clause,[],[f86,f141])).
% 6.89/1.28  fof(f86,plain,(
% 6.89/1.28    ( ! [X2,X0,X1] : (sP1(X0,X1,X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))) )),
% 6.89/1.28    inference(equality_resolution,[],[f82])).
% 6.89/1.28  fof(f82,plain,(
% 6.89/1.28    ( ! [X2,X0,X3,X1] : (sP1(X0,X1,X2,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 6.89/1.28    inference(definition_unfolding,[],[f63,f71])).
% 6.89/1.28  fof(f63,plain,(
% 6.89/1.28    ( ! [X2,X0,X3,X1] : (sP1(X0,X1,X2,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 6.89/1.28    inference(cnf_transformation,[],[f38])).
% 6.89/1.28  fof(f139,plain,(
% 6.89/1.28    spl5_10),
% 6.89/1.28    inference(avatar_split_clause,[],[f56,f137])).
% 6.89/1.28  fof(f56,plain,(
% 6.89/1.28    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | ~sP0(X5,X2,X1,X0) | ~sP1(X0,X1,X2,X3)) )),
% 6.89/1.28    inference(cnf_transformation,[],[f34])).
% 6.89/1.28  fof(f34,plain,(
% 6.89/1.28    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | ((~sP0(sK4(X0,X1,X2,X3),X2,X1,X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sP0(sK4(X0,X1,X2,X3),X2,X1,X0) | r2_hidden(sK4(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP0(X5,X2,X1,X0)) & (sP0(X5,X2,X1,X0) | ~r2_hidden(X5,X3))) | ~sP1(X0,X1,X2,X3)))),
% 6.89/1.28    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f33])).
% 6.89/1.28  fof(f33,plain,(
% 6.89/1.28    ! [X3,X2,X1,X0] : (? [X4] : ((~sP0(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP0(X4,X2,X1,X0) | r2_hidden(X4,X3))) => ((~sP0(sK4(X0,X1,X2,X3),X2,X1,X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sP0(sK4(X0,X1,X2,X3),X2,X1,X0) | r2_hidden(sK4(X0,X1,X2,X3),X3))))),
% 6.89/1.28    introduced(choice_axiom,[])).
% 6.89/1.28  fof(f32,plain,(
% 6.89/1.28    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | ? [X4] : ((~sP0(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP0(X4,X2,X1,X0) | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP0(X5,X2,X1,X0)) & (sP0(X5,X2,X1,X0) | ~r2_hidden(X5,X3))) | ~sP1(X0,X1,X2,X3)))),
% 6.89/1.28    inference(rectify,[],[f31])).
% 6.89/1.28  fof(f31,plain,(
% 6.89/1.28    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | ? [X4] : ((~sP0(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP0(X4,X2,X1,X0) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | ~sP0(X4,X2,X1,X0)) & (sP0(X4,X2,X1,X0) | ~r2_hidden(X4,X3))) | ~sP1(X0,X1,X2,X3)))),
% 6.89/1.28    inference(nnf_transformation,[],[f27])).
% 6.89/1.28  fof(f124,plain,(
% 6.89/1.28    spl5_8),
% 6.89/1.28    inference(avatar_split_clause,[],[f53,f122])).
% 6.89/1.28  fof(f53,plain,(
% 6.89/1.28    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 6.89/1.28    inference(cnf_transformation,[],[f3])).
% 6.89/1.28  fof(f3,axiom,(
% 6.89/1.28    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 6.89/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).
% 6.89/1.28  fof(f110,plain,(
% 6.89/1.28    spl5_6),
% 6.89/1.28    inference(avatar_split_clause,[],[f52,f108])).
% 6.89/1.28  fof(f52,plain,(
% 6.89/1.28    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 6.89/1.28    inference(cnf_transformation,[],[f5])).
% 6.89/1.28  fof(f5,axiom,(
% 6.89/1.28    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 6.89/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 6.89/1.28  fof(f106,plain,(
% 6.89/1.28    spl5_5),
% 6.89/1.28    inference(avatar_split_clause,[],[f42,f104])).
% 6.89/1.28  fof(f42,plain,(
% 6.89/1.28    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 6.89/1.28    inference(cnf_transformation,[],[f1])).
% 6.89/1.28  fof(f1,axiom,(
% 6.89/1.28    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 6.89/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 6.89/1.28  fof(f102,plain,(
% 6.89/1.28    spl5_4),
% 6.89/1.28    inference(avatar_split_clause,[],[f85,f100])).
% 6.89/1.28  fof(f85,plain,(
% 6.89/1.28    ( ! [X2,X3,X1] : (sP0(X3,X1,X2,X3)) )),
% 6.89/1.28    inference(equality_resolution,[],[f60])).
% 6.89/1.28  fof(f60,plain,(
% 6.89/1.28    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | X0 != X3) )),
% 6.89/1.28    inference(cnf_transformation,[],[f37])).
% 6.89/1.28  fof(f94,plain,(
% 6.89/1.28    spl5_2),
% 6.89/1.28    inference(avatar_split_clause,[],[f83,f92])).
% 6.89/1.28  fof(f83,plain,(
% 6.89/1.28    ( ! [X2,X3,X1] : (sP0(X1,X1,X2,X3)) )),
% 6.89/1.28    inference(equality_resolution,[],[f62])).
% 6.89/1.28  fof(f62,plain,(
% 6.89/1.28    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | X0 != X1) )),
% 6.89/1.28    inference(cnf_transformation,[],[f37])).
% 6.89/1.28  fof(f90,plain,(
% 6.89/1.28    spl5_1),
% 6.89/1.28    inference(avatar_split_clause,[],[f40,f88])).
% 6.89/1.28  fof(f40,plain,(
% 6.89/1.28    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 6.89/1.28    inference(cnf_transformation,[],[f4])).
% 6.89/1.28  fof(f4,axiom,(
% 6.89/1.28    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 6.89/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 6.89/1.28  % SZS output end Proof for theBenchmark
% 6.89/1.28  % (26160)------------------------------
% 6.89/1.28  % (26160)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.89/1.28  % (26160)Termination reason: Refutation
% 6.89/1.28  
% 6.89/1.28  % (26160)Memory used [KB]: 13304
% 6.89/1.28  % (26160)Time elapsed: 0.278 s
% 6.89/1.28  % (26160)------------------------------
% 6.89/1.28  % (26160)------------------------------
% 6.89/1.30  % (26115)Success in time 0.935 s
%------------------------------------------------------------------------------
