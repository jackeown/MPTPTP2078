%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : ordinal1__t4_ordinal1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:27 EDT 2019

% Result     : Theorem 7.61s
% Output     : Refutation 7.61s
% Verified   : 
% Statistics : Number of formulae       :  277 ( 952 expanded)
%              Number of leaves         :   76 ( 357 expanded)
%              Depth                    :   17
%              Number of atoms          :  718 (4064 expanded)
%              Number of equality atoms :  139 (1620 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2031,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f85,f92,f99,f106,f116,f129,f136,f143,f150,f171,f178,f185,f192,f203,f210,f219,f226,f240,f247,f254,f261,f301,f327,f334,f341,f348,f368,f375,f387,f411,f418,f425,f432,f439,f455,f462,f469,f476,f483,f498,f505,f567,f574,f581,f588,f611,f618,f625,f632,f655,f662,f669,f676,f1764,f1776,f1859,f1871,f1897,f2010])).

fof(f2010,plain,
    ( ~ spl8_4
    | ~ spl8_120 ),
    inference(avatar_contradiction_clause,[],[f2009])).

fof(f2009,plain,
    ( $false
    | ~ spl8_4
    | ~ spl8_120 ),
    inference(subsumption_resolution,[],[f1949,f91])).

fof(f91,plain,
    ( r2_hidden(sK2,sK3)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl8_4
  <=> r2_hidden(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f1949,plain,
    ( ~ r2_hidden(sK2,sK3)
    | ~ spl8_120 ),
    inference(superposition,[],[f761,f1896])).

fof(f1896,plain,
    ( sK3 = sK6(k2_enumset1(sK1,sK4,sK3,sK2))
    | ~ spl8_120 ),
    inference(avatar_component_clause,[],[f1895])).

fof(f1895,plain,
    ( spl8_120
  <=> sK3 = sK6(k2_enumset1(sK1,sK4,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_120])])).

fof(f761,plain,(
    ! [X2,X0,X3,X1] : ~ r2_hidden(X0,sK6(k2_enumset1(X1,X2,X3,X0))) ),
    inference(unit_resulting_resolution,[],[f487,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK6(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(condensation,[],[f53])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,sK6(X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK6(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK6(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f24,f32])).

fof(f32,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK6(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK6(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t4_ordinal1.p',t7_tarski)).

fof(f487,plain,(
    ! [X2,X0,X3,X1] : r2_hidden(X0,k2_enumset1(X1,X2,X3,X0)) ),
    inference(unit_resulting_resolution,[],[f70,f66])).

fof(f66,plain,(
    ! [X6,X4,X2,X3,X1] :
      ( ~ sP0(X6,X1,X2,X3,X4)
      | r2_hidden(X6,X4) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r2_hidden(X6,X4)
      | X0 != X6
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP0(X0,X1,X2,X3,X4)
        | ( ( ( sK7(X0,X1,X2,X3,X4) != X0
              & sK7(X0,X1,X2,X3,X4) != X1
              & sK7(X0,X1,X2,X3,X4) != X2
              & sK7(X0,X1,X2,X3,X4) != X3 )
            | ~ r2_hidden(sK7(X0,X1,X2,X3,X4),X4) )
          & ( sK7(X0,X1,X2,X3,X4) = X0
            | sK7(X0,X1,X2,X3,X4) = X1
            | sK7(X0,X1,X2,X3,X4) = X2
            | sK7(X0,X1,X2,X3,X4) = X3
            | r2_hidden(sK7(X0,X1,X2,X3,X4),X4) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X4)
              | ( X0 != X6
                & X1 != X6
                & X2 != X6
                & X3 != X6 ) )
            & ( X0 = X6
              | X1 = X6
              | X2 = X6
              | X3 = X6
              | ~ r2_hidden(X6,X4) ) )
        | ~ sP0(X0,X1,X2,X3,X4) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f36,f37])).

fof(f37,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( ( ( X0 != X5
              & X1 != X5
              & X2 != X5
              & X3 != X5 )
            | ~ r2_hidden(X5,X4) )
          & ( X0 = X5
            | X1 = X5
            | X2 = X5
            | X3 = X5
            | r2_hidden(X5,X4) ) )
     => ( ( ( sK7(X0,X1,X2,X3,X4) != X0
            & sK7(X0,X1,X2,X3,X4) != X1
            & sK7(X0,X1,X2,X3,X4) != X2
            & sK7(X0,X1,X2,X3,X4) != X3 )
          | ~ r2_hidden(sK7(X0,X1,X2,X3,X4),X4) )
        & ( sK7(X0,X1,X2,X3,X4) = X0
          | sK7(X0,X1,X2,X3,X4) = X1
          | sK7(X0,X1,X2,X3,X4) = X2
          | sK7(X0,X1,X2,X3,X4) = X3
          | r2_hidden(sK7(X0,X1,X2,X3,X4),X4) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP0(X0,X1,X2,X3,X4)
        | ? [X5] :
            ( ( ( X0 != X5
                & X1 != X5
                & X2 != X5
                & X3 != X5 )
              | ~ r2_hidden(X5,X4) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | X3 = X5
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X4)
              | ( X0 != X6
                & X1 != X6
                & X2 != X6
                & X3 != X6 ) )
            & ( X0 = X6
              | X1 = X6
              | X2 = X6
              | X3 = X6
              | ~ r2_hidden(X6,X4) ) )
        | ~ sP0(X0,X1,X2,X3,X4) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X3,X2,X1,X0,X4] :
      ( ( sP0(X3,X2,X1,X0,X4)
        | ? [X5] :
            ( ( ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 )
              | ~ r2_hidden(X5,X4) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X4)
              | ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X4) ) )
        | ~ sP0(X3,X2,X1,X0,X4) ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X3,X2,X1,X0,X4] :
      ( ( sP0(X3,X2,X1,X0,X4)
        | ? [X5] :
            ( ( ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 )
              | ~ r2_hidden(X5,X4) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X4)
              | ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X4) ) )
        | ~ sP0(X3,X2,X1,X0,X4) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X3,X2,X1,X0,X4] :
      ( sP0(X3,X2,X1,X0,X4)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ( X3 = X5
            | X2 = X5
            | X1 = X5
            | X0 = X5 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] : sP0(X3,X2,X1,X0,k2_enumset1(X0,X1,X2,X3)) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X3,X2,X1,X0,X4)
      | k2_enumset1(X0,X1,X2,X3) != X4 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_enumset1(X0,X1,X2,X3) = X4
        | ~ sP0(X3,X2,X1,X0,X4) )
      & ( sP0(X3,X2,X1,X0,X4)
        | k2_enumset1(X0,X1,X2,X3) != X4 ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> sP0(X3,X2,X1,X0,X4) ) ),
    inference(definition_folding,[],[f25,f26])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ( X3 = X5
            | X2 = X5
            | X1 = X5
            | X0 = X5 ) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X3 != X5
              & X2 != X5
              & X1 != X5
              & X0 != X5 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t4_ordinal1.p',d2_enumset1)).

fof(f1897,plain,
    ( spl8_120
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f1879,f104,f97,f83,f1895])).

fof(f83,plain,
    ( spl8_2
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f97,plain,
    ( spl8_6
  <=> r2_hidden(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f104,plain,
    ( spl8_8
  <=> r2_hidden(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f1879,plain,
    ( sK3 = sK6(k2_enumset1(sK1,sK4,sK3,sK2))
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f98,f1799])).

fof(f1799,plain,
    ( ! [X5] :
        ( ~ r2_hidden(X5,sK4)
        | sK6(k2_enumset1(sK1,sK4,X5,sK2)) = X5 )
    | ~ spl8_2
    | ~ spl8_8 ),
    inference(superposition,[],[f746,f1783])).

fof(f1783,plain,
    ( ! [X0] :
        ( sK4 = sK6(k2_enumset1(sK1,sK4,X0,sK2))
        | sK6(k2_enumset1(sK1,sK4,X0,sK2)) = X0 )
    | ~ spl8_2
    | ~ spl8_8 ),
    inference(resolution,[],[f1690,f105])).

fof(f105,plain,
    ( r2_hidden(sK4,sK1)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f104])).

fof(f1690,plain,
    ( ! [X6,X7] :
        ( ~ r2_hidden(X6,sK1)
        | sK6(k2_enumset1(sK1,X6,X7,sK2)) = X7
        | sK6(k2_enumset1(sK1,X6,X7,sK2)) = X6 )
    | ~ spl8_2 ),
    inference(superposition,[],[f738,f1666])).

fof(f1666,plain,
    ( ! [X24,X25] :
        ( sK1 = sK6(k2_enumset1(sK1,X24,X25,sK2))
        | sK6(k2_enumset1(sK1,X24,X25,sK2)) = X25
        | sK6(k2_enumset1(sK1,X24,X25,sK2)) = X24 )
    | ~ spl8_2 ),
    inference(resolution,[],[f1440,f84])).

fof(f84,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f1440,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r2_hidden(X4,X7)
      | sK6(k2_enumset1(X4,X5,X6,X7)) = X4
      | sK6(k2_enumset1(X4,X5,X6,X7)) = X6
      | sK6(k2_enumset1(X4,X5,X6,X7)) = X5 ) ),
    inference(superposition,[],[f730,f887])).

fof(f887,plain,(
    ! [X2,X0,X3,X1] :
      ( sK6(k2_enumset1(X0,X1,X2,X3)) = X3
      | sK6(k2_enumset1(X0,X1,X2,X3)) = X0
      | sK6(k2_enumset1(X0,X1,X2,X3)) = X2
      | sK6(k2_enumset1(X0,X1,X2,X3)) = X1 ) ),
    inference(resolution,[],[f729,f532])).

fof(f532,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X1,k2_enumset1(X3,X2,X0,X4))
      | X1 = X2
      | X1 = X3
      | X0 = X1
      | X1 = X4 ) ),
    inference(resolution,[],[f54,f70])).

fof(f54,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3,X4)
      | X1 = X6
      | X2 = X6
      | X3 = X6
      | ~ r2_hidden(X6,X4)
      | X0 = X6 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f729,plain,(
    ! [X2,X0,X3,X1] : r2_hidden(sK6(k2_enumset1(X0,X1,X2,X3)),k2_enumset1(X0,X1,X2,X3)) ),
    inference(unit_resulting_resolution,[],[f484,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X1),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f484,plain,(
    ! [X2,X0,X3,X1] : r2_hidden(X0,k2_enumset1(X0,X1,X2,X3)) ),
    inference(unit_resulting_resolution,[],[f70,f69])).

fof(f69,plain,(
    ! [X6,X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2,X6,X4)
      | r2_hidden(X6,X4) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r2_hidden(X6,X4)
      | X3 != X6
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f730,plain,(
    ! [X2,X0,X3,X1] : ~ r2_hidden(X0,sK6(k2_enumset1(X0,X1,X2,X3))) ),
    inference(unit_resulting_resolution,[],[f484,f71])).

fof(f738,plain,(
    ! [X2,X0,X3,X1] : ~ r2_hidden(X0,sK6(k2_enumset1(X1,X0,X2,X3))) ),
    inference(unit_resulting_resolution,[],[f485,f71])).

fof(f485,plain,(
    ! [X2,X0,X3,X1] : r2_hidden(X0,k2_enumset1(X1,X0,X2,X3)) ),
    inference(unit_resulting_resolution,[],[f70,f68])).

fof(f68,plain,(
    ! [X6,X4,X0,X3,X1] :
      ( ~ sP0(X0,X1,X6,X3,X4)
      | r2_hidden(X6,X4) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r2_hidden(X6,X4)
      | X2 != X6
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f746,plain,(
    ! [X2,X0,X3,X1] : ~ r2_hidden(X0,sK6(k2_enumset1(X1,X2,X0,X3))) ),
    inference(unit_resulting_resolution,[],[f486,f71])).

fof(f486,plain,(
    ! [X2,X0,X3,X1] : r2_hidden(X0,k2_enumset1(X1,X2,X0,X3)) ),
    inference(unit_resulting_resolution,[],[f70,f67])).

fof(f67,plain,(
    ! [X6,X4,X2,X0,X3] :
      ( ~ sP0(X0,X6,X2,X3,X4)
      | r2_hidden(X6,X4) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r2_hidden(X6,X4)
      | X1 != X6
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f98,plain,
    ( r2_hidden(sK3,sK4)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f97])).

fof(f1871,plain,
    ( ~ spl8_119
    | spl8_17
    | spl8_117 ),
    inference(avatar_split_clause,[],[f1864,f1857,f141,f1869])).

fof(f1869,plain,
    ( spl8_119
  <=> ~ m1_subset_1(sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_119])])).

fof(f141,plain,
    ( spl8_17
  <=> ~ v1_xboole_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f1857,plain,
    ( spl8_117
  <=> ~ r2_hidden(sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_117])])).

fof(f1864,plain,
    ( ~ m1_subset_1(sK4,sK4)
    | ~ spl8_17
    | ~ spl8_117 ),
    inference(unit_resulting_resolution,[],[f142,f1858,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t4_ordinal1.p',t2_subset)).

fof(f1858,plain,
    ( ~ r2_hidden(sK4,sK4)
    | ~ spl8_117 ),
    inference(avatar_component_clause,[],[f1857])).

fof(f142,plain,
    ( ~ v1_xboole_0(sK4)
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f141])).

fof(f1859,plain,
    ( spl8_114
    | ~ spl8_117
    | ~ spl8_2
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f1798,f104,f83,f1857,f1851])).

fof(f1851,plain,
    ( spl8_114
  <=> ! [X4] : sK6(k2_enumset1(sK1,sK4,X4,sK2)) = X4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_114])])).

fof(f1798,plain,
    ( ! [X4] :
        ( ~ r2_hidden(sK4,sK4)
        | sK6(k2_enumset1(sK1,sK4,X4,sK2)) = X4 )
    | ~ spl8_2
    | ~ spl8_8 ),
    inference(superposition,[],[f738,f1783])).

fof(f1776,plain,
    ( ~ spl8_113
    | spl8_19
    | spl8_111 ),
    inference(avatar_split_clause,[],[f1769,f1762,f148,f1774])).

fof(f1774,plain,
    ( spl8_113
  <=> ~ m1_subset_1(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_113])])).

fof(f148,plain,
    ( spl8_19
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f1762,plain,
    ( spl8_111
  <=> ~ r2_hidden(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_111])])).

fof(f1769,plain,
    ( ~ m1_subset_1(sK1,sK1)
    | ~ spl8_19
    | ~ spl8_111 ),
    inference(unit_resulting_resolution,[],[f149,f1763,f47])).

fof(f1763,plain,
    ( ~ r2_hidden(sK1,sK1)
    | ~ spl8_111 ),
    inference(avatar_component_clause,[],[f1762])).

fof(f149,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f148])).

fof(f1764,plain,
    ( spl8_108
    | ~ spl8_111
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f1688,f83,f1762,f1756])).

fof(f1756,plain,
    ( spl8_108
  <=> ! [X3,X2] :
        ( sK6(k2_enumset1(sK1,X2,X3,sK2)) = X3
        | sK6(k2_enumset1(sK1,X2,X3,sK2)) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_108])])).

fof(f1688,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(sK1,sK1)
        | sK6(k2_enumset1(sK1,X2,X3,sK2)) = X3
        | sK6(k2_enumset1(sK1,X2,X3,sK2)) = X2 )
    | ~ spl8_2 ),
    inference(superposition,[],[f730,f1666])).

fof(f676,plain,
    ( ~ spl8_107
    | ~ spl8_82 ),
    inference(avatar_split_clause,[],[f559,f503,f674])).

fof(f674,plain,
    ( spl8_107
  <=> ~ r2_hidden(sK5(sK4),sK6(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_107])])).

fof(f503,plain,
    ( spl8_82
  <=> r2_hidden(sK5(sK4),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_82])])).

fof(f559,plain,
    ( ~ r2_hidden(sK5(sK4),sK6(sK4))
    | ~ spl8_82 ),
    inference(unit_resulting_resolution,[],[f504,f71])).

fof(f504,plain,
    ( r2_hidden(sK5(sK4),sK4)
    | ~ spl8_82 ),
    inference(avatar_component_clause,[],[f503])).

fof(f669,plain,
    ( ~ spl8_105
    | ~ spl8_80 ),
    inference(avatar_split_clause,[],[f552,f496,f667])).

fof(f667,plain,
    ( spl8_105
  <=> ~ r2_hidden(sK5(sK3),sK6(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_105])])).

fof(f496,plain,
    ( spl8_80
  <=> r2_hidden(sK5(sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_80])])).

fof(f552,plain,
    ( ~ r2_hidden(sK5(sK3),sK6(sK3))
    | ~ spl8_80 ),
    inference(unit_resulting_resolution,[],[f497,f71])).

fof(f497,plain,
    ( r2_hidden(sK5(sK3),sK3)
    | ~ spl8_80 ),
    inference(avatar_component_clause,[],[f496])).

fof(f662,plain,
    ( ~ spl8_103
    | ~ spl8_78 ),
    inference(avatar_split_clause,[],[f545,f481,f660])).

fof(f660,plain,
    ( spl8_103
  <=> ~ r2_hidden(sK5(sK2),sK6(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_103])])).

fof(f481,plain,
    ( spl8_78
  <=> r2_hidden(sK5(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_78])])).

fof(f545,plain,
    ( ~ r2_hidden(sK5(sK2),sK6(sK2))
    | ~ spl8_78 ),
    inference(unit_resulting_resolution,[],[f482,f71])).

fof(f482,plain,
    ( r2_hidden(sK5(sK2),sK2)
    | ~ spl8_78 ),
    inference(avatar_component_clause,[],[f481])).

fof(f655,plain,
    ( ~ spl8_101
    | ~ spl8_76 ),
    inference(avatar_split_clause,[],[f538,f474,f653])).

fof(f653,plain,
    ( spl8_101
  <=> ~ r2_hidden(sK5(sK1),sK6(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_101])])).

fof(f474,plain,
    ( spl8_76
  <=> r2_hidden(sK5(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_76])])).

fof(f538,plain,
    ( ~ r2_hidden(sK5(sK1),sK6(sK1))
    | ~ spl8_76 ),
    inference(unit_resulting_resolution,[],[f475,f71])).

fof(f475,plain,
    ( r2_hidden(sK5(sK1),sK1)
    | ~ spl8_76 ),
    inference(avatar_component_clause,[],[f474])).

fof(f632,plain,
    ( ~ spl8_99
    | ~ spl8_42 ),
    inference(avatar_split_clause,[],[f288,f259,f630])).

fof(f630,plain,
    ( spl8_99
  <=> ~ r2_hidden(sK6(sK1),sK6(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_99])])).

fof(f259,plain,
    ( spl8_42
  <=> r2_hidden(sK6(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).

fof(f288,plain,
    ( ~ r2_hidden(sK6(sK1),sK6(sK1))
    | ~ spl8_42 ),
    inference(unit_resulting_resolution,[],[f260,f71])).

fof(f260,plain,
    ( r2_hidden(sK6(sK1),sK1)
    | ~ spl8_42 ),
    inference(avatar_component_clause,[],[f259])).

fof(f625,plain,
    ( ~ spl8_97
    | ~ spl8_40 ),
    inference(avatar_split_clause,[],[f281,f252,f623])).

fof(f623,plain,
    ( spl8_97
  <=> ~ r2_hidden(sK6(sK4),sK6(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_97])])).

fof(f252,plain,
    ( spl8_40
  <=> r2_hidden(sK6(sK4),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).

fof(f281,plain,
    ( ~ r2_hidden(sK6(sK4),sK6(sK4))
    | ~ spl8_40 ),
    inference(unit_resulting_resolution,[],[f253,f71])).

fof(f253,plain,
    ( r2_hidden(sK6(sK4),sK4)
    | ~ spl8_40 ),
    inference(avatar_component_clause,[],[f252])).

fof(f618,plain,
    ( ~ spl8_95
    | ~ spl8_38 ),
    inference(avatar_split_clause,[],[f274,f245,f616])).

fof(f616,plain,
    ( spl8_95
  <=> ~ r2_hidden(sK6(sK3),sK6(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_95])])).

fof(f245,plain,
    ( spl8_38
  <=> r2_hidden(sK6(sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).

fof(f274,plain,
    ( ~ r2_hidden(sK6(sK3),sK6(sK3))
    | ~ spl8_38 ),
    inference(unit_resulting_resolution,[],[f246,f71])).

fof(f246,plain,
    ( r2_hidden(sK6(sK3),sK3)
    | ~ spl8_38 ),
    inference(avatar_component_clause,[],[f245])).

fof(f611,plain,
    ( ~ spl8_93
    | ~ spl8_36 ),
    inference(avatar_split_clause,[],[f267,f238,f609])).

fof(f609,plain,
    ( spl8_93
  <=> ~ r2_hidden(sK6(sK2),sK6(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_93])])).

fof(f238,plain,
    ( spl8_36
  <=> r2_hidden(sK6(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).

fof(f267,plain,
    ( ~ r2_hidden(sK6(sK2),sK6(sK2))
    | ~ spl8_36 ),
    inference(unit_resulting_resolution,[],[f239,f71])).

fof(f239,plain,
    ( r2_hidden(sK6(sK2),sK2)
    | ~ spl8_36 ),
    inference(avatar_component_clause,[],[f238])).

fof(f588,plain,
    ( ~ spl8_91
    | ~ spl8_82 ),
    inference(avatar_split_clause,[],[f555,f503,f586])).

fof(f586,plain,
    ( spl8_91
  <=> ~ r2_hidden(sK4,sK5(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_91])])).

fof(f555,plain,
    ( ~ r2_hidden(sK4,sK5(sK4))
    | ~ spl8_82 ),
    inference(unit_resulting_resolution,[],[f504,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t4_ordinal1.p',antisymmetry_r2_hidden)).

fof(f581,plain,
    ( ~ spl8_89
    | ~ spl8_80 ),
    inference(avatar_split_clause,[],[f548,f496,f579])).

fof(f579,plain,
    ( spl8_89
  <=> ~ r2_hidden(sK3,sK5(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_89])])).

fof(f548,plain,
    ( ~ r2_hidden(sK3,sK5(sK3))
    | ~ spl8_80 ),
    inference(unit_resulting_resolution,[],[f497,f48])).

fof(f574,plain,
    ( ~ spl8_87
    | ~ spl8_78 ),
    inference(avatar_split_clause,[],[f541,f481,f572])).

fof(f572,plain,
    ( spl8_87
  <=> ~ r2_hidden(sK2,sK5(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_87])])).

fof(f541,plain,
    ( ~ r2_hidden(sK2,sK5(sK2))
    | ~ spl8_78 ),
    inference(unit_resulting_resolution,[],[f482,f48])).

fof(f567,plain,
    ( ~ spl8_85
    | ~ spl8_76 ),
    inference(avatar_split_clause,[],[f534,f474,f565])).

fof(f565,plain,
    ( spl8_85
  <=> ~ r2_hidden(sK1,sK5(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_85])])).

fof(f534,plain,
    ( ~ r2_hidden(sK1,sK5(sK1))
    | ~ spl8_76 ),
    inference(unit_resulting_resolution,[],[f475,f48])).

fof(f505,plain,
    ( spl8_82
    | spl8_17 ),
    inference(avatar_split_clause,[],[f313,f141,f503])).

fof(f313,plain,
    ( r2_hidden(sK5(sK4),sK4)
    | ~ spl8_17 ),
    inference(unit_resulting_resolution,[],[f142,f46,f47])).

fof(f46,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f9,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f9,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t4_ordinal1.p',existence_m1_subset_1)).

fof(f498,plain,
    ( spl8_80
    | spl8_15 ),
    inference(avatar_split_clause,[],[f312,f134,f496])).

fof(f134,plain,
    ( spl8_15
  <=> ~ v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f312,plain,
    ( r2_hidden(sK5(sK3),sK3)
    | ~ spl8_15 ),
    inference(unit_resulting_resolution,[],[f135,f46,f47])).

fof(f135,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f134])).

fof(f483,plain,
    ( spl8_78
    | spl8_13 ),
    inference(avatar_split_clause,[],[f311,f127,f481])).

fof(f127,plain,
    ( spl8_13
  <=> ~ v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f311,plain,
    ( r2_hidden(sK5(sK2),sK2)
    | ~ spl8_13 ),
    inference(unit_resulting_resolution,[],[f128,f46,f47])).

fof(f128,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f127])).

fof(f476,plain,
    ( spl8_76
    | spl8_19 ),
    inference(avatar_split_clause,[],[f310,f148,f474])).

fof(f310,plain,
    ( r2_hidden(sK5(sK1),sK1)
    | ~ spl8_19 ),
    inference(unit_resulting_resolution,[],[f149,f46,f47])).

fof(f469,plain,
    ( ~ spl8_75
    | ~ spl8_42 ),
    inference(avatar_split_clause,[],[f292,f259,f467])).

fof(f467,plain,
    ( spl8_75
  <=> ~ r2_hidden(sK1,sK6(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_75])])).

fof(f292,plain,
    ( ~ r2_hidden(sK1,sK6(sK1))
    | ~ spl8_42 ),
    inference(unit_resulting_resolution,[],[f260,f48])).

fof(f462,plain,
    ( spl8_72
    | ~ spl8_42 ),
    inference(avatar_split_clause,[],[f290,f259,f460])).

fof(f460,plain,
    ( spl8_72
  <=> m1_subset_1(sK6(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_72])])).

fof(f290,plain,
    ( m1_subset_1(sK6(sK1),sK1)
    | ~ spl8_42 ),
    inference(unit_resulting_resolution,[],[f260,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t4_ordinal1.p',t1_subset)).

fof(f455,plain,
    ( ~ spl8_71
    | ~ spl8_40 ),
    inference(avatar_split_clause,[],[f285,f252,f453])).

fof(f453,plain,
    ( spl8_71
  <=> ~ r2_hidden(sK4,sK6(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_71])])).

fof(f285,plain,
    ( ~ r2_hidden(sK4,sK6(sK4))
    | ~ spl8_40 ),
    inference(unit_resulting_resolution,[],[f253,f48])).

fof(f439,plain,
    ( spl8_68
    | ~ spl8_40 ),
    inference(avatar_split_clause,[],[f283,f252,f437])).

fof(f437,plain,
    ( spl8_68
  <=> m1_subset_1(sK6(sK4),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_68])])).

fof(f283,plain,
    ( m1_subset_1(sK6(sK4),sK4)
    | ~ spl8_40 ),
    inference(unit_resulting_resolution,[],[f253,f49])).

fof(f432,plain,
    ( ~ spl8_67
    | ~ spl8_38 ),
    inference(avatar_split_clause,[],[f278,f245,f430])).

fof(f430,plain,
    ( spl8_67
  <=> ~ r2_hidden(sK3,sK6(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_67])])).

fof(f278,plain,
    ( ~ r2_hidden(sK3,sK6(sK3))
    | ~ spl8_38 ),
    inference(unit_resulting_resolution,[],[f246,f48])).

fof(f425,plain,
    ( spl8_64
    | ~ spl8_38 ),
    inference(avatar_split_clause,[],[f276,f245,f423])).

fof(f423,plain,
    ( spl8_64
  <=> m1_subset_1(sK6(sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_64])])).

fof(f276,plain,
    ( m1_subset_1(sK6(sK3),sK3)
    | ~ spl8_38 ),
    inference(unit_resulting_resolution,[],[f246,f49])).

fof(f418,plain,
    ( ~ spl8_63
    | ~ spl8_36 ),
    inference(avatar_split_clause,[],[f271,f238,f416])).

fof(f416,plain,
    ( spl8_63
  <=> ~ r2_hidden(sK2,sK6(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_63])])).

fof(f271,plain,
    ( ~ r2_hidden(sK2,sK6(sK2))
    | ~ spl8_36 ),
    inference(unit_resulting_resolution,[],[f239,f48])).

fof(f411,plain,
    ( spl8_60
    | ~ spl8_36 ),
    inference(avatar_split_clause,[],[f269,f238,f409])).

fof(f409,plain,
    ( spl8_60
  <=> m1_subset_1(sK6(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_60])])).

fof(f269,plain,
    ( m1_subset_1(sK6(sK2),sK2)
    | ~ spl8_36 ),
    inference(unit_resulting_resolution,[],[f239,f49])).

fof(f387,plain,
    ( ~ spl8_59
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f265,f104,f385])).

fof(f385,plain,
    ( spl8_59
  <=> ~ r2_hidden(sK4,sK6(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_59])])).

fof(f265,plain,
    ( ~ r2_hidden(sK4,sK6(sK1))
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f105,f71])).

fof(f375,plain,
    ( ~ spl8_57
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f264,f97,f373])).

fof(f373,plain,
    ( spl8_57
  <=> ~ r2_hidden(sK3,sK6(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_57])])).

fof(f264,plain,
    ( ~ r2_hidden(sK3,sK6(sK4))
    | ~ spl8_6 ),
    inference(unit_resulting_resolution,[],[f98,f71])).

fof(f368,plain,
    ( ~ spl8_55
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f263,f90,f366])).

fof(f366,plain,
    ( spl8_55
  <=> ~ r2_hidden(sK2,sK6(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_55])])).

fof(f263,plain,
    ( ~ r2_hidden(sK2,sK6(sK3))
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f91,f71])).

fof(f348,plain,
    ( ~ spl8_53
    | spl8_17
    | spl8_27 ),
    inference(avatar_split_clause,[],[f305,f190,f141,f346])).

fof(f346,plain,
    ( spl8_53
  <=> ~ m1_subset_1(sK1,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_53])])).

fof(f190,plain,
    ( spl8_27
  <=> ~ r2_hidden(sK1,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f305,plain,
    ( ~ m1_subset_1(sK1,sK4)
    | ~ spl8_17
    | ~ spl8_27 ),
    inference(unit_resulting_resolution,[],[f191,f142,f47])).

fof(f191,plain,
    ( ~ r2_hidden(sK1,sK4)
    | ~ spl8_27 ),
    inference(avatar_component_clause,[],[f190])).

fof(f341,plain,
    ( ~ spl8_51
    | spl8_15
    | spl8_25 ),
    inference(avatar_split_clause,[],[f304,f183,f134,f339])).

fof(f339,plain,
    ( spl8_51
  <=> ~ m1_subset_1(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_51])])).

fof(f183,plain,
    ( spl8_25
  <=> ~ r2_hidden(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f304,plain,
    ( ~ m1_subset_1(sK4,sK3)
    | ~ spl8_15
    | ~ spl8_25 ),
    inference(unit_resulting_resolution,[],[f184,f135,f47])).

fof(f184,plain,
    ( ~ r2_hidden(sK4,sK3)
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f183])).

fof(f334,plain,
    ( ~ spl8_49
    | spl8_13
    | spl8_23 ),
    inference(avatar_split_clause,[],[f303,f176,f127,f332])).

fof(f332,plain,
    ( spl8_49
  <=> ~ m1_subset_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_49])])).

fof(f176,plain,
    ( spl8_23
  <=> ~ r2_hidden(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f303,plain,
    ( ~ m1_subset_1(sK3,sK2)
    | ~ spl8_13
    | ~ spl8_23 ),
    inference(unit_resulting_resolution,[],[f177,f128,f47])).

fof(f177,plain,
    ( ~ r2_hidden(sK3,sK2)
    | ~ spl8_23 ),
    inference(avatar_component_clause,[],[f176])).

fof(f327,plain,
    ( ~ spl8_47
    | spl8_19
    | spl8_21 ),
    inference(avatar_split_clause,[],[f302,f169,f148,f325])).

fof(f325,plain,
    ( spl8_47
  <=> ~ m1_subset_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_47])])).

fof(f169,plain,
    ( spl8_21
  <=> ~ r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f302,plain,
    ( ~ m1_subset_1(sK2,sK1)
    | ~ spl8_19
    | ~ spl8_21 ),
    inference(unit_resulting_resolution,[],[f170,f149,f47])).

fof(f170,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f169])).

fof(f301,plain,
    ( ~ spl8_45
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f262,f83,f299])).

fof(f299,plain,
    ( spl8_45
  <=> ~ r2_hidden(sK1,sK6(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_45])])).

fof(f262,plain,
    ( ~ r2_hidden(sK1,sK6(sK2))
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f84,f71])).

fof(f261,plain,
    ( spl8_42
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f230,f104,f259])).

fof(f230,plain,
    ( r2_hidden(sK6(sK1),sK1)
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f105,f52])).

fof(f254,plain,
    ( spl8_40
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f229,f97,f252])).

fof(f229,plain,
    ( r2_hidden(sK6(sK4),sK4)
    | ~ spl8_6 ),
    inference(unit_resulting_resolution,[],[f98,f52])).

fof(f247,plain,
    ( spl8_38
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f228,f90,f245])).

fof(f228,plain,
    ( r2_hidden(sK6(sK3),sK3)
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f91,f52])).

fof(f240,plain,
    ( spl8_36
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f227,f83,f238])).

fof(f227,plain,
    ( r2_hidden(sK6(sK2),sK2)
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f84,f52])).

fof(f226,plain,
    ( spl8_34
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f196,f104,f224])).

fof(f224,plain,
    ( spl8_34
  <=> m1_subset_1(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).

fof(f196,plain,
    ( m1_subset_1(sK4,sK1)
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f105,f49])).

fof(f219,plain,
    ( spl8_32
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f195,f97,f217])).

fof(f217,plain,
    ( spl8_32
  <=> m1_subset_1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f195,plain,
    ( m1_subset_1(sK3,sK4)
    | ~ spl8_6 ),
    inference(unit_resulting_resolution,[],[f98,f49])).

fof(f210,plain,
    ( spl8_30
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f194,f90,f208])).

fof(f208,plain,
    ( spl8_30
  <=> m1_subset_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f194,plain,
    ( m1_subset_1(sK2,sK3)
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f91,f49])).

fof(f203,plain,
    ( spl8_28
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f193,f83,f201])).

fof(f201,plain,
    ( spl8_28
  <=> m1_subset_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f193,plain,
    ( m1_subset_1(sK1,sK2)
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f84,f49])).

fof(f192,plain,
    ( ~ spl8_27
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f160,f104,f190])).

fof(f160,plain,
    ( ~ r2_hidden(sK1,sK4)
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f105,f48])).

fof(f185,plain,
    ( ~ spl8_25
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f159,f97,f183])).

fof(f159,plain,
    ( ~ r2_hidden(sK4,sK3)
    | ~ spl8_6 ),
    inference(unit_resulting_resolution,[],[f98,f48])).

fof(f178,plain,
    ( ~ spl8_23
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f158,f90,f176])).

fof(f158,plain,
    ( ~ r2_hidden(sK3,sK2)
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f91,f48])).

fof(f171,plain,
    ( ~ spl8_21
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f157,f83,f169])).

fof(f157,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f84,f48])).

fof(f150,plain,
    ( ~ spl8_19
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f120,f104,f148])).

fof(f120,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f105,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t4_ordinal1.p',t7_boole)).

fof(f143,plain,
    ( ~ spl8_17
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f119,f97,f141])).

fof(f119,plain,
    ( ~ v1_xboole_0(sK4)
    | ~ spl8_6 ),
    inference(unit_resulting_resolution,[],[f98,f51])).

fof(f136,plain,
    ( ~ spl8_15
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f118,f90,f134])).

fof(f118,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f91,f51])).

fof(f129,plain,
    ( ~ spl8_13
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f117,f83,f127])).

fof(f117,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f84,f51])).

fof(f116,plain,
    ( spl8_10
    | ~ spl8_0 ),
    inference(avatar_split_clause,[],[f107,f76,f114])).

fof(f114,plain,
    ( spl8_10
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f76,plain,
    ( spl8_0
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_0])])).

fof(f107,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl8_0 ),
    inference(unit_resulting_resolution,[],[f77,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t4_ordinal1.p',t6_boole)).

fof(f77,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl8_0 ),
    inference(avatar_component_clause,[],[f76])).

fof(f106,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f43,f104])).

fof(f43,plain,(
    r2_hidden(sK4,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( r2_hidden(sK4,sK1)
    & r2_hidden(sK3,sK4)
    & r2_hidden(sK2,sK3)
    & r2_hidden(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f16,f28])).

fof(f28,plain,
    ( ? [X0,X1,X2,X3] :
        ( r2_hidden(X3,X0)
        & r2_hidden(X2,X3)
        & r2_hidden(X1,X2)
        & r2_hidden(X0,X1) )
   => ( r2_hidden(sK4,sK1)
      & r2_hidden(sK3,sK4)
      & r2_hidden(sK2,sK3)
      & r2_hidden(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( r2_hidden(X3,X0)
      & r2_hidden(X2,X3)
      & r2_hidden(X1,X2)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( r2_hidden(X3,X0)
          & r2_hidden(X2,X3)
          & r2_hidden(X1,X2)
          & r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( r2_hidden(X3,X0)
        & r2_hidden(X2,X3)
        & r2_hidden(X1,X2)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t4_ordinal1.p',t4_ordinal1)).

fof(f99,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f42,f97])).

fof(f42,plain,(
    r2_hidden(sK3,sK4) ),
    inference(cnf_transformation,[],[f29])).

fof(f92,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f41,f90])).

fof(f41,plain,(
    r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f85,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f40,f83])).

fof(f40,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f78,plain,(
    spl8_0 ),
    inference(avatar_split_clause,[],[f44,f76])).

fof(f44,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t4_ordinal1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
