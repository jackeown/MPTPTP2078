%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:55 EST 2020

% Result     : Theorem 7.47s
% Output     : Refutation 7.47s
% Verified   : 
% Statistics : Number of formulae       :  254 (2056 expanded)
%              Number of leaves         :   53 ( 738 expanded)
%              Depth                    :   13
%              Number of atoms          :  672 (8175 expanded)
%              Number of equality atoms :  248 (5982 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3063,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f84,f89,f103,f135,f140,f280,f289,f290,f1139,f1386,f1387,f1388,f1393,f1394,f1395,f1448,f1708,f1713,f1718,f1723,f1728,f1733,f1734,f1735,f1740,f1741,f1742,f1743,f1744,f1745,f1746,f1747,f1748,f1749,f1750,f1751,f1752,f1757,f1758,f1759,f1760,f1853,f1858,f1860,f1865,f1870,f1871,f1880,f1886,f2047,f2052,f2057,f2062,f2067,f2072,f3061,f3062])).

fof(f3062,plain,(
    spl4_30 ),
    inference(avatar_contradiction_clause,[],[f3055])).

fof(f3055,plain,
    ( $false
    | spl4_30 ),
    inference(unit_resulting_resolution,[],[f78,f2056])).

fof(f2056,plain,
    ( ~ r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2))
    | spl4_30 ),
    inference(avatar_component_clause,[],[f2054])).

fof(f2054,plain,
    ( spl4_30
  <=> r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f78,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f45,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f41,f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f43,f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f52,f57])).

fof(f57,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f53,f54])).

fof(f54,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f53,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f43,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f41,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f45,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK3(X0,X1,X2,X3) != X2
              & sK3(X0,X1,X2,X3) != X1
              & sK3(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
          & ( sK3(X0,X1,X2,X3) = X2
            | sK3(X0,X1,X2,X3) = X1
            | sK3(X0,X1,X2,X3) = X0
            | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f28])).

fof(f28,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK3(X0,X1,X2,X3) != X2
            & sK3(X0,X1,X2,X3) != X1
            & sK3(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
        & ( sK3(X0,X1,X2,X3) = X2
          | sK3(X0,X1,X2,X3) = X1
          | sK3(X0,X1,X2,X3) = X0
          | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f3061,plain,(
    spl4_30 ),
    inference(avatar_contradiction_clause,[],[f3056])).

fof(f3056,plain,
    ( $false
    | spl4_30 ),
    inference(resolution,[],[f2056,f78])).

fof(f2072,plain,
    ( ~ spl4_33
    | spl4_8
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f2007,f1850,f286,f2069])).

fof(f2069,plain,
    ( spl4_33
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f286,plain,
    ( spl4_8
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f1850,plain,
    ( spl4_23
  <=> k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f2007,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2)
    | spl4_8
    | ~ spl4_23 ),
    inference(superposition,[],[f287,f1852])).

fof(f1852,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2)
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f1850])).

fof(f287,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f286])).

fof(f2067,plain,
    ( ~ spl4_32
    | spl4_7
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f2006,f1850,f282,f2064])).

fof(f2064,plain,
    ( spl4_32
  <=> r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f282,plain,
    ( spl4_7
  <=> r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f2006,plain,
    ( ~ r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | spl4_7
    | ~ spl4_23 ),
    inference(superposition,[],[f284,f1852])).

fof(f284,plain,
    ( ~ r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | spl4_7 ),
    inference(avatar_component_clause,[],[f282])).

fof(f2062,plain,
    ( spl4_31
    | ~ spl4_6
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f2005,f1850,f277,f2059])).

fof(f2059,plain,
    ( spl4_31
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f277,plain,
    ( spl4_6
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f2005,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl4_6
    | ~ spl4_23 ),
    inference(superposition,[],[f279,f1852])).

fof(f279,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f277])).

fof(f2057,plain,
    ( ~ spl4_30
    | spl4_4
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f1998,f1850,f132,f2054])).

fof(f132,plain,
    ( spl4_4
  <=> r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f1998,plain,
    ( ~ r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2))
    | spl4_4
    | ~ spl4_23 ),
    inference(superposition,[],[f134,f1852])).

fof(f134,plain,
    ( ~ r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f132])).

fof(f2052,plain,
    ( spl4_29
    | ~ spl4_3
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f1997,f1850,f100,f2049])).

fof(f2049,plain,
    ( spl4_29
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f100,plain,
    ( spl4_3
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f1997,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2))
    | ~ spl4_3
    | ~ spl4_23 ),
    inference(superposition,[],[f102,f1852])).

fof(f102,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f100])).

fof(f2047,plain,
    ( spl4_28
    | ~ spl4_2
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f1996,f1850,f86,f2044])).

fof(f2044,plain,
    ( spl4_28
  <=> r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f86,plain,
    ( spl4_2
  <=> r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f1996,plain,
    ( r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2))
    | ~ spl4_2
    | ~ spl4_23 ),
    inference(superposition,[],[f88,f1852])).

fof(f88,plain,
    ( r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f86])).

fof(f1886,plain,
    ( spl4_27
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f1842,f1136,f1883])).

fof(f1883,plain,
    ( spl4_27
  <=> k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f1136,plain,
    ( spl4_9
  <=> k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f1842,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2))
    | ~ spl4_9 ),
    inference(superposition,[],[f117,f1138])).

fof(f1138,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f1136])).

fof(f117,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f104,f90])).

fof(f90,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f36,f33])).

fof(f33,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f36,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f104,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f42,f32])).

fof(f32,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f42,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f1880,plain,
    ( spl4_26
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f1875,f1136,f1877])).

fof(f1877,plain,
    ( spl4_26
  <=> k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f1875,plain,
    ( k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f1874,f36])).

fof(f1874,plain,
    ( k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2))))
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f1873,f111])).

fof(f111,plain,(
    ! [X8,X7,X9] : k5_xboole_0(X7,k5_xboole_0(X8,X9)) = k5_xboole_0(X9,k5_xboole_0(X7,X8)) ),
    inference(superposition,[],[f42,f36])).

fof(f1873,plain,
    ( k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f1839,f36])).

fof(f1839,plain,
    ( k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2)))
    | ~ spl4_9 ),
    inference(superposition,[],[f109,f1138])).

fof(f109,plain,(
    ! [X4,X3] : k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4))) ),
    inference(superposition,[],[f42,f32])).

fof(f1871,plain,
    ( spl4_23
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f1836,f1136,f1850])).

fof(f1836,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2)
    | ~ spl4_9 ),
    inference(superposition,[],[f117,f1138])).

fof(f1870,plain,
    ( spl4_23
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f1835,f1136,f1850])).

fof(f1835,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2)
    | ~ spl4_9 ),
    inference(superposition,[],[f1138,f117])).

fof(f1865,plain,
    ( spl4_25
    | spl4_23
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f1861,f1136,f1850,f1863])).

fof(f1863,plain,
    ( spl4_25
  <=> ! [X3] :
        ( sK1 != sK3(sK0,sK0,sK1,X3)
        | ~ r2_hidden(sK3(sK0,sK0,sK1,X3),X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f1861,plain,
    ( ! [X3] :
        ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2)
        | sK1 != sK3(sK0,sK0,sK1,X3)
        | ~ r2_hidden(sK3(sK0,sK0,sK1,X3),X3) )
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f1830,f117])).

fof(f1830,plain,
    ( ! [X3] :
        ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(X3,k5_xboole_0(X3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))
        | sK1 != sK3(sK0,sK0,sK1,X3)
        | ~ r2_hidden(sK3(sK0,sK0,sK1,X3),X3) )
    | ~ spl4_9 ),
    inference(superposition,[],[f1138,f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = X3
      | sK3(X0,X1,X2,X3) != X2
      | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) ) ),
    inference(definition_unfolding,[],[f51,f60])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | sK3(X0,X1,X2,X3) != X2
      | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1860,plain,
    ( spl4_24
    | spl4_23
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f1859,f1136,f1850,f1856])).

fof(f1856,plain,
    ( spl4_24
  <=> ! [X1] :
        ( sK0 != sK3(sK0,sK0,sK1,X1)
        | ~ r2_hidden(sK3(sK0,sK0,sK1,X1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f1859,plain,
    ( ! [X2] :
        ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2)
        | sK0 != sK3(sK0,sK0,sK1,X2)
        | ~ r2_hidden(sK3(sK0,sK0,sK1,X2),X2) )
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f1829,f117])).

fof(f1829,plain,
    ( ! [X2] :
        ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(X2,k5_xboole_0(X2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))
        | sK0 != sK3(sK0,sK0,sK1,X2)
        | ~ r2_hidden(sK3(sK0,sK0,sK1,X2),X2) )
    | ~ spl4_9 ),
    inference(superposition,[],[f1138,f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = X3
      | sK3(X0,X1,X2,X3) != X1
      | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) ) ),
    inference(definition_unfolding,[],[f50,f60])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | sK3(X0,X1,X2,X3) != X1
      | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1858,plain,
    ( spl4_24
    | spl4_23
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f1854,f1136,f1850,f1856])).

fof(f1854,plain,
    ( ! [X1] :
        ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2)
        | sK0 != sK3(sK0,sK0,sK1,X1)
        | ~ r2_hidden(sK3(sK0,sK0,sK1,X1),X1) )
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f1828,f117])).

fof(f1828,plain,
    ( ! [X1] :
        ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(X1,k5_xboole_0(X1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))
        | sK0 != sK3(sK0,sK0,sK1,X1)
        | ~ r2_hidden(sK3(sK0,sK0,sK1,X1),X1) )
    | ~ spl4_9 ),
    inference(superposition,[],[f1138,f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = X3
      | sK3(X0,X1,X2,X3) != X0
      | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) ) ),
    inference(definition_unfolding,[],[f49,f60])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | sK3(X0,X1,X2,X3) != X0
      | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1853,plain,
    ( spl4_22
    | spl4_23
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f1845,f1136,f1850,f1847])).

fof(f1847,plain,
    ( spl4_22
  <=> ! [X0] :
        ( sK1 = sK3(sK0,sK0,sK1,X0)
        | r2_hidden(sK3(sK0,sK0,sK1,X0),X0)
        | sK0 = sK3(sK0,sK0,sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f1845,plain,
    ( ! [X0] :
        ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2)
        | sK1 = sK3(sK0,sK0,sK1,X0)
        | sK0 = sK3(sK0,sK0,sK1,X0)
        | r2_hidden(sK3(sK0,sK0,sK1,X0),X0) )
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f1844,f117])).

fof(f1844,plain,
    ( ! [X0] :
        ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(X0,k5_xboole_0(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))
        | sK1 = sK3(sK0,sK0,sK1,X0)
        | sK0 = sK3(sK0,sK0,sK1,X0)
        | r2_hidden(sK3(sK0,sK0,sK1,X0),X0) )
    | ~ spl4_9 ),
    inference(duplicate_literal_removal,[],[f1827])).

fof(f1827,plain,
    ( ! [X0] :
        ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(X0,k5_xboole_0(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))
        | sK1 = sK3(sK0,sK0,sK1,X0)
        | sK0 = sK3(sK0,sK0,sK1,X0)
        | sK0 = sK3(sK0,sK0,sK1,X0)
        | r2_hidden(sK3(sK0,sK0,sK1,X0),X0) )
    | ~ spl4_9 ),
    inference(superposition,[],[f1138,f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = X3
      | sK3(X0,X1,X2,X3) = X2
      | sK3(X0,X1,X2,X3) = X1
      | sK3(X0,X1,X2,X3) = X0
      | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ),
    inference(definition_unfolding,[],[f48,f60])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | sK3(X0,X1,X2,X3) = X2
      | sK3(X0,X1,X2,X3) = X1
      | sK3(X0,X1,X2,X3) = X0
      | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1760,plain,
    ( spl4_12
    | spl4_4
    | spl4_13 ),
    inference(avatar_split_clause,[],[f1662,f1445,f132,f1441])).

fof(f1441,plain,
    ( spl4_12
  <=> r2_hidden(sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f1445,plain,
    ( spl4_13
  <=> sK2 = sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f1662,plain,
    ( r2_hidden(sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | spl4_4
    | spl4_13 ),
    inference(unit_resulting_resolution,[],[f76,f1447,f213])).

fof(f213,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(sK2,sK2,sK2,X0),X0)
        | sK2 = sK3(sK2,sK2,sK2,X0)
        | ~ r2_hidden(sK0,X0) )
    | spl4_4 ),
    inference(duplicate_literal_removal,[],[f209])).

fof(f209,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK0,X0)
        | sK2 = sK3(sK2,sK2,sK2,X0)
        | sK2 = sK3(sK2,sK2,sK2,X0)
        | sK2 = sK3(sK2,sK2,sK2,X0)
        | r2_hidden(sK3(sK2,sK2,sK2,X0),X0) )
    | spl4_4 ),
    inference(superposition,[],[f134,f68])).

fof(f1447,plain,
    ( sK2 != sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | spl4_13 ),
    inference(avatar_component_clause,[],[f1445])).

fof(f76,plain,(
    ! [X2,X0,X5] : r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2)) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2) != X3 ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f46,f60])).

fof(f46,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1759,plain,
    ( ~ spl4_21
    | spl4_13 ),
    inference(avatar_split_clause,[],[f1663,f1445,f1754])).

fof(f1754,plain,
    ( spl4_21
  <=> r2_hidden(sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f1663,plain,
    ( ~ r2_hidden(sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | spl4_13 ),
    inference(unit_resulting_resolution,[],[f1447,f1447,f1447,f79])).

fof(f79,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))
      | X1 = X5
      | X0 = X5
      | X2 = X5 ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f44,f60])).

fof(f44,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1758,plain,
    ( ~ spl4_21
    | spl4_13 ),
    inference(avatar_split_clause,[],[f1666,f1445,f1754])).

fof(f1666,plain,
    ( ~ r2_hidden(sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | spl4_13 ),
    inference(unit_resulting_resolution,[],[f1447,f1447,f1447,f79])).

fof(f1757,plain,
    ( ~ spl4_21
    | spl4_13 ),
    inference(avatar_split_clause,[],[f1669,f1445,f1754])).

fof(f1669,plain,
    ( ~ r2_hidden(sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | spl4_13 ),
    inference(unit_resulting_resolution,[],[f1447,f1447,f1447,f79])).

fof(f1752,plain,
    ( spl4_12
    | spl4_8
    | spl4_13 ),
    inference(avatar_split_clause,[],[f1672,f1445,f286,f1441])).

fof(f1672,plain,
    ( r2_hidden(sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | spl4_8
    | spl4_13 ),
    inference(unit_resulting_resolution,[],[f1447,f1447,f287,f1447,f68])).

fof(f1751,plain,
    ( spl4_12
    | spl4_1
    | spl4_13 ),
    inference(avatar_split_clause,[],[f1673,f1445,f81,f1441])).

fof(f81,plain,
    ( spl4_1
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f1673,plain,
    ( r2_hidden(sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | spl4_1
    | spl4_13 ),
    inference(unit_resulting_resolution,[],[f83,f83,f83,f76,f1447,f1447,f1447,f188])).

fof(f188,plain,(
    ! [X35,X33,X31,X34,X32] :
      ( r2_hidden(sK3(X31,X32,X33,X34),X34)
      | X32 = X35
      | X31 = X35
      | X33 = X35
      | sK3(X31,X32,X33,X34) = X33
      | sK3(X31,X32,X33,X34) = X32
      | sK3(X31,X32,X33,X34) = X31
      | ~ r2_hidden(X35,X34) ) ),
    inference(superposition,[],[f79,f68])).

fof(f83,plain,
    ( sK0 != sK2
    | spl4_1 ),
    inference(avatar_component_clause,[],[f81])).

fof(f1750,plain,
    ( spl4_12
    | spl4_1
    | spl4_13 ),
    inference(avatar_split_clause,[],[f1674,f1445,f81,f1441])).

fof(f1674,plain,
    ( r2_hidden(sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | spl4_1
    | spl4_13 ),
    inference(unit_resulting_resolution,[],[f83,f83,f83,f78,f1447,f1447,f1447,f188])).

fof(f1749,plain,
    ( spl4_12
    | spl4_8
    | spl4_13 ),
    inference(avatar_split_clause,[],[f1675,f1445,f286,f1441])).

fof(f1675,plain,
    ( r2_hidden(sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | spl4_8
    | spl4_13 ),
    inference(unit_resulting_resolution,[],[f1447,f1447,f287,f1447,f68])).

fof(f1748,plain,
    ( spl4_12
    | spl4_1
    | spl4_13 ),
    inference(avatar_split_clause,[],[f1676,f1445,f81,f1441])).

fof(f1676,plain,
    ( r2_hidden(sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | spl4_1
    | spl4_13 ),
    inference(unit_resulting_resolution,[],[f83,f83,f83,f76,f1447,f1447,f1447,f188])).

fof(f1747,plain,
    ( spl4_12
    | spl4_1
    | spl4_13 ),
    inference(avatar_split_clause,[],[f1677,f1445,f81,f1441])).

fof(f1677,plain,
    ( r2_hidden(sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | spl4_1
    | spl4_13 ),
    inference(unit_resulting_resolution,[],[f83,f83,f83,f78,f1447,f1447,f1447,f188])).

fof(f1746,plain,
    ( spl4_12
    | spl4_8
    | spl4_13 ),
    inference(avatar_split_clause,[],[f1678,f1445,f286,f1441])).

fof(f1678,plain,
    ( r2_hidden(sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | spl4_8
    | spl4_13 ),
    inference(unit_resulting_resolution,[],[f1447,f1447,f287,f1447,f68])).

fof(f1745,plain,
    ( spl4_12
    | spl4_1
    | spl4_13 ),
    inference(avatar_split_clause,[],[f1679,f1445,f81,f1441])).

fof(f1679,plain,
    ( r2_hidden(sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | spl4_1
    | spl4_13 ),
    inference(unit_resulting_resolution,[],[f83,f83,f83,f76,f1447,f1447,f1447,f188])).

fof(f1744,plain,
    ( spl4_12
    | spl4_1
    | spl4_13 ),
    inference(avatar_split_clause,[],[f1680,f1445,f81,f1441])).

fof(f1680,plain,
    ( r2_hidden(sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | spl4_1
    | spl4_13 ),
    inference(unit_resulting_resolution,[],[f83,f83,f83,f78,f1447,f1447,f1447,f188])).

fof(f1743,plain,
    ( ~ spl4_17
    | spl4_13 ),
    inference(avatar_split_clause,[],[f1681,f1445,f1720])).

fof(f1720,plain,
    ( spl4_17
  <=> r2_hidden(sK2,k6_enumset1(sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f1681,plain,
    ( ~ r2_hidden(sK2,k6_enumset1(sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))
    | spl4_13 ),
    inference(unit_resulting_resolution,[],[f1447,f1447,f1447,f79])).

fof(f1742,plain,
    ( ~ spl4_15
    | spl4_1
    | spl4_13 ),
    inference(avatar_split_clause,[],[f1682,f1445,f81,f1710])).

fof(f1710,plain,
    ( spl4_15
  <=> r2_hidden(sK2,k6_enumset1(sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK0,sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f1682,plain,
    ( ~ r2_hidden(sK2,k6_enumset1(sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK0,sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))
    | spl4_1
    | spl4_13 ),
    inference(unit_resulting_resolution,[],[f83,f1447,f1447,f79])).

fof(f1741,plain,
    ( ~ spl4_19
    | spl4_1
    | spl4_13 ),
    inference(avatar_split_clause,[],[f1683,f1445,f81,f1730])).

fof(f1730,plain,
    ( spl4_19
  <=> r2_hidden(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f1683,plain,
    ( ~ r2_hidden(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))
    | spl4_1
    | spl4_13 ),
    inference(unit_resulting_resolution,[],[f1447,f83,f1447,f79])).

fof(f1740,plain,
    ( ~ spl4_20
    | spl4_1
    | spl4_13 ),
    inference(avatar_split_clause,[],[f1684,f1445,f81,f1737])).

fof(f1737,plain,
    ( spl4_20
  <=> r2_hidden(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f1684,plain,
    ( ~ r2_hidden(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))
    | spl4_1
    | spl4_13 ),
    inference(unit_resulting_resolution,[],[f83,f83,f1447,f79])).

fof(f1735,plain,
    ( ~ spl4_17
    | spl4_13 ),
    inference(avatar_split_clause,[],[f1687,f1445,f1720])).

fof(f1687,plain,
    ( ~ r2_hidden(sK2,k6_enumset1(sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))
    | spl4_13 ),
    inference(unit_resulting_resolution,[],[f1447,f1447,f1447,f79])).

fof(f1734,plain,
    ( ~ spl4_16
    | spl4_1
    | spl4_13 ),
    inference(avatar_split_clause,[],[f1688,f1445,f81,f1715])).

fof(f1715,plain,
    ( spl4_16
  <=> r2_hidden(sK2,k6_enumset1(sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f1688,plain,
    ( ~ r2_hidden(sK2,k6_enumset1(sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK0))
    | spl4_1
    | spl4_13 ),
    inference(unit_resulting_resolution,[],[f83,f1447,f1447,f79])).

fof(f1733,plain,
    ( ~ spl4_19
    | spl4_1
    | spl4_13 ),
    inference(avatar_split_clause,[],[f1689,f1445,f81,f1730])).

fof(f1689,plain,
    ( ~ r2_hidden(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))
    | spl4_1
    | spl4_13 ),
    inference(unit_resulting_resolution,[],[f1447,f83,f1447,f79])).

fof(f1728,plain,
    ( ~ spl4_18
    | spl4_1
    | spl4_13 ),
    inference(avatar_split_clause,[],[f1690,f1445,f81,f1725])).

fof(f1725,plain,
    ( spl4_18
  <=> r2_hidden(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f1690,plain,
    ( ~ r2_hidden(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK0))
    | spl4_1
    | spl4_13 ),
    inference(unit_resulting_resolution,[],[f83,f83,f1447,f79])).

fof(f1723,plain,
    ( ~ spl4_17
    | spl4_13 ),
    inference(avatar_split_clause,[],[f1693,f1445,f1720])).

fof(f1693,plain,
    ( ~ r2_hidden(sK2,k6_enumset1(sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))
    | spl4_13 ),
    inference(unit_resulting_resolution,[],[f1447,f1447,f1447,f79])).

fof(f1718,plain,
    ( ~ spl4_16
    | spl4_1
    | spl4_13 ),
    inference(avatar_split_clause,[],[f1694,f1445,f81,f1715])).

fof(f1694,plain,
    ( ~ r2_hidden(sK2,k6_enumset1(sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK0))
    | spl4_1
    | spl4_13 ),
    inference(unit_resulting_resolution,[],[f83,f1447,f1447,f79])).

fof(f1713,plain,
    ( ~ spl4_15
    | spl4_1
    | spl4_13 ),
    inference(avatar_split_clause,[],[f1695,f1445,f81,f1710])).

fof(f1695,plain,
    ( ~ r2_hidden(sK2,k6_enumset1(sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK0,sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))
    | spl4_1
    | spl4_13 ),
    inference(unit_resulting_resolution,[],[f1447,f83,f1447,f79])).

fof(f1708,plain,
    ( ~ spl4_14
    | spl4_1
    | spl4_13 ),
    inference(avatar_split_clause,[],[f1696,f1445,f81,f1705])).

fof(f1705,plain,
    ( spl4_14
  <=> r2_hidden(sK2,k6_enumset1(sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f1696,plain,
    ( ~ r2_hidden(sK2,k6_enumset1(sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK0,sK0))
    | spl4_1
    | spl4_13 ),
    inference(unit_resulting_resolution,[],[f83,f83,f1447,f79])).

fof(f1448,plain,
    ( ~ spl4_12
    | ~ spl4_13
    | ~ spl4_2
    | spl4_7 ),
    inference(avatar_split_clause,[],[f1439,f282,f86,f1445,f1441])).

fof(f1439,plain,
    ( sK2 != sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ r2_hidden(sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl4_2
    | spl4_7 ),
    inference(duplicate_literal_removal,[],[f1433])).

fof(f1433,plain,
    ( sK2 != sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ r2_hidden(sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | sK2 != sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ r2_hidden(sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl4_2
    | spl4_7 ),
    inference(resolution,[],[f911,f145])).

fof(f145,plain,
    ( ! [X3] :
        ( r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),X3)
        | sK2 != sK3(sK2,sK2,sK2,X3)
        | ~ r2_hidden(sK3(sK2,sK2,sK2,X3),X3) )
    | ~ spl4_2 ),
    inference(superposition,[],[f88,f65])).

fof(f911,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
        | sK2 != sK3(sK2,sK2,sK2,X1)
        | ~ r2_hidden(sK3(sK2,sK2,sK2,X1),X1) )
    | spl4_7 ),
    inference(superposition,[],[f284,f67])).

fof(f1395,plain,
    ( ~ spl4_11
    | spl4_8 ),
    inference(avatar_split_clause,[],[f1359,f286,f1390])).

fof(f1390,plain,
    ( spl4_11
  <=> r2_hidden(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f1359,plain,
    ( ~ r2_hidden(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))
    | spl4_8 ),
    inference(unit_resulting_resolution,[],[f287,f287,f287,f79])).

fof(f1394,plain,
    ( ~ spl4_11
    | spl4_8 ),
    inference(avatar_split_clause,[],[f1362,f286,f1390])).

fof(f1362,plain,
    ( ~ r2_hidden(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))
    | spl4_8 ),
    inference(unit_resulting_resolution,[],[f287,f287,f287,f79])).

fof(f1393,plain,
    ( ~ spl4_11
    | spl4_8 ),
    inference(avatar_split_clause,[],[f1365,f286,f1390])).

fof(f1365,plain,
    ( ~ r2_hidden(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))
    | spl4_8 ),
    inference(unit_resulting_resolution,[],[f287,f287,f287,f79])).

fof(f1388,plain,
    ( ~ spl4_10
    | spl4_8 ),
    inference(avatar_split_clause,[],[f1368,f286,f1383])).

fof(f1383,plain,
    ( spl4_10
  <=> r2_hidden(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f1368,plain,
    ( ~ r2_hidden(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))
    | spl4_8 ),
    inference(unit_resulting_resolution,[],[f287,f287,f287,f79])).

fof(f1387,plain,
    ( ~ spl4_10
    | spl4_8 ),
    inference(avatar_split_clause,[],[f1371,f286,f1383])).

fof(f1371,plain,
    ( ~ r2_hidden(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))
    | spl4_8 ),
    inference(unit_resulting_resolution,[],[f287,f287,f287,f79])).

fof(f1386,plain,
    ( ~ spl4_10
    | spl4_8 ),
    inference(avatar_split_clause,[],[f1374,f286,f1383])).

fof(f1374,plain,
    ( ~ r2_hidden(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))
    | spl4_8 ),
    inference(unit_resulting_resolution,[],[f287,f287,f287,f79])).

fof(f1139,plain,
    ( spl4_9
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f1134,f100,f1136])).

fof(f1134,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2)
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f1098,f36])).

fof(f1098,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2)
    | ~ spl4_3 ),
    inference(superposition,[],[f202,f102])).

fof(f202,plain,(
    ! [X14,X12,X10,X8,X15,X13,X11,X9] : k6_enumset1(X9,X10,X11,X12,X13,X14,X15,X8) = k5_xboole_0(k6_enumset1(X9,X9,X10,X11,X12,X13,X14,X15),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X9,X9,X10,X11,X12,X13,X14,X15),k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8)))) ),
    inference(superposition,[],[f63,f35])).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f63,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) ),
    inference(definition_unfolding,[],[f55,f56,f54,f62])).

fof(f62,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f34,f61])).

fof(f61,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f37,f60])).

fof(f37,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f34,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f56,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f38,f39])).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f55,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).

fof(f290,plain,
    ( ~ spl4_7
    | spl4_8
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f274,f100,f286,f282])).

fof(f274,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | ~ r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl4_3 ),
    inference(superposition,[],[f102,f95])).

fof(f95,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(X3,X2) = X2
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f40,f35])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f289,plain,
    ( ~ spl4_7
    | spl4_8
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f270,f100,f286,f282])).

fof(f270,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | ~ r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl4_3 ),
    inference(superposition,[],[f95,f102])).

fof(f280,plain,
    ( spl4_6
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f266,f86,f277])).

fof(f266,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f88,f95])).

fof(f140,plain,
    ( ~ spl4_5
    | spl4_1 ),
    inference(avatar_split_clause,[],[f120,f81,f137])).

fof(f137,plain,
    ( spl4_5
  <=> r2_hidden(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f120,plain,
    ( ~ r2_hidden(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f83,f83,f83,f79])).

fof(f135,plain,
    ( ~ spl4_4
    | spl4_1 ),
    inference(avatar_split_clause,[],[f121,f81,f132])).

fof(f121,plain,
    ( ~ r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f83,f83,f83,f79])).

fof(f103,plain,
    ( spl4_3
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f94,f86,f100])).

fof(f94,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f88,f40])).

fof(f89,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f64,f86])).

fof(f64,plain,(
    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(definition_unfolding,[],[f30,f61,f62])).

fof(f30,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( sK0 != sK2
    & r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f23])).

fof(f23,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) )
   => ( sK0 != sK2
      & r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
       => X0 = X2 ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
     => X0 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_zfmisc_1)).

fof(f84,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f31,f81])).

fof(f31,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:21:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (28785)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.50  % (28784)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (28781)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.22/0.52  % (28792)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.22/0.52  % (28800)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.22/0.52  % (28793)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.22/0.52  % (28801)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.22/0.52  % (28795)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.22/0.52  % (28795)Refutation not found, incomplete strategy% (28795)------------------------------
% 1.22/0.52  % (28795)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.52  % (28795)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.52  
% 1.22/0.52  % (28795)Memory used [KB]: 10618
% 1.22/0.52  % (28795)Time elapsed: 0.117 s
% 1.22/0.52  % (28795)------------------------------
% 1.22/0.52  % (28795)------------------------------
% 1.34/0.53  % (28779)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.34/0.53  % (28789)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.34/0.53  % (28807)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.34/0.53  % (28799)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.34/0.53  % (28804)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.34/0.53  % (28793)Refutation not found, incomplete strategy% (28793)------------------------------
% 1.34/0.53  % (28793)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.53  % (28791)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.34/0.53  % (28778)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.34/0.53  % (28780)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.34/0.53  % (28778)Refutation not found, incomplete strategy% (28778)------------------------------
% 1.34/0.53  % (28778)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.53  % (28778)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.53  
% 1.34/0.53  % (28778)Memory used [KB]: 1663
% 1.34/0.53  % (28778)Time elapsed: 0.123 s
% 1.34/0.53  % (28778)------------------------------
% 1.34/0.53  % (28778)------------------------------
% 1.34/0.53  % (28793)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.53  
% 1.34/0.53  % (28793)Memory used [KB]: 6140
% 1.34/0.53  % (28793)Time elapsed: 0.123 s
% 1.34/0.53  % (28793)------------------------------
% 1.34/0.53  % (28793)------------------------------
% 1.34/0.53  % (28782)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.34/0.53  % (28780)Refutation not found, incomplete strategy% (28780)------------------------------
% 1.34/0.53  % (28780)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.53  % (28780)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.53  
% 1.34/0.53  % (28780)Memory used [KB]: 10746
% 1.34/0.53  % (28780)Time elapsed: 0.124 s
% 1.34/0.53  % (28780)------------------------------
% 1.34/0.53  % (28780)------------------------------
% 1.34/0.53  % (28782)Refutation not found, incomplete strategy% (28782)------------------------------
% 1.34/0.53  % (28782)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.53  % (28782)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.53  
% 1.34/0.53  % (28782)Memory used [KB]: 6140
% 1.34/0.53  % (28782)Time elapsed: 0.125 s
% 1.34/0.53  % (28782)------------------------------
% 1.34/0.53  % (28782)------------------------------
% 1.34/0.53  % (28790)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.34/0.54  % (28805)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.34/0.54  % (28789)Refutation not found, incomplete strategy% (28789)------------------------------
% 1.34/0.54  % (28789)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (28794)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.34/0.54  % (28799)Refutation not found, incomplete strategy% (28799)------------------------------
% 1.34/0.54  % (28799)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (28799)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.54  
% 1.34/0.54  % (28799)Memory used [KB]: 1663
% 1.34/0.54  % (28799)Time elapsed: 0.092 s
% 1.34/0.54  % (28799)------------------------------
% 1.34/0.54  % (28799)------------------------------
% 1.34/0.54  % (28789)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.54  
% 1.34/0.54  % (28789)Memory used [KB]: 10618
% 1.34/0.54  % (28789)Time elapsed: 0.143 s
% 1.34/0.54  % (28789)------------------------------
% 1.34/0.54  % (28789)------------------------------
% 1.34/0.54  % (28788)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.34/0.54  % (28797)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.34/0.54  % (28787)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.34/0.54  % (28786)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.34/0.54  % (28796)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.34/0.54  % (28802)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.34/0.54  % (28787)Refutation not found, incomplete strategy% (28787)------------------------------
% 1.34/0.54  % (28787)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (28783)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.34/0.54  % (28806)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.34/0.55  % (28798)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.34/0.55  % (28786)Refutation not found, incomplete strategy% (28786)------------------------------
% 1.34/0.55  % (28786)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.55  % (28786)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.55  
% 1.34/0.55  % (28786)Memory used [KB]: 10746
% 1.34/0.55  % (28786)Time elapsed: 0.148 s
% 1.34/0.55  % (28786)------------------------------
% 1.34/0.55  % (28786)------------------------------
% 1.34/0.55  % (28803)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.34/0.55  % (28803)Refutation not found, incomplete strategy% (28803)------------------------------
% 1.34/0.55  % (28803)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.55  % (28803)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.55  
% 1.34/0.55  % (28803)Memory used [KB]: 6268
% 1.34/0.55  % (28803)Time elapsed: 0.150 s
% 1.34/0.55  % (28803)------------------------------
% 1.34/0.55  % (28803)------------------------------
% 1.34/0.55  % (28787)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.55  
% 1.34/0.55  % (28787)Memory used [KB]: 10618
% 1.34/0.55  % (28787)Time elapsed: 0.138 s
% 1.34/0.55  % (28787)------------------------------
% 1.34/0.55  % (28787)------------------------------
% 1.34/0.56  % (28804)Refutation not found, incomplete strategy% (28804)------------------------------
% 1.34/0.56  % (28804)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.56  % (28788)Refutation not found, incomplete strategy% (28788)------------------------------
% 1.34/0.56  % (28788)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.56  % (28788)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.56  
% 1.34/0.56  % (28788)Memory used [KB]: 10618
% 1.34/0.56  % (28788)Time elapsed: 0.157 s
% 1.34/0.56  % (28788)------------------------------
% 1.34/0.56  % (28788)------------------------------
% 1.34/0.57  % (28804)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.57  
% 1.34/0.57  % (28804)Memory used [KB]: 10874
% 1.34/0.57  % (28804)Time elapsed: 0.153 s
% 1.34/0.57  % (28804)------------------------------
% 1.34/0.57  % (28804)------------------------------
% 1.94/0.67  % (28808)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.94/0.67  % (28809)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 1.94/0.67  % (28811)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 1.94/0.67  % (28814)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 1.94/0.67  % (28810)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 1.94/0.67  % (28812)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 1.94/0.67  % (28816)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 1.94/0.68  % (28808)Refutation not found, incomplete strategy% (28808)------------------------------
% 1.94/0.68  % (28808)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.94/0.68  % (28813)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 1.94/0.68  % (28817)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 1.94/0.68  % (28815)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 1.94/0.68  % (28808)Termination reason: Refutation not found, incomplete strategy
% 1.94/0.68  
% 1.94/0.68  % (28808)Memory used [KB]: 6140
% 1.94/0.68  % (28808)Time elapsed: 0.118 s
% 1.94/0.68  % (28808)------------------------------
% 1.94/0.68  % (28808)------------------------------
% 1.94/0.69  % (28818)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 2.33/0.71  % (28819)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 2.68/0.79  % (28809)Refutation not found, incomplete strategy% (28809)------------------------------
% 2.68/0.79  % (28809)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.68/0.80  % (28809)Termination reason: Refutation not found, incomplete strategy
% 2.68/0.80  
% 2.68/0.80  % (28809)Memory used [KB]: 6140
% 2.68/0.80  % (28809)Time elapsed: 0.231 s
% 2.68/0.80  % (28809)------------------------------
% 2.68/0.80  % (28809)------------------------------
% 2.68/0.82  % (28820)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 2.68/0.84  % (28783)Time limit reached!
% 2.68/0.84  % (28783)------------------------------
% 2.68/0.84  % (28783)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.68/0.84  % (28783)Termination reason: Time limit
% 2.68/0.84  
% 2.68/0.84  % (28783)Memory used [KB]: 10362
% 2.68/0.84  % (28783)Time elapsed: 0.406 s
% 2.68/0.84  % (28783)------------------------------
% 2.68/0.84  % (28783)------------------------------
% 3.37/0.90  % (28790)Time limit reached!
% 3.37/0.90  % (28790)------------------------------
% 3.37/0.90  % (28790)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.37/0.92  % (28821)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 3.37/0.92  % (28790)Termination reason: Time limit
% 3.37/0.92  % (28790)Termination phase: Saturation
% 3.37/0.92  
% 3.37/0.92  % (28790)Memory used [KB]: 10874
% 3.37/0.92  % (28790)Time elapsed: 0.500 s
% 3.37/0.92  % (28790)------------------------------
% 3.37/0.92  % (28790)------------------------------
% 3.51/0.97  % (28812)Time limit reached!
% 3.51/0.97  % (28812)------------------------------
% 3.51/0.97  % (28812)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.51/0.97  % (28822)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 3.51/0.97  % (28812)Termination reason: Time limit
% 3.51/0.97  
% 3.51/0.97  % (28812)Memory used [KB]: 14839
% 3.51/0.97  % (28812)Time elapsed: 0.407 s
% 3.51/0.97  % (28812)------------------------------
% 3.51/0.97  % (28812)------------------------------
% 3.51/0.99  % (28811)Time limit reached!
% 3.51/0.99  % (28811)------------------------------
% 3.51/0.99  % (28811)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.51/0.99  % (28811)Termination reason: Time limit
% 3.51/0.99  % (28811)Termination phase: Saturation
% 3.51/0.99  
% 3.51/0.99  % (28811)Memory used [KB]: 8571
% 3.51/0.99  % (28811)Time elapsed: 0.400 s
% 3.51/0.99  % (28811)------------------------------
% 3.51/0.99  % (28811)------------------------------
% 3.51/1.00  % (28779)Time limit reached!
% 3.51/1.00  % (28779)------------------------------
% 3.51/1.00  % (28779)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.51/1.00  % (28779)Termination reason: Time limit
% 3.51/1.00  
% 3.51/1.00  % (28779)Memory used [KB]: 10618
% 3.51/1.00  % (28779)Time elapsed: 0.595 s
% 3.51/1.00  % (28779)------------------------------
% 3.51/1.00  % (28779)------------------------------
% 3.51/1.01  % (28806)Time limit reached!
% 3.51/1.01  % (28806)------------------------------
% 3.51/1.01  % (28806)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.16/1.03  % (28806)Termination reason: Time limit
% 4.16/1.03  
% 4.16/1.03  % (28806)Memory used [KB]: 8187
% 4.16/1.03  % (28806)Time elapsed: 0.613 s
% 4.16/1.03  % (28806)------------------------------
% 4.16/1.03  % (28806)------------------------------
% 4.16/1.03  % (28823)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 4.16/1.06  % (28794)Time limit reached!
% 4.16/1.06  % (28794)------------------------------
% 4.16/1.06  % (28794)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.16/1.06  % (28794)Termination reason: Time limit
% 4.16/1.06  
% 4.16/1.06  % (28794)Memory used [KB]: 16630
% 4.16/1.06  % (28794)Time elapsed: 0.656 s
% 4.16/1.06  % (28794)------------------------------
% 4.16/1.06  % (28794)------------------------------
% 4.16/1.07  % (28785)Time limit reached!
% 4.16/1.07  % (28785)------------------------------
% 4.16/1.07  % (28785)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.16/1.08  % (28785)Termination reason: Time limit
% 4.16/1.08  
% 4.16/1.08  % (28785)Memory used [KB]: 15223
% 4.16/1.08  % (28785)Time elapsed: 0.661 s
% 4.16/1.08  % (28785)------------------------------
% 4.16/1.08  % (28785)------------------------------
% 4.48/1.10  % (28825)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 4.48/1.10  % (28824)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 4.48/1.11  % (28825)Refutation not found, incomplete strategy% (28825)------------------------------
% 4.48/1.11  % (28825)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.48/1.11  % (28825)Termination reason: Refutation not found, incomplete strategy
% 4.48/1.11  
% 4.48/1.11  % (28825)Memory used [KB]: 6140
% 4.48/1.11  % (28825)Time elapsed: 0.103 s
% 4.48/1.11  % (28825)------------------------------
% 4.48/1.11  % (28825)------------------------------
% 4.48/1.14  % (28826)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 4.48/1.14  % (28827)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 4.74/1.18  % (28828)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 4.74/1.23  % (28829)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 4.74/1.28  % (28830)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 7.25/1.30  % (28820)Time limit reached!
% 7.25/1.30  % (28820)------------------------------
% 7.25/1.30  % (28820)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.25/1.30  % (28820)Termination reason: Time limit
% 7.25/1.30  
% 7.25/1.30  % (28820)Memory used [KB]: 5884
% 7.25/1.30  % (28820)Time elapsed: 0.582 s
% 7.25/1.30  % (28820)------------------------------
% 7.25/1.30  % (28820)------------------------------
% 7.47/1.31  % (28796)Refutation found. Thanks to Tanya!
% 7.47/1.31  % SZS status Theorem for theBenchmark
% 7.47/1.31  % SZS output start Proof for theBenchmark
% 7.47/1.31  fof(f3063,plain,(
% 7.47/1.31    $false),
% 7.47/1.31    inference(avatar_sat_refutation,[],[f84,f89,f103,f135,f140,f280,f289,f290,f1139,f1386,f1387,f1388,f1393,f1394,f1395,f1448,f1708,f1713,f1718,f1723,f1728,f1733,f1734,f1735,f1740,f1741,f1742,f1743,f1744,f1745,f1746,f1747,f1748,f1749,f1750,f1751,f1752,f1757,f1758,f1759,f1760,f1853,f1858,f1860,f1865,f1870,f1871,f1880,f1886,f2047,f2052,f2057,f2062,f2067,f2072,f3061,f3062])).
% 7.47/1.31  fof(f3062,plain,(
% 7.47/1.31    spl4_30),
% 7.47/1.31    inference(avatar_contradiction_clause,[],[f3055])).
% 7.47/1.31  fof(f3055,plain,(
% 7.47/1.31    $false | spl4_30),
% 7.47/1.31    inference(unit_resulting_resolution,[],[f78,f2056])).
% 7.47/1.31  fof(f2056,plain,(
% 7.47/1.31    ~r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2)) | spl4_30),
% 7.47/1.31    inference(avatar_component_clause,[],[f2054])).
% 7.47/1.31  fof(f2054,plain,(
% 7.47/1.31    spl4_30 <=> r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2))),
% 7.47/1.31    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 7.47/1.31  fof(f78,plain,(
% 7.47/1.31    ( ! [X2,X5,X1] : (r2_hidden(X5,k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2))) )),
% 7.47/1.31    inference(equality_resolution,[],[f77])).
% 7.47/1.31  fof(f77,plain,(
% 7.47/1.31    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2) != X3) )),
% 7.47/1.31    inference(equality_resolution,[],[f71])).
% 7.47/1.31  fof(f71,plain,(
% 7.47/1.31    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 7.47/1.31    inference(definition_unfolding,[],[f45,f60])).
% 7.47/1.31  fof(f60,plain,(
% 7.47/1.31    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 7.47/1.31    inference(definition_unfolding,[],[f41,f59])).
% 7.47/1.31  fof(f59,plain,(
% 7.47/1.31    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 7.47/1.31    inference(definition_unfolding,[],[f43,f58])).
% 7.47/1.31  fof(f58,plain,(
% 7.47/1.31    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 7.47/1.31    inference(definition_unfolding,[],[f52,f57])).
% 7.47/1.31  fof(f57,plain,(
% 7.47/1.31    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 7.47/1.31    inference(definition_unfolding,[],[f53,f54])).
% 7.47/1.31  fof(f54,plain,(
% 7.47/1.31    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 7.47/1.31    inference(cnf_transformation,[],[f17])).
% 7.47/1.31  fof(f17,axiom,(
% 7.47/1.31    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 7.47/1.31    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 7.47/1.31  fof(f53,plain,(
% 7.47/1.31    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 7.47/1.31    inference(cnf_transformation,[],[f16])).
% 7.47/1.31  fof(f16,axiom,(
% 7.47/1.31    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 7.47/1.31    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 7.47/1.31  fof(f52,plain,(
% 7.47/1.31    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 7.47/1.31    inference(cnf_transformation,[],[f15])).
% 7.47/1.31  fof(f15,axiom,(
% 7.47/1.31    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 7.47/1.31    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 7.47/1.31  fof(f43,plain,(
% 7.47/1.31    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 7.47/1.31    inference(cnf_transformation,[],[f14])).
% 7.47/1.31  fof(f14,axiom,(
% 7.47/1.31    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 7.47/1.31    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 7.47/1.31  fof(f41,plain,(
% 7.47/1.31    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.47/1.31    inference(cnf_transformation,[],[f13])).
% 7.47/1.31  fof(f13,axiom,(
% 7.47/1.31    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.47/1.31    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 7.47/1.31  fof(f45,plain,(
% 7.47/1.31    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 7.47/1.31    inference(cnf_transformation,[],[f29])).
% 7.47/1.31  fof(f29,plain,(
% 7.47/1.31    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.47/1.31    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f28])).
% 7.47/1.31  fof(f28,plain,(
% 7.47/1.31    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3))))),
% 7.47/1.31    introduced(choice_axiom,[])).
% 7.47/1.31  fof(f27,plain,(
% 7.47/1.31    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.47/1.31    inference(rectify,[],[f26])).
% 7.47/1.31  fof(f26,plain,(
% 7.47/1.31    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.47/1.31    inference(flattening,[],[f25])).
% 7.47/1.31  fof(f25,plain,(
% 7.47/1.31    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.47/1.31    inference(nnf_transformation,[],[f22])).
% 7.47/1.31  fof(f22,plain,(
% 7.47/1.31    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 7.47/1.31    inference(ennf_transformation,[],[f9])).
% 7.47/1.31  fof(f9,axiom,(
% 7.47/1.31    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 7.47/1.31    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 7.47/1.31  fof(f3061,plain,(
% 7.47/1.31    spl4_30),
% 7.47/1.31    inference(avatar_contradiction_clause,[],[f3056])).
% 7.47/1.31  fof(f3056,plain,(
% 7.47/1.31    $false | spl4_30),
% 7.47/1.31    inference(resolution,[],[f2056,f78])).
% 7.47/1.31  fof(f2072,plain,(
% 7.47/1.31    ~spl4_33 | spl4_8 | ~spl4_23),
% 7.47/1.31    inference(avatar_split_clause,[],[f2007,f1850,f286,f2069])).
% 7.47/1.31  fof(f2069,plain,(
% 7.47/1.31    spl4_33 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2)),
% 7.47/1.31    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 7.47/1.31  fof(f286,plain,(
% 7.47/1.31    spl4_8 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),
% 7.47/1.31    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 7.47/1.31  fof(f1850,plain,(
% 7.47/1.31    spl4_23 <=> k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2)),
% 7.47/1.31    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 7.47/1.31  fof(f2007,plain,(
% 7.47/1.31    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) | (spl4_8 | ~spl4_23)),
% 7.47/1.31    inference(superposition,[],[f287,f1852])).
% 7.47/1.31  fof(f1852,plain,(
% 7.47/1.31    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) | ~spl4_23),
% 7.47/1.31    inference(avatar_component_clause,[],[f1850])).
% 7.47/1.31  fof(f287,plain,(
% 7.47/1.31    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) | spl4_8),
% 7.47/1.31    inference(avatar_component_clause,[],[f286])).
% 7.47/1.31  fof(f2067,plain,(
% 7.47/1.31    ~spl4_32 | spl4_7 | ~spl4_23),
% 7.47/1.31    inference(avatar_split_clause,[],[f2006,f1850,f282,f2064])).
% 7.47/1.31  fof(f2064,plain,(
% 7.47/1.31    spl4_32 <=> r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),
% 7.47/1.31    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 7.47/1.31  fof(f282,plain,(
% 7.47/1.31    spl4_7 <=> r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),
% 7.47/1.31    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 7.47/1.31  fof(f2006,plain,(
% 7.47/1.31    ~r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | (spl4_7 | ~spl4_23)),
% 7.47/1.31    inference(superposition,[],[f284,f1852])).
% 7.47/1.31  fof(f284,plain,(
% 7.47/1.31    ~r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | spl4_7),
% 7.47/1.31    inference(avatar_component_clause,[],[f282])).
% 7.47/1.31  fof(f2062,plain,(
% 7.47/1.31    spl4_31 | ~spl4_6 | ~spl4_23),
% 7.47/1.31    inference(avatar_split_clause,[],[f2005,f1850,f277,f2059])).
% 7.47/1.31  fof(f2059,plain,(
% 7.47/1.31    spl4_31 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),
% 7.47/1.31    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 7.47/1.31  fof(f277,plain,(
% 7.47/1.31    spl4_6 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),
% 7.47/1.31    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 7.47/1.31  fof(f2005,plain,(
% 7.47/1.31    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | (~spl4_6 | ~spl4_23)),
% 7.47/1.31    inference(superposition,[],[f279,f1852])).
% 7.47/1.31  fof(f279,plain,(
% 7.47/1.31    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~spl4_6),
% 7.47/1.31    inference(avatar_component_clause,[],[f277])).
% 7.47/1.31  fof(f2057,plain,(
% 7.47/1.31    ~spl4_30 | spl4_4 | ~spl4_23),
% 7.47/1.31    inference(avatar_split_clause,[],[f1998,f1850,f132,f2054])).
% 7.47/1.31  fof(f132,plain,(
% 7.47/1.31    spl4_4 <=> r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),
% 7.47/1.31    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 7.47/1.31  fof(f1998,plain,(
% 7.47/1.31    ~r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2)) | (spl4_4 | ~spl4_23)),
% 7.47/1.31    inference(superposition,[],[f134,f1852])).
% 7.47/1.31  fof(f134,plain,(
% 7.47/1.31    ~r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | spl4_4),
% 7.47/1.31    inference(avatar_component_clause,[],[f132])).
% 7.47/1.31  fof(f2052,plain,(
% 7.47/1.31    spl4_29 | ~spl4_3 | ~spl4_23),
% 7.47/1.31    inference(avatar_split_clause,[],[f1997,f1850,f100,f2049])).
% 7.47/1.31  fof(f2049,plain,(
% 7.47/1.31    spl4_29 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2))),
% 7.47/1.31    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 7.47/1.31  fof(f100,plain,(
% 7.47/1.31    spl4_3 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),
% 7.47/1.31    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 7.47/1.31  fof(f1997,plain,(
% 7.47/1.31    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2)) | (~spl4_3 | ~spl4_23)),
% 7.47/1.31    inference(superposition,[],[f102,f1852])).
% 7.47/1.31  fof(f102,plain,(
% 7.47/1.31    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | ~spl4_3),
% 7.47/1.31    inference(avatar_component_clause,[],[f100])).
% 7.47/1.31  fof(f2047,plain,(
% 7.47/1.31    spl4_28 | ~spl4_2 | ~spl4_23),
% 7.47/1.31    inference(avatar_split_clause,[],[f1996,f1850,f86,f2044])).
% 7.47/1.31  fof(f2044,plain,(
% 7.47/1.31    spl4_28 <=> r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2))),
% 7.47/1.31    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 7.47/1.31  fof(f86,plain,(
% 7.47/1.31    spl4_2 <=> r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),
% 7.47/1.31    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 7.47/1.31  fof(f1996,plain,(
% 7.47/1.31    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2)) | (~spl4_2 | ~spl4_23)),
% 7.47/1.31    inference(superposition,[],[f88,f1852])).
% 7.47/1.31  fof(f88,plain,(
% 7.47/1.31    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | ~spl4_2),
% 7.47/1.31    inference(avatar_component_clause,[],[f86])).
% 7.47/1.31  fof(f1886,plain,(
% 7.47/1.31    spl4_27 | ~spl4_9),
% 7.47/1.31    inference(avatar_split_clause,[],[f1842,f1136,f1883])).
% 7.47/1.31  fof(f1883,plain,(
% 7.47/1.31    spl4_27 <=> k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2))),
% 7.47/1.31    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 7.47/1.31  fof(f1136,plain,(
% 7.47/1.31    spl4_9 <=> k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2)),
% 7.47/1.31    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 7.47/1.31  fof(f1842,plain,(
% 7.47/1.31    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2)) | ~spl4_9),
% 7.47/1.31    inference(superposition,[],[f117,f1138])).
% 7.47/1.31  fof(f1138,plain,(
% 7.47/1.31    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) | ~spl4_9),
% 7.47/1.31    inference(avatar_component_clause,[],[f1136])).
% 7.47/1.31  fof(f117,plain,(
% 7.47/1.31    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 7.47/1.31    inference(forward_demodulation,[],[f104,f90])).
% 7.47/1.31  fof(f90,plain,(
% 7.47/1.31    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 7.47/1.31    inference(superposition,[],[f36,f33])).
% 7.47/1.31  fof(f33,plain,(
% 7.47/1.31    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.47/1.31    inference(cnf_transformation,[],[f5])).
% 7.47/1.32  fof(f5,axiom,(
% 7.47/1.32    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 7.47/1.32    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 7.47/1.32  fof(f36,plain,(
% 7.47/1.32    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 7.47/1.32    inference(cnf_transformation,[],[f2])).
% 7.47/1.32  fof(f2,axiom,(
% 7.47/1.32    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 7.47/1.32    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 7.47/1.32  fof(f104,plain,(
% 7.47/1.32    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 7.47/1.32    inference(superposition,[],[f42,f32])).
% 7.47/1.32  fof(f32,plain,(
% 7.47/1.32    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 7.47/1.32    inference(cnf_transformation,[],[f7])).
% 7.47/1.32  fof(f7,axiom,(
% 7.47/1.32    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 7.47/1.32    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 7.47/1.32  fof(f42,plain,(
% 7.47/1.32    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 7.47/1.32    inference(cnf_transformation,[],[f6])).
% 7.47/1.32  fof(f6,axiom,(
% 7.47/1.32    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 7.47/1.32    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 7.47/1.32  fof(f1880,plain,(
% 7.47/1.32    spl4_26 | ~spl4_9),
% 7.47/1.32    inference(avatar_split_clause,[],[f1875,f1136,f1877])).
% 7.47/1.32  fof(f1877,plain,(
% 7.47/1.32    spl4_26 <=> k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))),
% 7.47/1.32    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 7.47/1.32  fof(f1875,plain,(
% 7.47/1.32    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) | ~spl4_9),
% 7.47/1.32    inference(forward_demodulation,[],[f1874,f36])).
% 7.47/1.32  fof(f1874,plain,(
% 7.47/1.32    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2)))) | ~spl4_9),
% 7.47/1.32    inference(forward_demodulation,[],[f1873,f111])).
% 7.47/1.32  fof(f111,plain,(
% 7.47/1.32    ( ! [X8,X7,X9] : (k5_xboole_0(X7,k5_xboole_0(X8,X9)) = k5_xboole_0(X9,k5_xboole_0(X7,X8))) )),
% 7.47/1.32    inference(superposition,[],[f42,f36])).
% 7.47/1.32  fof(f1873,plain,(
% 7.47/1.32    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) | ~spl4_9),
% 7.47/1.32    inference(forward_demodulation,[],[f1839,f36])).
% 7.47/1.32  fof(f1839,plain,(
% 7.47/1.32    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2))) | ~spl4_9),
% 7.47/1.32    inference(superposition,[],[f109,f1138])).
% 7.47/1.32  fof(f109,plain,(
% 7.47/1.32    ( ! [X4,X3] : (k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4)))) )),
% 7.47/1.32    inference(superposition,[],[f42,f32])).
% 7.47/1.32  fof(f1871,plain,(
% 7.47/1.32    spl4_23 | ~spl4_9),
% 7.47/1.32    inference(avatar_split_clause,[],[f1836,f1136,f1850])).
% 7.47/1.32  fof(f1836,plain,(
% 7.47/1.32    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) | ~spl4_9),
% 7.47/1.32    inference(superposition,[],[f117,f1138])).
% 7.47/1.32  fof(f1870,plain,(
% 7.47/1.32    spl4_23 | ~spl4_9),
% 7.47/1.32    inference(avatar_split_clause,[],[f1835,f1136,f1850])).
% 7.47/1.32  fof(f1835,plain,(
% 7.47/1.32    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) | ~spl4_9),
% 7.47/1.32    inference(superposition,[],[f1138,f117])).
% 7.47/1.32  fof(f1865,plain,(
% 7.47/1.32    spl4_25 | spl4_23 | ~spl4_9),
% 7.47/1.32    inference(avatar_split_clause,[],[f1861,f1136,f1850,f1863])).
% 7.47/1.32  fof(f1863,plain,(
% 7.47/1.32    spl4_25 <=> ! [X3] : (sK1 != sK3(sK0,sK0,sK1,X3) | ~r2_hidden(sK3(sK0,sK0,sK1,X3),X3))),
% 7.47/1.32    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 7.47/1.32  fof(f1861,plain,(
% 7.47/1.32    ( ! [X3] : (k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) | sK1 != sK3(sK0,sK0,sK1,X3) | ~r2_hidden(sK3(sK0,sK0,sK1,X3),X3)) ) | ~spl4_9),
% 7.47/1.32    inference(forward_demodulation,[],[f1830,f117])).
% 7.47/1.32  fof(f1830,plain,(
% 7.47/1.32    ( ! [X3] : (k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(X3,k5_xboole_0(X3,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) | sK1 != sK3(sK0,sK0,sK1,X3) | ~r2_hidden(sK3(sK0,sK0,sK1,X3),X3)) ) | ~spl4_9),
% 7.47/1.32    inference(superposition,[],[f1138,f65])).
% 7.47/1.32  fof(f65,plain,(
% 7.47/1.32    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = X3 | sK3(X0,X1,X2,X3) != X2 | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) )),
% 7.47/1.32    inference(definition_unfolding,[],[f51,f60])).
% 7.47/1.32  fof(f51,plain,(
% 7.47/1.32    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | sK3(X0,X1,X2,X3) != X2 | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) )),
% 7.47/1.32    inference(cnf_transformation,[],[f29])).
% 7.47/1.32  fof(f1860,plain,(
% 7.47/1.32    spl4_24 | spl4_23 | ~spl4_9),
% 7.47/1.32    inference(avatar_split_clause,[],[f1859,f1136,f1850,f1856])).
% 7.47/1.32  fof(f1856,plain,(
% 7.47/1.32    spl4_24 <=> ! [X1] : (sK0 != sK3(sK0,sK0,sK1,X1) | ~r2_hidden(sK3(sK0,sK0,sK1,X1),X1))),
% 7.47/1.32    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 7.47/1.32  fof(f1859,plain,(
% 7.47/1.32    ( ! [X2] : (k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) | sK0 != sK3(sK0,sK0,sK1,X2) | ~r2_hidden(sK3(sK0,sK0,sK1,X2),X2)) ) | ~spl4_9),
% 7.47/1.32    inference(forward_demodulation,[],[f1829,f117])).
% 7.47/1.32  fof(f1829,plain,(
% 7.47/1.32    ( ! [X2] : (k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(X2,k5_xboole_0(X2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) | sK0 != sK3(sK0,sK0,sK1,X2) | ~r2_hidden(sK3(sK0,sK0,sK1,X2),X2)) ) | ~spl4_9),
% 7.47/1.32    inference(superposition,[],[f1138,f66])).
% 7.47/1.32  fof(f66,plain,(
% 7.47/1.32    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = X3 | sK3(X0,X1,X2,X3) != X1 | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) )),
% 7.47/1.32    inference(definition_unfolding,[],[f50,f60])).
% 7.47/1.32  fof(f50,plain,(
% 7.47/1.32    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | sK3(X0,X1,X2,X3) != X1 | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) )),
% 7.47/1.32    inference(cnf_transformation,[],[f29])).
% 7.47/1.32  fof(f1858,plain,(
% 7.47/1.32    spl4_24 | spl4_23 | ~spl4_9),
% 7.47/1.32    inference(avatar_split_clause,[],[f1854,f1136,f1850,f1856])).
% 7.47/1.32  fof(f1854,plain,(
% 7.47/1.32    ( ! [X1] : (k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) | sK0 != sK3(sK0,sK0,sK1,X1) | ~r2_hidden(sK3(sK0,sK0,sK1,X1),X1)) ) | ~spl4_9),
% 7.47/1.32    inference(forward_demodulation,[],[f1828,f117])).
% 7.47/1.32  fof(f1828,plain,(
% 7.47/1.32    ( ! [X1] : (k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(X1,k5_xboole_0(X1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) | sK0 != sK3(sK0,sK0,sK1,X1) | ~r2_hidden(sK3(sK0,sK0,sK1,X1),X1)) ) | ~spl4_9),
% 7.47/1.32    inference(superposition,[],[f1138,f67])).
% 7.47/1.32  fof(f67,plain,(
% 7.47/1.32    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = X3 | sK3(X0,X1,X2,X3) != X0 | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) )),
% 7.47/1.32    inference(definition_unfolding,[],[f49,f60])).
% 7.47/1.32  fof(f49,plain,(
% 7.47/1.32    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | sK3(X0,X1,X2,X3) != X0 | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) )),
% 7.47/1.32    inference(cnf_transformation,[],[f29])).
% 7.47/1.32  fof(f1853,plain,(
% 7.47/1.32    spl4_22 | spl4_23 | ~spl4_9),
% 7.47/1.32    inference(avatar_split_clause,[],[f1845,f1136,f1850,f1847])).
% 7.47/1.32  fof(f1847,plain,(
% 7.47/1.32    spl4_22 <=> ! [X0] : (sK1 = sK3(sK0,sK0,sK1,X0) | r2_hidden(sK3(sK0,sK0,sK1,X0),X0) | sK0 = sK3(sK0,sK0,sK1,X0))),
% 7.47/1.32    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 7.47/1.32  fof(f1845,plain,(
% 7.47/1.32    ( ! [X0] : (k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) | sK1 = sK3(sK0,sK0,sK1,X0) | sK0 = sK3(sK0,sK0,sK1,X0) | r2_hidden(sK3(sK0,sK0,sK1,X0),X0)) ) | ~spl4_9),
% 7.47/1.32    inference(forward_demodulation,[],[f1844,f117])).
% 7.47/1.32  fof(f1844,plain,(
% 7.47/1.32    ( ! [X0] : (k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(X0,k5_xboole_0(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) | sK1 = sK3(sK0,sK0,sK1,X0) | sK0 = sK3(sK0,sK0,sK1,X0) | r2_hidden(sK3(sK0,sK0,sK1,X0),X0)) ) | ~spl4_9),
% 7.47/1.32    inference(duplicate_literal_removal,[],[f1827])).
% 7.47/1.32  fof(f1827,plain,(
% 7.47/1.32    ( ! [X0] : (k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(X0,k5_xboole_0(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) | sK1 = sK3(sK0,sK0,sK1,X0) | sK0 = sK3(sK0,sK0,sK1,X0) | sK0 = sK3(sK0,sK0,sK1,X0) | r2_hidden(sK3(sK0,sK0,sK1,X0),X0)) ) | ~spl4_9),
% 7.47/1.32    inference(superposition,[],[f1138,f68])).
% 7.47/1.32  fof(f68,plain,(
% 7.47/1.32    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = X3 | sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3)) )),
% 7.47/1.32    inference(definition_unfolding,[],[f48,f60])).
% 7.47/1.32  fof(f48,plain,(
% 7.47/1.32    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3)) )),
% 7.47/1.32    inference(cnf_transformation,[],[f29])).
% 7.47/1.32  fof(f1760,plain,(
% 7.47/1.32    spl4_12 | spl4_4 | spl4_13),
% 7.47/1.32    inference(avatar_split_clause,[],[f1662,f1445,f132,f1441])).
% 7.47/1.32  fof(f1441,plain,(
% 7.47/1.32    spl4_12 <=> r2_hidden(sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),
% 7.47/1.32    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 7.47/1.32  fof(f1445,plain,(
% 7.47/1.32    spl4_13 <=> sK2 = sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),
% 7.47/1.32    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 7.47/1.32  fof(f1662,plain,(
% 7.47/1.32    r2_hidden(sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | (spl4_4 | spl4_13)),
% 7.47/1.32    inference(unit_resulting_resolution,[],[f76,f1447,f213])).
% 7.47/1.32  fof(f213,plain,(
% 7.47/1.32    ( ! [X0] : (r2_hidden(sK3(sK2,sK2,sK2,X0),X0) | sK2 = sK3(sK2,sK2,sK2,X0) | ~r2_hidden(sK0,X0)) ) | spl4_4),
% 7.47/1.32    inference(duplicate_literal_removal,[],[f209])).
% 7.47/1.32  fof(f209,plain,(
% 7.47/1.32    ( ! [X0] : (~r2_hidden(sK0,X0) | sK2 = sK3(sK2,sK2,sK2,X0) | sK2 = sK3(sK2,sK2,sK2,X0) | sK2 = sK3(sK2,sK2,sK2,X0) | r2_hidden(sK3(sK2,sK2,sK2,X0),X0)) ) | spl4_4),
% 7.47/1.32    inference(superposition,[],[f134,f68])).
% 7.47/1.32  fof(f1447,plain,(
% 7.47/1.32    sK2 != sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | spl4_13),
% 7.47/1.32    inference(avatar_component_clause,[],[f1445])).
% 7.47/1.32  fof(f76,plain,(
% 7.47/1.32    ( ! [X2,X0,X5] : (r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2))) )),
% 7.47/1.32    inference(equality_resolution,[],[f75])).
% 7.47/1.32  fof(f75,plain,(
% 7.47/1.32    ( ! [X2,X0,X5,X3] : (r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X5,X2) != X3) )),
% 7.47/1.32    inference(equality_resolution,[],[f70])).
% 7.47/1.32  fof(f70,plain,(
% 7.47/1.32    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 7.47/1.32    inference(definition_unfolding,[],[f46,f60])).
% 7.47/1.32  fof(f46,plain,(
% 7.47/1.32    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 7.47/1.32    inference(cnf_transformation,[],[f29])).
% 7.47/1.32  fof(f1759,plain,(
% 7.47/1.32    ~spl4_21 | spl4_13),
% 7.47/1.32    inference(avatar_split_clause,[],[f1663,f1445,f1754])).
% 7.47/1.32  fof(f1754,plain,(
% 7.47/1.32    spl4_21 <=> r2_hidden(sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),
% 7.47/1.32    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 7.47/1.32  fof(f1663,plain,(
% 7.47/1.32    ~r2_hidden(sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | spl4_13),
% 7.47/1.32    inference(unit_resulting_resolution,[],[f1447,f1447,f1447,f79])).
% 7.47/1.32  fof(f79,plain,(
% 7.47/1.32    ( ! [X2,X0,X5,X1] : (~r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) | X1 = X5 | X0 = X5 | X2 = X5) )),
% 7.47/1.32    inference(equality_resolution,[],[f72])).
% 7.47/1.32  fof(f72,plain,(
% 7.47/1.32    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 7.47/1.32    inference(definition_unfolding,[],[f44,f60])).
% 7.47/1.32  fof(f44,plain,(
% 7.47/1.32    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 7.47/1.32    inference(cnf_transformation,[],[f29])).
% 7.47/1.32  fof(f1758,plain,(
% 7.47/1.32    ~spl4_21 | spl4_13),
% 7.47/1.32    inference(avatar_split_clause,[],[f1666,f1445,f1754])).
% 7.47/1.32  fof(f1666,plain,(
% 7.47/1.32    ~r2_hidden(sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | spl4_13),
% 7.47/1.32    inference(unit_resulting_resolution,[],[f1447,f1447,f1447,f79])).
% 7.47/1.32  fof(f1757,plain,(
% 7.47/1.32    ~spl4_21 | spl4_13),
% 7.47/1.32    inference(avatar_split_clause,[],[f1669,f1445,f1754])).
% 7.47/1.32  fof(f1669,plain,(
% 7.47/1.32    ~r2_hidden(sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | spl4_13),
% 7.47/1.32    inference(unit_resulting_resolution,[],[f1447,f1447,f1447,f79])).
% 7.47/1.32  fof(f1752,plain,(
% 7.47/1.32    spl4_12 | spl4_8 | spl4_13),
% 7.47/1.32    inference(avatar_split_clause,[],[f1672,f1445,f286,f1441])).
% 7.47/1.32  fof(f1672,plain,(
% 7.47/1.32    r2_hidden(sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | (spl4_8 | spl4_13)),
% 7.47/1.32    inference(unit_resulting_resolution,[],[f1447,f1447,f287,f1447,f68])).
% 7.47/1.32  fof(f1751,plain,(
% 7.47/1.32    spl4_12 | spl4_1 | spl4_13),
% 7.47/1.32    inference(avatar_split_clause,[],[f1673,f1445,f81,f1441])).
% 7.47/1.32  fof(f81,plain,(
% 7.47/1.32    spl4_1 <=> sK0 = sK2),
% 7.47/1.32    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 7.47/1.32  fof(f1673,plain,(
% 7.47/1.32    r2_hidden(sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | (spl4_1 | spl4_13)),
% 7.47/1.32    inference(unit_resulting_resolution,[],[f83,f83,f83,f76,f1447,f1447,f1447,f188])).
% 7.47/1.32  fof(f188,plain,(
% 7.47/1.32    ( ! [X35,X33,X31,X34,X32] : (r2_hidden(sK3(X31,X32,X33,X34),X34) | X32 = X35 | X31 = X35 | X33 = X35 | sK3(X31,X32,X33,X34) = X33 | sK3(X31,X32,X33,X34) = X32 | sK3(X31,X32,X33,X34) = X31 | ~r2_hidden(X35,X34)) )),
% 7.47/1.32    inference(superposition,[],[f79,f68])).
% 7.47/1.32  fof(f83,plain,(
% 7.47/1.32    sK0 != sK2 | spl4_1),
% 7.47/1.32    inference(avatar_component_clause,[],[f81])).
% 7.47/1.32  fof(f1750,plain,(
% 7.47/1.32    spl4_12 | spl4_1 | spl4_13),
% 7.47/1.32    inference(avatar_split_clause,[],[f1674,f1445,f81,f1441])).
% 7.47/1.32  fof(f1674,plain,(
% 7.47/1.32    r2_hidden(sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | (spl4_1 | spl4_13)),
% 7.47/1.32    inference(unit_resulting_resolution,[],[f83,f83,f83,f78,f1447,f1447,f1447,f188])).
% 7.47/1.32  fof(f1749,plain,(
% 7.47/1.32    spl4_12 | spl4_8 | spl4_13),
% 7.47/1.32    inference(avatar_split_clause,[],[f1675,f1445,f286,f1441])).
% 7.47/1.32  fof(f1675,plain,(
% 7.47/1.32    r2_hidden(sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | (spl4_8 | spl4_13)),
% 7.47/1.32    inference(unit_resulting_resolution,[],[f1447,f1447,f287,f1447,f68])).
% 7.47/1.32  fof(f1748,plain,(
% 7.47/1.32    spl4_12 | spl4_1 | spl4_13),
% 7.47/1.32    inference(avatar_split_clause,[],[f1676,f1445,f81,f1441])).
% 7.47/1.32  fof(f1676,plain,(
% 7.47/1.32    r2_hidden(sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | (spl4_1 | spl4_13)),
% 7.47/1.32    inference(unit_resulting_resolution,[],[f83,f83,f83,f76,f1447,f1447,f1447,f188])).
% 7.47/1.32  fof(f1747,plain,(
% 7.47/1.32    spl4_12 | spl4_1 | spl4_13),
% 7.47/1.32    inference(avatar_split_clause,[],[f1677,f1445,f81,f1441])).
% 7.47/1.32  fof(f1677,plain,(
% 7.47/1.32    r2_hidden(sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | (spl4_1 | spl4_13)),
% 7.47/1.32    inference(unit_resulting_resolution,[],[f83,f83,f83,f78,f1447,f1447,f1447,f188])).
% 7.47/1.32  fof(f1746,plain,(
% 7.47/1.32    spl4_12 | spl4_8 | spl4_13),
% 7.47/1.32    inference(avatar_split_clause,[],[f1678,f1445,f286,f1441])).
% 7.47/1.32  fof(f1678,plain,(
% 7.47/1.32    r2_hidden(sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | (spl4_8 | spl4_13)),
% 7.47/1.32    inference(unit_resulting_resolution,[],[f1447,f1447,f287,f1447,f68])).
% 7.47/1.32  fof(f1745,plain,(
% 7.47/1.32    spl4_12 | spl4_1 | spl4_13),
% 7.47/1.32    inference(avatar_split_clause,[],[f1679,f1445,f81,f1441])).
% 7.47/1.32  fof(f1679,plain,(
% 7.47/1.32    r2_hidden(sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | (spl4_1 | spl4_13)),
% 7.47/1.32    inference(unit_resulting_resolution,[],[f83,f83,f83,f76,f1447,f1447,f1447,f188])).
% 7.47/1.32  fof(f1744,plain,(
% 7.47/1.32    spl4_12 | spl4_1 | spl4_13),
% 7.47/1.32    inference(avatar_split_clause,[],[f1680,f1445,f81,f1441])).
% 7.47/1.32  fof(f1680,plain,(
% 7.47/1.32    r2_hidden(sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | (spl4_1 | spl4_13)),
% 7.47/1.32    inference(unit_resulting_resolution,[],[f83,f83,f83,f78,f1447,f1447,f1447,f188])).
% 7.47/1.32  fof(f1743,plain,(
% 7.47/1.32    ~spl4_17 | spl4_13),
% 7.47/1.32    inference(avatar_split_clause,[],[f1681,f1445,f1720])).
% 7.47/1.32  fof(f1720,plain,(
% 7.47/1.32    spl4_17 <=> r2_hidden(sK2,k6_enumset1(sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))),
% 7.47/1.32    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 7.47/1.32  fof(f1681,plain,(
% 7.47/1.32    ~r2_hidden(sK2,k6_enumset1(sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) | spl4_13),
% 7.47/1.32    inference(unit_resulting_resolution,[],[f1447,f1447,f1447,f79])).
% 7.47/1.32  fof(f1742,plain,(
% 7.47/1.32    ~spl4_15 | spl4_1 | spl4_13),
% 7.47/1.32    inference(avatar_split_clause,[],[f1682,f1445,f81,f1710])).
% 7.47/1.32  fof(f1710,plain,(
% 7.47/1.32    spl4_15 <=> r2_hidden(sK2,k6_enumset1(sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK0,sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))),
% 7.47/1.32    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 7.47/1.32  fof(f1682,plain,(
% 7.47/1.32    ~r2_hidden(sK2,k6_enumset1(sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK0,sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) | (spl4_1 | spl4_13)),
% 7.47/1.32    inference(unit_resulting_resolution,[],[f83,f1447,f1447,f79])).
% 7.47/1.32  fof(f1741,plain,(
% 7.47/1.32    ~spl4_19 | spl4_1 | spl4_13),
% 7.47/1.32    inference(avatar_split_clause,[],[f1683,f1445,f81,f1730])).
% 7.47/1.32  fof(f1730,plain,(
% 7.47/1.32    spl4_19 <=> r2_hidden(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))),
% 7.47/1.32    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 7.47/1.32  fof(f1683,plain,(
% 7.47/1.32    ~r2_hidden(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) | (spl4_1 | spl4_13)),
% 7.47/1.32    inference(unit_resulting_resolution,[],[f1447,f83,f1447,f79])).
% 7.47/1.32  fof(f1740,plain,(
% 7.47/1.32    ~spl4_20 | spl4_1 | spl4_13),
% 7.47/1.32    inference(avatar_split_clause,[],[f1684,f1445,f81,f1737])).
% 7.47/1.32  fof(f1737,plain,(
% 7.47/1.32    spl4_20 <=> r2_hidden(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))),
% 7.47/1.32    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 7.47/1.32  fof(f1684,plain,(
% 7.47/1.32    ~r2_hidden(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) | (spl4_1 | spl4_13)),
% 7.47/1.32    inference(unit_resulting_resolution,[],[f83,f83,f1447,f79])).
% 7.47/1.32  fof(f1735,plain,(
% 7.47/1.32    ~spl4_17 | spl4_13),
% 7.47/1.32    inference(avatar_split_clause,[],[f1687,f1445,f1720])).
% 7.47/1.32  fof(f1687,plain,(
% 7.47/1.32    ~r2_hidden(sK2,k6_enumset1(sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) | spl4_13),
% 7.47/1.32    inference(unit_resulting_resolution,[],[f1447,f1447,f1447,f79])).
% 7.47/1.32  fof(f1734,plain,(
% 7.47/1.32    ~spl4_16 | spl4_1 | spl4_13),
% 7.47/1.32    inference(avatar_split_clause,[],[f1688,f1445,f81,f1715])).
% 7.47/1.32  fof(f1715,plain,(
% 7.47/1.32    spl4_16 <=> r2_hidden(sK2,k6_enumset1(sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK0))),
% 7.47/1.32    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 7.47/1.32  fof(f1688,plain,(
% 7.47/1.32    ~r2_hidden(sK2,k6_enumset1(sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK0)) | (spl4_1 | spl4_13)),
% 7.47/1.32    inference(unit_resulting_resolution,[],[f83,f1447,f1447,f79])).
% 7.47/1.32  fof(f1733,plain,(
% 7.47/1.32    ~spl4_19 | spl4_1 | spl4_13),
% 7.47/1.32    inference(avatar_split_clause,[],[f1689,f1445,f81,f1730])).
% 7.47/1.32  fof(f1689,plain,(
% 7.47/1.32    ~r2_hidden(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) | (spl4_1 | spl4_13)),
% 7.47/1.32    inference(unit_resulting_resolution,[],[f1447,f83,f1447,f79])).
% 7.47/1.32  fof(f1728,plain,(
% 7.47/1.32    ~spl4_18 | spl4_1 | spl4_13),
% 7.47/1.32    inference(avatar_split_clause,[],[f1690,f1445,f81,f1725])).
% 7.47/1.32  fof(f1725,plain,(
% 7.47/1.32    spl4_18 <=> r2_hidden(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK0))),
% 7.47/1.32    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 7.47/1.32  fof(f1690,plain,(
% 7.47/1.32    ~r2_hidden(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK0)) | (spl4_1 | spl4_13)),
% 7.47/1.32    inference(unit_resulting_resolution,[],[f83,f83,f1447,f79])).
% 7.47/1.32  fof(f1723,plain,(
% 7.47/1.32    ~spl4_17 | spl4_13),
% 7.47/1.32    inference(avatar_split_clause,[],[f1693,f1445,f1720])).
% 7.47/1.32  fof(f1693,plain,(
% 7.47/1.32    ~r2_hidden(sK2,k6_enumset1(sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) | spl4_13),
% 7.47/1.32    inference(unit_resulting_resolution,[],[f1447,f1447,f1447,f79])).
% 7.47/1.32  fof(f1718,plain,(
% 7.47/1.32    ~spl4_16 | spl4_1 | spl4_13),
% 7.47/1.32    inference(avatar_split_clause,[],[f1694,f1445,f81,f1715])).
% 7.47/1.32  fof(f1694,plain,(
% 7.47/1.32    ~r2_hidden(sK2,k6_enumset1(sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK0)) | (spl4_1 | spl4_13)),
% 7.47/1.32    inference(unit_resulting_resolution,[],[f83,f1447,f1447,f79])).
% 7.47/1.32  fof(f1713,plain,(
% 7.47/1.32    ~spl4_15 | spl4_1 | spl4_13),
% 7.47/1.32    inference(avatar_split_clause,[],[f1695,f1445,f81,f1710])).
% 7.47/1.32  fof(f1695,plain,(
% 7.47/1.32    ~r2_hidden(sK2,k6_enumset1(sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK0,sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) | (spl4_1 | spl4_13)),
% 7.47/1.32    inference(unit_resulting_resolution,[],[f1447,f83,f1447,f79])).
% 7.47/1.32  fof(f1708,plain,(
% 7.47/1.32    ~spl4_14 | spl4_1 | spl4_13),
% 7.47/1.32    inference(avatar_split_clause,[],[f1696,f1445,f81,f1705])).
% 7.47/1.32  fof(f1705,plain,(
% 7.47/1.32    spl4_14 <=> r2_hidden(sK2,k6_enumset1(sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK0,sK0))),
% 7.47/1.32    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 7.47/1.32  fof(f1696,plain,(
% 7.47/1.32    ~r2_hidden(sK2,k6_enumset1(sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK0,sK0)) | (spl4_1 | spl4_13)),
% 7.47/1.32    inference(unit_resulting_resolution,[],[f83,f83,f1447,f79])).
% 7.47/1.32  fof(f1448,plain,(
% 7.47/1.32    ~spl4_12 | ~spl4_13 | ~spl4_2 | spl4_7),
% 7.47/1.32    inference(avatar_split_clause,[],[f1439,f282,f86,f1445,f1441])).
% 7.47/1.32  fof(f1439,plain,(
% 7.47/1.32    sK2 != sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~r2_hidden(sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | (~spl4_2 | spl4_7)),
% 7.47/1.32    inference(duplicate_literal_removal,[],[f1433])).
% 7.47/1.32  fof(f1433,plain,(
% 7.47/1.32    sK2 != sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~r2_hidden(sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | sK2 != sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~r2_hidden(sK3(sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | (~spl4_2 | spl4_7)),
% 7.47/1.32    inference(resolution,[],[f911,f145])).
% 7.47/1.32  fof(f145,plain,(
% 7.47/1.32    ( ! [X3] : (r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),X3) | sK2 != sK3(sK2,sK2,sK2,X3) | ~r2_hidden(sK3(sK2,sK2,sK2,X3),X3)) ) | ~spl4_2),
% 7.47/1.32    inference(superposition,[],[f88,f65])).
% 7.47/1.32  fof(f911,plain,(
% 7.47/1.32    ( ! [X1] : (~r1_tarski(X1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | sK2 != sK3(sK2,sK2,sK2,X1) | ~r2_hidden(sK3(sK2,sK2,sK2,X1),X1)) ) | spl4_7),
% 7.47/1.32    inference(superposition,[],[f284,f67])).
% 7.47/1.32  fof(f1395,plain,(
% 7.47/1.32    ~spl4_11 | spl4_8),
% 7.47/1.32    inference(avatar_split_clause,[],[f1359,f286,f1390])).
% 7.47/1.32  fof(f1390,plain,(
% 7.47/1.32    spl4_11 <=> r2_hidden(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),
% 7.47/1.32    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 7.47/1.32  fof(f1359,plain,(
% 7.47/1.32    ~r2_hidden(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | spl4_8),
% 7.47/1.32    inference(unit_resulting_resolution,[],[f287,f287,f287,f79])).
% 7.47/1.32  fof(f1394,plain,(
% 7.47/1.32    ~spl4_11 | spl4_8),
% 7.47/1.32    inference(avatar_split_clause,[],[f1362,f286,f1390])).
% 7.47/1.32  fof(f1362,plain,(
% 7.47/1.32    ~r2_hidden(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | spl4_8),
% 7.47/1.32    inference(unit_resulting_resolution,[],[f287,f287,f287,f79])).
% 7.47/1.32  fof(f1393,plain,(
% 7.47/1.32    ~spl4_11 | spl4_8),
% 7.47/1.32    inference(avatar_split_clause,[],[f1365,f286,f1390])).
% 7.47/1.32  fof(f1365,plain,(
% 7.47/1.32    ~r2_hidden(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | spl4_8),
% 7.47/1.32    inference(unit_resulting_resolution,[],[f287,f287,f287,f79])).
% 7.47/1.32  fof(f1388,plain,(
% 7.47/1.32    ~spl4_10 | spl4_8),
% 7.47/1.32    inference(avatar_split_clause,[],[f1368,f286,f1383])).
% 7.47/1.32  fof(f1383,plain,(
% 7.47/1.32    spl4_10 <=> r2_hidden(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))),
% 7.47/1.32    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 7.47/1.32  fof(f1368,plain,(
% 7.47/1.32    ~r2_hidden(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) | spl4_8),
% 7.47/1.32    inference(unit_resulting_resolution,[],[f287,f287,f287,f79])).
% 7.47/1.32  fof(f1387,plain,(
% 7.47/1.32    ~spl4_10 | spl4_8),
% 7.47/1.32    inference(avatar_split_clause,[],[f1371,f286,f1383])).
% 7.47/1.32  fof(f1371,plain,(
% 7.47/1.32    ~r2_hidden(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) | spl4_8),
% 7.47/1.32    inference(unit_resulting_resolution,[],[f287,f287,f287,f79])).
% 7.47/1.32  fof(f1386,plain,(
% 7.47/1.32    ~spl4_10 | spl4_8),
% 7.47/1.32    inference(avatar_split_clause,[],[f1374,f286,f1383])).
% 7.47/1.32  fof(f1374,plain,(
% 7.47/1.32    ~r2_hidden(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) | spl4_8),
% 7.47/1.32    inference(unit_resulting_resolution,[],[f287,f287,f287,f79])).
% 7.47/1.32  fof(f1139,plain,(
% 7.47/1.32    spl4_9 | ~spl4_3),
% 7.47/1.32    inference(avatar_split_clause,[],[f1134,f100,f1136])).
% 7.47/1.32  fof(f1134,plain,(
% 7.47/1.32    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) | ~spl4_3),
% 7.47/1.32    inference(forward_demodulation,[],[f1098,f36])).
% 7.47/1.32  fof(f1098,plain,(
% 7.47/1.32    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) | ~spl4_3),
% 7.47/1.32    inference(superposition,[],[f202,f102])).
% 7.47/1.32  fof(f202,plain,(
% 7.47/1.32    ( ! [X14,X12,X10,X8,X15,X13,X11,X9] : (k6_enumset1(X9,X10,X11,X12,X13,X14,X15,X8) = k5_xboole_0(k6_enumset1(X9,X9,X10,X11,X12,X13,X14,X15),k5_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k3_xboole_0(k6_enumset1(X9,X9,X10,X11,X12,X13,X14,X15),k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8))))) )),
% 7.47/1.32    inference(superposition,[],[f63,f35])).
% 7.47/1.32  fof(f35,plain,(
% 7.47/1.32    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.47/1.32    inference(cnf_transformation,[],[f1])).
% 7.47/1.32  fof(f1,axiom,(
% 7.47/1.32    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.47/1.32    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 7.47/1.32  fof(f63,plain,(
% 7.47/1.32    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6))))) )),
% 7.47/1.32    inference(definition_unfolding,[],[f55,f56,f54,f62])).
% 7.47/1.32  fof(f62,plain,(
% 7.47/1.32    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 7.47/1.32    inference(definition_unfolding,[],[f34,f61])).
% 7.47/1.32  fof(f61,plain,(
% 7.47/1.32    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 7.47/1.32    inference(definition_unfolding,[],[f37,f60])).
% 7.47/1.32  fof(f37,plain,(
% 7.47/1.32    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.47/1.32    inference(cnf_transformation,[],[f12])).
% 7.47/1.32  fof(f12,axiom,(
% 7.47/1.32    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 7.47/1.32    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 7.47/1.32  fof(f34,plain,(
% 7.47/1.32    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.47/1.32    inference(cnf_transformation,[],[f11])).
% 7.47/1.32  fof(f11,axiom,(
% 7.47/1.32    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.47/1.32    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 7.47/1.32  fof(f56,plain,(
% 7.47/1.32    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 7.47/1.32    inference(definition_unfolding,[],[f38,f39])).
% 7.47/1.32  fof(f39,plain,(
% 7.47/1.32    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.47/1.32    inference(cnf_transformation,[],[f3])).
% 7.47/1.32  fof(f3,axiom,(
% 7.47/1.32    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.47/1.32    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 7.47/1.32  fof(f38,plain,(
% 7.47/1.32    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 7.47/1.32    inference(cnf_transformation,[],[f8])).
% 7.47/1.32  fof(f8,axiom,(
% 7.47/1.32    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 7.47/1.32    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 7.47/1.32  fof(f55,plain,(
% 7.47/1.32    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))) )),
% 7.47/1.32    inference(cnf_transformation,[],[f10])).
% 7.47/1.32  fof(f10,axiom,(
% 7.47/1.32    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))),
% 7.47/1.32    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).
% 7.47/1.32  fof(f290,plain,(
% 7.47/1.32    ~spl4_7 | spl4_8 | ~spl4_3),
% 7.47/1.32    inference(avatar_split_clause,[],[f274,f100,f286,f282])).
% 7.47/1.32  fof(f274,plain,(
% 7.47/1.32    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) | ~r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~spl4_3),
% 7.47/1.32    inference(superposition,[],[f102,f95])).
% 7.47/1.32  fof(f95,plain,(
% 7.47/1.32    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = X2 | ~r1_tarski(X2,X3)) )),
% 7.47/1.32    inference(superposition,[],[f40,f35])).
% 7.47/1.32  fof(f40,plain,(
% 7.47/1.32    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.47/1.32    inference(cnf_transformation,[],[f21])).
% 7.47/1.32  fof(f21,plain,(
% 7.47/1.32    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.47/1.32    inference(ennf_transformation,[],[f4])).
% 7.47/1.32  fof(f4,axiom,(
% 7.47/1.32    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.47/1.32    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 7.47/1.32  fof(f289,plain,(
% 7.47/1.32    ~spl4_7 | spl4_8 | ~spl4_3),
% 7.47/1.32    inference(avatar_split_clause,[],[f270,f100,f286,f282])).
% 7.47/1.32  fof(f270,plain,(
% 7.47/1.32    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) | ~r1_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~spl4_3),
% 7.47/1.32    inference(superposition,[],[f95,f102])).
% 7.47/1.32  fof(f280,plain,(
% 7.47/1.32    spl4_6 | ~spl4_2),
% 7.47/1.32    inference(avatar_split_clause,[],[f266,f86,f277])).
% 7.47/1.32  fof(f266,plain,(
% 7.47/1.32    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~spl4_2),
% 7.47/1.32    inference(unit_resulting_resolution,[],[f88,f95])).
% 7.47/1.32  fof(f140,plain,(
% 7.47/1.32    ~spl4_5 | spl4_1),
% 7.47/1.32    inference(avatar_split_clause,[],[f120,f81,f137])).
% 7.47/1.32  fof(f137,plain,(
% 7.47/1.32    spl4_5 <=> r2_hidden(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 7.47/1.32    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 7.47/1.32  fof(f120,plain,(
% 7.47/1.32    ~r2_hidden(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | spl4_1),
% 7.47/1.32    inference(unit_resulting_resolution,[],[f83,f83,f83,f79])).
% 7.47/1.32  fof(f135,plain,(
% 7.47/1.32    ~spl4_4 | spl4_1),
% 7.47/1.32    inference(avatar_split_clause,[],[f121,f81,f132])).
% 7.47/1.32  fof(f121,plain,(
% 7.47/1.32    ~r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | spl4_1),
% 7.47/1.32    inference(unit_resulting_resolution,[],[f83,f83,f83,f79])).
% 7.47/1.32  fof(f103,plain,(
% 7.47/1.32    spl4_3 | ~spl4_2),
% 7.47/1.32    inference(avatar_split_clause,[],[f94,f86,f100])).
% 7.47/1.32  fof(f94,plain,(
% 7.47/1.32    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | ~spl4_2),
% 7.47/1.32    inference(unit_resulting_resolution,[],[f88,f40])).
% 7.47/1.32  fof(f89,plain,(
% 7.47/1.32    spl4_2),
% 7.47/1.32    inference(avatar_split_clause,[],[f64,f86])).
% 7.47/1.32  fof(f64,plain,(
% 7.47/1.32    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),
% 7.47/1.32    inference(definition_unfolding,[],[f30,f61,f62])).
% 7.47/1.32  fof(f30,plain,(
% 7.47/1.32    r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2))),
% 7.47/1.32    inference(cnf_transformation,[],[f24])).
% 7.47/1.32  fof(f24,plain,(
% 7.47/1.32    sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2))),
% 7.47/1.32    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f23])).
% 7.47/1.32  fof(f23,plain,(
% 7.47/1.32    ? [X0,X1,X2] : (X0 != X2 & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))) => (sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)))),
% 7.47/1.32    introduced(choice_axiom,[])).
% 7.47/1.32  fof(f20,plain,(
% 7.47/1.32    ? [X0,X1,X2] : (X0 != X2 & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)))),
% 7.47/1.32    inference(ennf_transformation,[],[f19])).
% 7.47/1.32  fof(f19,negated_conjecture,(
% 7.47/1.32    ~! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => X0 = X2)),
% 7.47/1.32    inference(negated_conjecture,[],[f18])).
% 7.47/1.32  fof(f18,conjecture,(
% 7.47/1.32    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => X0 = X2)),
% 7.47/1.32    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_zfmisc_1)).
% 7.47/1.32  fof(f84,plain,(
% 7.47/1.32    ~spl4_1),
% 7.47/1.32    inference(avatar_split_clause,[],[f31,f81])).
% 7.47/1.33  fof(f31,plain,(
% 7.47/1.33    sK0 != sK2),
% 7.47/1.33    inference(cnf_transformation,[],[f24])).
% 7.47/1.33  % SZS output end Proof for theBenchmark
% 7.47/1.33  % (28796)------------------------------
% 7.47/1.33  % (28796)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.47/1.33  % (28796)Termination reason: Refutation
% 7.47/1.33  
% 7.47/1.33  % (28796)Memory used [KB]: 11769
% 7.47/1.33  % (28796)Time elapsed: 0.923 s
% 7.47/1.33  % (28796)------------------------------
% 7.47/1.33  % (28796)------------------------------
% 7.47/1.33  % (28777)Success in time 0.984 s
%------------------------------------------------------------------------------
