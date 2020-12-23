%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : ordinal1__t5_ordinal1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n030.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:28 EDT 2019

% Result     : Theorem 8.13s
% Output     : Refutation 8.13s
% Verified   : 
% Statistics : Number of formulae       :  342 (1440 expanded)
%              Number of leaves         :   94 ( 520 expanded)
%              Depth                    :   19
%              Number of atoms          :  912 (7523 expanded)
%              Number of equality atoms :  181 (3726 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4451,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f89,f96,f103,f110,f117,f127,f141,f148,f157,f164,f171,f193,f200,f212,f219,f226,f235,f242,f249,f256,f263,f284,f314,f321,f328,f335,f342,f371,f378,f385,f392,f399,f412,f419,f426,f433,f512,f529,f536,f543,f550,f557,f566,f573,f580,f587,f594,f602,f609,f616,f623,f700,f707,f714,f721,f728,f760,f782,f789,f796,f803,f844,f866,f873,f880,f887,f3933,f3946,f4096,f4109,f4205,f4219,f4229,f4243,f4271,f4421])).

fof(f4421,plain,
    ( ~ spl9_4
    | ~ spl9_156 ),
    inference(avatar_contradiction_clause,[],[f4420])).

fof(f4420,plain,
    ( $false
    | ~ spl9_4
    | ~ spl9_156 ),
    inference(subsumption_resolution,[],[f4325,f95])).

fof(f95,plain,
    ( r2_hidden(sK2,sK3)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl9_4
  <=> r2_hidden(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f4325,plain,
    ( ~ r2_hidden(sK2,sK3)
    | ~ spl9_156 ),
    inference(superposition,[],[f955,f4270])).

fof(f4270,plain,
    ( sK3 = sK7(k3_enumset1(sK1,sK5,sK4,sK3,sK2))
    | ~ spl9_156 ),
    inference(avatar_component_clause,[],[f4269])).

fof(f4269,plain,
    ( spl9_156
  <=> sK3 = sK7(k3_enumset1(sK1,sK5,sK4,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_156])])).

fof(f955,plain,(
    ! [X4,X2,X0,X3,X1] : ~ r2_hidden(X0,sK7(k3_enumset1(X1,X2,X3,X4,X0))) ),
    inference(unit_resulting_resolution,[],[f517,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK7(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(condensation,[],[f54])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,sK7(X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK7(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK7(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f24,f32])).

fof(f32,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK7(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK7(X1),X1) ) ) ),
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
    file('/export/starexec/sandbox2/benchmark/ordinal1__t5_ordinal1.p',t7_tarski)).

fof(f517,plain,(
    ! [X4,X2,X0,X3,X1] : r2_hidden(X0,k3_enumset1(X1,X2,X3,X4,X0)) ),
    inference(unit_resulting_resolution,[],[f74,f69])).

fof(f69,plain,(
    ! [X4,X2,X7,X5,X3,X1] :
      ( ~ sP0(X7,X1,X2,X3,X4,X5)
      | r2_hidden(X7,X5) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r2_hidden(X7,X5)
      | X0 != X7
      | ~ sP0(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( sP0(X0,X1,X2,X3,X4,X5)
        | ( ( ( sK8(X0,X1,X2,X3,X4,X5) != X0
              & sK8(X0,X1,X2,X3,X4,X5) != X1
              & sK8(X0,X1,X2,X3,X4,X5) != X2
              & sK8(X0,X1,X2,X3,X4,X5) != X3
              & sK8(X0,X1,X2,X3,X4,X5) != X4 )
            | ~ r2_hidden(sK8(X0,X1,X2,X3,X4,X5),X5) )
          & ( sK8(X0,X1,X2,X3,X4,X5) = X0
            | sK8(X0,X1,X2,X3,X4,X5) = X1
            | sK8(X0,X1,X2,X3,X4,X5) = X2
            | sK8(X0,X1,X2,X3,X4,X5) = X3
            | sK8(X0,X1,X2,X3,X4,X5) = X4
            | r2_hidden(sK8(X0,X1,X2,X3,X4,X5),X5) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X5)
              | ( X0 != X7
                & X1 != X7
                & X2 != X7
                & X3 != X7
                & X4 != X7 ) )
            & ( X0 = X7
              | X1 = X7
              | X2 = X7
              | X3 = X7
              | X4 = X7
              | ~ r2_hidden(X7,X5) ) )
        | ~ sP0(X0,X1,X2,X3,X4,X5) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f36,f37])).

fof(f37,plain,(
    ! [X5,X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( ( ( X0 != X6
              & X1 != X6
              & X2 != X6
              & X3 != X6
              & X4 != X6 )
            | ~ r2_hidden(X6,X5) )
          & ( X0 = X6
            | X1 = X6
            | X2 = X6
            | X3 = X6
            | X4 = X6
            | r2_hidden(X6,X5) ) )
     => ( ( ( sK8(X0,X1,X2,X3,X4,X5) != X0
            & sK8(X0,X1,X2,X3,X4,X5) != X1
            & sK8(X0,X1,X2,X3,X4,X5) != X2
            & sK8(X0,X1,X2,X3,X4,X5) != X3
            & sK8(X0,X1,X2,X3,X4,X5) != X4 )
          | ~ r2_hidden(sK8(X0,X1,X2,X3,X4,X5),X5) )
        & ( sK8(X0,X1,X2,X3,X4,X5) = X0
          | sK8(X0,X1,X2,X3,X4,X5) = X1
          | sK8(X0,X1,X2,X3,X4,X5) = X2
          | sK8(X0,X1,X2,X3,X4,X5) = X3
          | sK8(X0,X1,X2,X3,X4,X5) = X4
          | r2_hidden(sK8(X0,X1,X2,X3,X4,X5),X5) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( sP0(X0,X1,X2,X3,X4,X5)
        | ? [X6] :
            ( ( ( X0 != X6
                & X1 != X6
                & X2 != X6
                & X3 != X6
                & X4 != X6 )
              | ~ r2_hidden(X6,X5) )
            & ( X0 = X6
              | X1 = X6
              | X2 = X6
              | X3 = X6
              | X4 = X6
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X5)
              | ( X0 != X7
                & X1 != X7
                & X2 != X7
                & X3 != X7
                & X4 != X7 ) )
            & ( X0 = X7
              | X1 = X7
              | X2 = X7
              | X3 = X7
              | X4 = X7
              | ~ r2_hidden(X7,X5) ) )
        | ~ sP0(X0,X1,X2,X3,X4,X5) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X4,X3,X2,X1,X0,X5] :
      ( ( sP0(X4,X3,X2,X1,X0,X5)
        | ? [X6] :
            ( ( ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 )
              | ~ r2_hidden(X6,X5) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X5)
              | ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 ) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | ~ r2_hidden(X6,X5) ) )
        | ~ sP0(X4,X3,X2,X1,X0,X5) ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X4,X3,X2,X1,X0,X5] :
      ( ( sP0(X4,X3,X2,X1,X0,X5)
        | ? [X6] :
            ( ( ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 )
              | ~ r2_hidden(X6,X5) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X5)
              | ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 ) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | ~ r2_hidden(X6,X5) ) )
        | ~ sP0(X4,X3,X2,X1,X0,X5) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X4,X3,X2,X1,X0,X5] :
      ( sP0(X4,X3,X2,X1,X0,X5)
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ( X4 = X6
            | X3 = X6
            | X2 = X6
            | X1 = X6
            | X0 = X6 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] : sP0(X4,X3,X2,X1,X0,k3_enumset1(X0,X1,X2,X3,X4)) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sP0(X4,X3,X2,X1,X0,X5)
      | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( k3_enumset1(X0,X1,X2,X3,X4) = X5
        | ~ sP0(X4,X3,X2,X1,X0,X5) )
      & ( sP0(X4,X3,X2,X1,X0,X5)
        | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> sP0(X4,X3,X2,X1,X0,X5) ) ),
    inference(definition_folding,[],[f25,f26])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ( X4 = X6
            | X3 = X6
            | X2 = X6
            | X1 = X6
            | X0 = X6 ) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ~ ( X4 != X6
              & X3 != X6
              & X2 != X6
              & X1 != X6
              & X0 != X6 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t5_ordinal1.p',d3_enumset1)).

fof(f4271,plain,
    ( spl9_156
    | ~ spl9_2
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f4252,f115,f108,f101,f87,f4269])).

fof(f87,plain,
    ( spl9_2
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f101,plain,
    ( spl9_6
  <=> r2_hidden(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f108,plain,
    ( spl9_8
  <=> r2_hidden(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f115,plain,
    ( spl9_10
  <=> r2_hidden(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f4252,plain,
    ( sK3 = sK7(k3_enumset1(sK1,sK5,sK4,sK3,sK2))
    | ~ spl9_2
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(unit_resulting_resolution,[],[f102,f4133])).

fof(f4133,plain,
    ( ! [X7] :
        ( ~ r2_hidden(X7,sK4)
        | sK7(k3_enumset1(sK1,sK5,sK4,X7,sK2)) = X7 )
    | ~ spl9_2
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(superposition,[],[f947,f4113])).

fof(f4113,plain,
    ( ! [X0] :
        ( sK4 = sK7(k3_enumset1(sK1,sK5,sK4,X0,sK2))
        | sK7(k3_enumset1(sK1,sK5,sK4,X0,sK2)) = X0 )
    | ~ spl9_2
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(resolution,[],[f4024,f109])).

fof(f109,plain,
    ( r2_hidden(sK4,sK5)
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f108])).

fof(f4024,plain,
    ( ! [X10,X11] :
        ( ~ r2_hidden(X10,sK5)
        | sK7(k3_enumset1(sK1,sK5,X10,X11,sK2)) = X11
        | sK7(k3_enumset1(sK1,sK5,X10,X11,sK2)) = X10 )
    | ~ spl9_2
    | ~ spl9_10 ),
    inference(superposition,[],[f939,f4007])).

fof(f4007,plain,
    ( ! [X0,X1] :
        ( sK5 = sK7(k3_enumset1(sK1,sK5,X0,X1,sK2))
        | sK7(k3_enumset1(sK1,sK5,X0,X1,sK2)) = X1
        | sK7(k3_enumset1(sK1,sK5,X0,X1,sK2)) = X0 )
    | ~ spl9_2
    | ~ spl9_10 ),
    inference(resolution,[],[f3861,f116])).

fof(f116,plain,
    ( r2_hidden(sK5,sK1)
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f115])).

fof(f3861,plain,
    ( ! [X10,X11,X9] :
        ( ~ r2_hidden(X9,sK1)
        | sK7(k3_enumset1(sK1,X9,X10,X11,sK2)) = X9
        | sK7(k3_enumset1(sK1,X9,X10,X11,sK2)) = X11
        | sK7(k3_enumset1(sK1,X9,X10,X11,sK2)) = X10 )
    | ~ spl9_2 ),
    inference(superposition,[],[f931,f3769])).

fof(f3769,plain,
    ( ! [X41,X42,X40] :
        ( sK1 = sK7(k3_enumset1(sK1,X40,X41,X42,sK2))
        | sK7(k3_enumset1(sK1,X40,X41,X42,sK2)) = X40
        | sK7(k3_enumset1(sK1,X40,X41,X42,sK2)) = X42
        | sK7(k3_enumset1(sK1,X40,X41,X42,sK2)) = X41 )
    | ~ spl9_2 ),
    inference(resolution,[],[f1993,f88])).

fof(f88,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f87])).

fof(f1993,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ r2_hidden(X5,X9)
      | sK7(k3_enumset1(X5,X6,X7,X8,X9)) = X6
      | sK7(k3_enumset1(X5,X6,X7,X8,X9)) = X5
      | sK7(k3_enumset1(X5,X6,X7,X8,X9)) = X8
      | sK7(k3_enumset1(X5,X6,X7,X8,X9)) = X7 ) ),
    inference(superposition,[],[f898,f1094])).

fof(f1094,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sK7(k3_enumset1(X0,X1,X2,X3,X4)) = X4
      | sK7(k3_enumset1(X0,X1,X2,X3,X4)) = X1
      | sK7(k3_enumset1(X0,X1,X2,X3,X4)) = X0
      | sK7(k3_enumset1(X0,X1,X2,X3,X4)) = X3
      | sK7(k3_enumset1(X0,X1,X2,X3,X4)) = X2 ) ),
    inference(resolution,[],[f897,f595])).

fof(f595,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(X1,k3_enumset1(X4,X3,X2,X0,X5))
      | X1 = X2
      | X1 = X3
      | X1 = X4
      | X0 = X1
      | X1 = X5 ) ),
    inference(resolution,[],[f55,f74])).

fof(f55,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3,X4,X5)
      | X1 = X7
      | X2 = X7
      | X3 = X7
      | X4 = X7
      | ~ r2_hidden(X7,X5)
      | X0 = X7 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f897,plain,(
    ! [X4,X2,X0,X3,X1] : r2_hidden(sK7(k3_enumset1(X0,X1,X2,X3,X4)),k3_enumset1(X0,X1,X2,X3,X4)) ),
    inference(unit_resulting_resolution,[],[f513,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X1),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f513,plain,(
    ! [X4,X2,X0,X3,X1] : r2_hidden(X0,k3_enumset1(X0,X1,X2,X3,X4)) ),
    inference(unit_resulting_resolution,[],[f74,f73])).

fof(f73,plain,(
    ! [X2,X0,X7,X5,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3,X7,X5)
      | r2_hidden(X7,X5) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r2_hidden(X7,X5)
      | X4 != X7
      | ~ sP0(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f898,plain,(
    ! [X4,X2,X0,X3,X1] : ~ r2_hidden(X0,sK7(k3_enumset1(X0,X1,X2,X3,X4))) ),
    inference(unit_resulting_resolution,[],[f513,f75])).

fof(f931,plain,(
    ! [X4,X2,X0,X3,X1] : ~ r2_hidden(X0,sK7(k3_enumset1(X1,X0,X2,X3,X4))) ),
    inference(unit_resulting_resolution,[],[f514,f75])).

fof(f514,plain,(
    ! [X4,X2,X0,X3,X1] : r2_hidden(X0,k3_enumset1(X1,X0,X2,X3,X4)) ),
    inference(unit_resulting_resolution,[],[f74,f72])).

fof(f72,plain,(
    ! [X4,X2,X0,X7,X5,X1] :
      ( ~ sP0(X0,X1,X2,X7,X4,X5)
      | r2_hidden(X7,X5) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r2_hidden(X7,X5)
      | X3 != X7
      | ~ sP0(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f939,plain,(
    ! [X4,X2,X0,X3,X1] : ~ r2_hidden(X0,sK7(k3_enumset1(X1,X2,X0,X3,X4))) ),
    inference(unit_resulting_resolution,[],[f515,f75])).

fof(f515,plain,(
    ! [X4,X2,X0,X3,X1] : r2_hidden(X0,k3_enumset1(X1,X2,X0,X3,X4)) ),
    inference(unit_resulting_resolution,[],[f74,f71])).

fof(f71,plain,(
    ! [X4,X0,X7,X5,X3,X1] :
      ( ~ sP0(X0,X1,X7,X3,X4,X5)
      | r2_hidden(X7,X5) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r2_hidden(X7,X5)
      | X2 != X7
      | ~ sP0(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f947,plain,(
    ! [X4,X2,X0,X3,X1] : ~ r2_hidden(X0,sK7(k3_enumset1(X1,X2,X3,X0,X4))) ),
    inference(unit_resulting_resolution,[],[f516,f75])).

fof(f516,plain,(
    ! [X4,X2,X0,X3,X1] : r2_hidden(X0,k3_enumset1(X1,X2,X3,X0,X4)) ),
    inference(unit_resulting_resolution,[],[f74,f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X7,X5,X3] :
      ( ~ sP0(X0,X7,X2,X3,X4,X5)
      | r2_hidden(X7,X5) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r2_hidden(X7,X5)
      | X1 != X7
      | ~ sP0(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f102,plain,
    ( r2_hidden(sK3,sK4)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f101])).

fof(f4243,plain,
    ( ~ spl9_155
    | spl9_19
    | spl9_153 ),
    inference(avatar_split_clause,[],[f4235,f4227,f155,f4241])).

fof(f4241,plain,
    ( spl9_155
  <=> ~ m1_subset_1(sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_155])])).

fof(f155,plain,
    ( spl9_19
  <=> ~ v1_xboole_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f4227,plain,
    ( spl9_153
  <=> ~ r2_hidden(sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_153])])).

fof(f4235,plain,
    ( ~ m1_subset_1(sK4,sK4)
    | ~ spl9_19
    | ~ spl9_153 ),
    inference(unit_resulting_resolution,[],[f156,f4228,f48])).

fof(f48,plain,(
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
    file('/export/starexec/sandbox2/benchmark/ordinal1__t5_ordinal1.p',t2_subset)).

fof(f4228,plain,
    ( ~ r2_hidden(sK4,sK4)
    | ~ spl9_153 ),
    inference(avatar_component_clause,[],[f4227])).

fof(f156,plain,
    ( ~ v1_xboole_0(sK4)
    | ~ spl9_19 ),
    inference(avatar_component_clause,[],[f155])).

fof(f4229,plain,
    ( spl9_146
    | ~ spl9_153
    | ~ spl9_2
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f4132,f115,f108,f87,f4227,f4197])).

fof(f4197,plain,
    ( spl9_146
  <=> ! [X3] : sK7(k3_enumset1(sK1,sK5,sK4,X3,sK2)) = X3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_146])])).

fof(f4132,plain,
    ( ! [X6] :
        ( ~ r2_hidden(sK4,sK4)
        | sK7(k3_enumset1(sK1,sK5,sK4,X6,sK2)) = X6 )
    | ~ spl9_2
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(superposition,[],[f939,f4113])).

fof(f4219,plain,
    ( ~ spl9_151
    | spl9_19
    | spl9_149 ),
    inference(avatar_split_clause,[],[f4212,f4203,f155,f4217])).

fof(f4217,plain,
    ( spl9_151
  <=> ~ m1_subset_1(sK1,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_151])])).

fof(f4203,plain,
    ( spl9_149
  <=> ~ r2_hidden(sK1,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_149])])).

fof(f4212,plain,
    ( ~ m1_subset_1(sK1,sK4)
    | ~ spl9_19
    | ~ spl9_149 ),
    inference(unit_resulting_resolution,[],[f156,f4204,f48])).

fof(f4204,plain,
    ( ~ r2_hidden(sK1,sK4)
    | ~ spl9_149 ),
    inference(avatar_component_clause,[],[f4203])).

fof(f4205,plain,
    ( spl9_146
    | ~ spl9_149
    | ~ spl9_2
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f4129,f115,f108,f87,f4203,f4197])).

fof(f4129,plain,
    ( ! [X3] :
        ( ~ r2_hidden(sK1,sK4)
        | sK7(k3_enumset1(sK1,sK5,sK4,X3,sK2)) = X3 )
    | ~ spl9_2
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(superposition,[],[f898,f4113])).

fof(f4109,plain,
    ( ~ spl9_145
    | spl9_21
    | spl9_143 ),
    inference(avatar_split_clause,[],[f4102,f4094,f162,f4107])).

fof(f4107,plain,
    ( spl9_145
  <=> ~ m1_subset_1(sK5,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_145])])).

fof(f162,plain,
    ( spl9_21
  <=> ~ v1_xboole_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f4094,plain,
    ( spl9_143
  <=> ~ r2_hidden(sK5,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_143])])).

fof(f4102,plain,
    ( ~ m1_subset_1(sK5,sK5)
    | ~ spl9_21
    | ~ spl9_143 ),
    inference(unit_resulting_resolution,[],[f163,f4095,f48])).

fof(f4095,plain,
    ( ~ r2_hidden(sK5,sK5)
    | ~ spl9_143 ),
    inference(avatar_component_clause,[],[f4094])).

fof(f163,plain,
    ( ~ v1_xboole_0(sK5)
    | ~ spl9_21 ),
    inference(avatar_component_clause,[],[f162])).

fof(f4096,plain,
    ( spl9_140
    | ~ spl9_143
    | ~ spl9_2
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f4023,f115,f87,f4094,f4088])).

fof(f4088,plain,
    ( spl9_140
  <=> ! [X9,X8] :
        ( sK7(k3_enumset1(sK1,sK5,X8,X9,sK2)) = X9
        | sK7(k3_enumset1(sK1,sK5,X8,X9,sK2)) = X8 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_140])])).

fof(f4023,plain,
    ( ! [X8,X9] :
        ( ~ r2_hidden(sK5,sK5)
        | sK7(k3_enumset1(sK1,sK5,X8,X9,sK2)) = X9
        | sK7(k3_enumset1(sK1,sK5,X8,X9,sK2)) = X8 )
    | ~ spl9_2
    | ~ spl9_10 ),
    inference(superposition,[],[f931,f4007])).

fof(f3946,plain,
    ( ~ spl9_139
    | spl9_23
    | spl9_137 ),
    inference(avatar_split_clause,[],[f3939,f3931,f169,f3944])).

fof(f3944,plain,
    ( spl9_139
  <=> ~ m1_subset_1(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_139])])).

fof(f169,plain,
    ( spl9_23
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).

fof(f3931,plain,
    ( spl9_137
  <=> ~ r2_hidden(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_137])])).

fof(f3939,plain,
    ( ~ m1_subset_1(sK1,sK1)
    | ~ spl9_23
    | ~ spl9_137 ),
    inference(unit_resulting_resolution,[],[f170,f3932,f48])).

fof(f3932,plain,
    ( ~ r2_hidden(sK1,sK1)
    | ~ spl9_137 ),
    inference(avatar_component_clause,[],[f3931])).

fof(f170,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl9_23 ),
    inference(avatar_component_clause,[],[f169])).

fof(f3933,plain,
    ( spl9_134
    | ~ spl9_137
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f3859,f87,f3931,f3925])).

fof(f3925,plain,
    ( spl9_134
  <=> ! [X3,X5,X4] :
        ( sK7(k3_enumset1(sK1,X3,X4,X5,sK2)) = X3
        | sK7(k3_enumset1(sK1,X3,X4,X5,sK2)) = X4
        | sK7(k3_enumset1(sK1,X3,X4,X5,sK2)) = X5 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_134])])).

fof(f3859,plain,
    ( ! [X4,X5,X3] :
        ( ~ r2_hidden(sK1,sK1)
        | sK7(k3_enumset1(sK1,X3,X4,X5,sK2)) = X3
        | sK7(k3_enumset1(sK1,X3,X4,X5,sK2)) = X5
        | sK7(k3_enumset1(sK1,X3,X4,X5,sK2)) = X4 )
    | ~ spl9_2 ),
    inference(superposition,[],[f898,f3769])).

fof(f887,plain,
    ( ~ spl9_133
    | ~ spl9_82 ),
    inference(avatar_split_clause,[],[f657,f548,f885])).

fof(f885,plain,
    ( spl9_133
  <=> ~ r2_hidden(sK6(sK5),sK7(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_133])])).

fof(f548,plain,
    ( spl9_82
  <=> r2_hidden(sK6(sK5),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_82])])).

fof(f657,plain,
    ( ~ r2_hidden(sK6(sK5),sK7(sK5))
    | ~ spl9_82 ),
    inference(unit_resulting_resolution,[],[f549,f75])).

fof(f549,plain,
    ( r2_hidden(sK6(sK5),sK5)
    | ~ spl9_82 ),
    inference(avatar_component_clause,[],[f548])).

fof(f880,plain,
    ( ~ spl9_131
    | ~ spl9_80 ),
    inference(avatar_split_clause,[],[f650,f541,f878])).

fof(f878,plain,
    ( spl9_131
  <=> ~ r2_hidden(sK6(sK4),sK7(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_131])])).

fof(f541,plain,
    ( spl9_80
  <=> r2_hidden(sK6(sK4),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_80])])).

fof(f650,plain,
    ( ~ r2_hidden(sK6(sK4),sK7(sK4))
    | ~ spl9_80 ),
    inference(unit_resulting_resolution,[],[f542,f75])).

fof(f542,plain,
    ( r2_hidden(sK6(sK4),sK4)
    | ~ spl9_80 ),
    inference(avatar_component_clause,[],[f541])).

fof(f873,plain,
    ( ~ spl9_129
    | ~ spl9_78 ),
    inference(avatar_split_clause,[],[f643,f534,f871])).

fof(f871,plain,
    ( spl9_129
  <=> ~ r2_hidden(sK6(sK3),sK7(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_129])])).

fof(f534,plain,
    ( spl9_78
  <=> r2_hidden(sK6(sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_78])])).

fof(f643,plain,
    ( ~ r2_hidden(sK6(sK3),sK7(sK3))
    | ~ spl9_78 ),
    inference(unit_resulting_resolution,[],[f535,f75])).

fof(f535,plain,
    ( r2_hidden(sK6(sK3),sK3)
    | ~ spl9_78 ),
    inference(avatar_component_clause,[],[f534])).

fof(f866,plain,
    ( ~ spl9_127
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f636,f527,f864])).

fof(f864,plain,
    ( spl9_127
  <=> ~ r2_hidden(sK6(sK2),sK7(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_127])])).

fof(f527,plain,
    ( spl9_76
  <=> r2_hidden(sK6(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_76])])).

fof(f636,plain,
    ( ~ r2_hidden(sK6(sK2),sK7(sK2))
    | ~ spl9_76 ),
    inference(unit_resulting_resolution,[],[f528,f75])).

fof(f528,plain,
    ( r2_hidden(sK6(sK2),sK2)
    | ~ spl9_76 ),
    inference(avatar_component_clause,[],[f527])).

fof(f844,plain,
    ( ~ spl9_125
    | ~ spl9_74 ),
    inference(avatar_split_clause,[],[f629,f510,f842])).

fof(f842,plain,
    ( spl9_125
  <=> ~ r2_hidden(sK6(sK1),sK7(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_125])])).

fof(f510,plain,
    ( spl9_74
  <=> r2_hidden(sK6(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_74])])).

fof(f629,plain,
    ( ~ r2_hidden(sK6(sK1),sK7(sK1))
    | ~ spl9_74 ),
    inference(unit_resulting_resolution,[],[f511,f75])).

fof(f511,plain,
    ( r2_hidden(sK6(sK1),sK1)
    | ~ spl9_74 ),
    inference(avatar_component_clause,[],[f510])).

fof(f803,plain,
    ( ~ spl9_123
    | ~ spl9_62 ),
    inference(avatar_split_clause,[],[f468,f390,f801])).

fof(f801,plain,
    ( spl9_123
  <=> ~ r2_hidden(sK7(sK1),sK7(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_123])])).

fof(f390,plain,
    ( spl9_62
  <=> r2_hidden(sK7(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_62])])).

fof(f468,plain,
    ( ~ r2_hidden(sK7(sK1),sK7(sK1))
    | ~ spl9_62 ),
    inference(unit_resulting_resolution,[],[f391,f75])).

fof(f391,plain,
    ( r2_hidden(sK7(sK1),sK1)
    | ~ spl9_62 ),
    inference(avatar_component_clause,[],[f390])).

fof(f796,plain,
    ( ~ spl9_121
    | ~ spl9_60 ),
    inference(avatar_split_clause,[],[f461,f383,f794])).

fof(f794,plain,
    ( spl9_121
  <=> ~ r2_hidden(sK7(sK5),sK7(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_121])])).

fof(f383,plain,
    ( spl9_60
  <=> r2_hidden(sK7(sK5),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_60])])).

fof(f461,plain,
    ( ~ r2_hidden(sK7(sK5),sK7(sK5))
    | ~ spl9_60 ),
    inference(unit_resulting_resolution,[],[f384,f75])).

fof(f384,plain,
    ( r2_hidden(sK7(sK5),sK5)
    | ~ spl9_60 ),
    inference(avatar_component_clause,[],[f383])).

fof(f789,plain,
    ( ~ spl9_119
    | ~ spl9_58 ),
    inference(avatar_split_clause,[],[f454,f376,f787])).

fof(f787,plain,
    ( spl9_119
  <=> ~ r2_hidden(sK7(sK4),sK7(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_119])])).

fof(f376,plain,
    ( spl9_58
  <=> r2_hidden(sK7(sK4),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_58])])).

fof(f454,plain,
    ( ~ r2_hidden(sK7(sK4),sK7(sK4))
    | ~ spl9_58 ),
    inference(unit_resulting_resolution,[],[f377,f75])).

fof(f377,plain,
    ( r2_hidden(sK7(sK4),sK4)
    | ~ spl9_58 ),
    inference(avatar_component_clause,[],[f376])).

fof(f782,plain,
    ( ~ spl9_117
    | ~ spl9_56 ),
    inference(avatar_split_clause,[],[f447,f369,f780])).

fof(f780,plain,
    ( spl9_117
  <=> ~ r2_hidden(sK7(sK3),sK7(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_117])])).

fof(f369,plain,
    ( spl9_56
  <=> r2_hidden(sK7(sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_56])])).

fof(f447,plain,
    ( ~ r2_hidden(sK7(sK3),sK7(sK3))
    | ~ spl9_56 ),
    inference(unit_resulting_resolution,[],[f370,f75])).

fof(f370,plain,
    ( r2_hidden(sK7(sK3),sK3)
    | ~ spl9_56 ),
    inference(avatar_component_clause,[],[f369])).

fof(f760,plain,
    ( ~ spl9_115
    | ~ spl9_44 ),
    inference(avatar_split_clause,[],[f434,f282,f758])).

fof(f758,plain,
    ( spl9_115
  <=> ~ r2_hidden(sK7(sK2),sK7(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_115])])).

fof(f282,plain,
    ( spl9_44
  <=> r2_hidden(sK7(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_44])])).

fof(f434,plain,
    ( ~ r2_hidden(sK7(sK2),sK7(sK2))
    | ~ spl9_44 ),
    inference(unit_resulting_resolution,[],[f283,f75])).

fof(f283,plain,
    ( r2_hidden(sK7(sK2),sK2)
    | ~ spl9_44 ),
    inference(avatar_component_clause,[],[f282])).

fof(f728,plain,
    ( ~ spl9_113
    | ~ spl9_82 ),
    inference(avatar_split_clause,[],[f653,f548,f726])).

fof(f726,plain,
    ( spl9_113
  <=> ~ r2_hidden(sK5,sK6(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_113])])).

fof(f653,plain,
    ( ~ r2_hidden(sK5,sK6(sK5))
    | ~ spl9_82 ),
    inference(unit_resulting_resolution,[],[f549,f49])).

fof(f49,plain,(
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
    file('/export/starexec/sandbox2/benchmark/ordinal1__t5_ordinal1.p',antisymmetry_r2_hidden)).

fof(f721,plain,
    ( ~ spl9_111
    | ~ spl9_80 ),
    inference(avatar_split_clause,[],[f646,f541,f719])).

fof(f719,plain,
    ( spl9_111
  <=> ~ r2_hidden(sK4,sK6(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_111])])).

fof(f646,plain,
    ( ~ r2_hidden(sK4,sK6(sK4))
    | ~ spl9_80 ),
    inference(unit_resulting_resolution,[],[f542,f49])).

fof(f714,plain,
    ( ~ spl9_109
    | ~ spl9_78 ),
    inference(avatar_split_clause,[],[f639,f534,f712])).

fof(f712,plain,
    ( spl9_109
  <=> ~ r2_hidden(sK3,sK6(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_109])])).

fof(f639,plain,
    ( ~ r2_hidden(sK3,sK6(sK3))
    | ~ spl9_78 ),
    inference(unit_resulting_resolution,[],[f535,f49])).

fof(f707,plain,
    ( ~ spl9_107
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f632,f527,f705])).

fof(f705,plain,
    ( spl9_107
  <=> ~ r2_hidden(sK2,sK6(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_107])])).

fof(f632,plain,
    ( ~ r2_hidden(sK2,sK6(sK2))
    | ~ spl9_76 ),
    inference(unit_resulting_resolution,[],[f528,f49])).

fof(f700,plain,
    ( ~ spl9_105
    | ~ spl9_74 ),
    inference(avatar_split_clause,[],[f625,f510,f698])).

fof(f698,plain,
    ( spl9_105
  <=> ~ r2_hidden(sK1,sK6(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_105])])).

fof(f625,plain,
    ( ~ r2_hidden(sK1,sK6(sK1))
    | ~ spl9_74 ),
    inference(unit_resulting_resolution,[],[f511,f49])).

fof(f623,plain,
    ( ~ spl9_103
    | ~ spl9_62 ),
    inference(avatar_split_clause,[],[f472,f390,f621])).

fof(f621,plain,
    ( spl9_103
  <=> ~ r2_hidden(sK1,sK7(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_103])])).

fof(f472,plain,
    ( ~ r2_hidden(sK1,sK7(sK1))
    | ~ spl9_62 ),
    inference(unit_resulting_resolution,[],[f391,f49])).

fof(f616,plain,
    ( spl9_100
    | ~ spl9_62 ),
    inference(avatar_split_clause,[],[f470,f390,f614])).

fof(f614,plain,
    ( spl9_100
  <=> m1_subset_1(sK7(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_100])])).

fof(f470,plain,
    ( m1_subset_1(sK7(sK1),sK1)
    | ~ spl9_62 ),
    inference(unit_resulting_resolution,[],[f391,f50])).

fof(f50,plain,(
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
    file('/export/starexec/sandbox2/benchmark/ordinal1__t5_ordinal1.p',t1_subset)).

fof(f609,plain,
    ( ~ spl9_99
    | ~ spl9_60 ),
    inference(avatar_split_clause,[],[f465,f383,f607])).

fof(f607,plain,
    ( spl9_99
  <=> ~ r2_hidden(sK5,sK7(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_99])])).

fof(f465,plain,
    ( ~ r2_hidden(sK5,sK7(sK5))
    | ~ spl9_60 ),
    inference(unit_resulting_resolution,[],[f384,f49])).

fof(f602,plain,
    ( spl9_96
    | ~ spl9_60 ),
    inference(avatar_split_clause,[],[f463,f383,f600])).

fof(f600,plain,
    ( spl9_96
  <=> m1_subset_1(sK7(sK5),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_96])])).

fof(f463,plain,
    ( m1_subset_1(sK7(sK5),sK5)
    | ~ spl9_60 ),
    inference(unit_resulting_resolution,[],[f384,f50])).

fof(f594,plain,
    ( ~ spl9_95
    | ~ spl9_58 ),
    inference(avatar_split_clause,[],[f458,f376,f592])).

fof(f592,plain,
    ( spl9_95
  <=> ~ r2_hidden(sK4,sK7(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_95])])).

fof(f458,plain,
    ( ~ r2_hidden(sK4,sK7(sK4))
    | ~ spl9_58 ),
    inference(unit_resulting_resolution,[],[f377,f49])).

fof(f587,plain,
    ( spl9_92
    | ~ spl9_58 ),
    inference(avatar_split_clause,[],[f456,f376,f585])).

fof(f585,plain,
    ( spl9_92
  <=> m1_subset_1(sK7(sK4),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_92])])).

fof(f456,plain,
    ( m1_subset_1(sK7(sK4),sK4)
    | ~ spl9_58 ),
    inference(unit_resulting_resolution,[],[f377,f50])).

fof(f580,plain,
    ( ~ spl9_91
    | ~ spl9_56 ),
    inference(avatar_split_clause,[],[f451,f369,f578])).

fof(f578,plain,
    ( spl9_91
  <=> ~ r2_hidden(sK3,sK7(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_91])])).

fof(f451,plain,
    ( ~ r2_hidden(sK3,sK7(sK3))
    | ~ spl9_56 ),
    inference(unit_resulting_resolution,[],[f370,f49])).

fof(f573,plain,
    ( spl9_88
    | ~ spl9_56 ),
    inference(avatar_split_clause,[],[f449,f369,f571])).

fof(f571,plain,
    ( spl9_88
  <=> m1_subset_1(sK7(sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_88])])).

fof(f449,plain,
    ( m1_subset_1(sK7(sK3),sK3)
    | ~ spl9_56 ),
    inference(unit_resulting_resolution,[],[f370,f50])).

fof(f566,plain,
    ( ~ spl9_87
    | ~ spl9_44 ),
    inference(avatar_split_clause,[],[f438,f282,f564])).

fof(f564,plain,
    ( spl9_87
  <=> ~ r2_hidden(sK2,sK7(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_87])])).

fof(f438,plain,
    ( ~ r2_hidden(sK2,sK7(sK2))
    | ~ spl9_44 ),
    inference(unit_resulting_resolution,[],[f283,f49])).

fof(f557,plain,
    ( spl9_84
    | ~ spl9_44 ),
    inference(avatar_split_clause,[],[f436,f282,f555])).

fof(f555,plain,
    ( spl9_84
  <=> m1_subset_1(sK7(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_84])])).

fof(f436,plain,
    ( m1_subset_1(sK7(sK2),sK2)
    | ~ spl9_44 ),
    inference(unit_resulting_resolution,[],[f283,f50])).

fof(f550,plain,
    ( spl9_82
    | spl9_21 ),
    inference(avatar_split_clause,[],[f299,f162,f548])).

fof(f299,plain,
    ( r2_hidden(sK6(sK5),sK5)
    | ~ spl9_21 ),
    inference(unit_resulting_resolution,[],[f163,f47,f48])).

fof(f47,plain,(
    ! [X0] : m1_subset_1(sK6(X0),X0) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] : m1_subset_1(sK6(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f9,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f9,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t5_ordinal1.p',existence_m1_subset_1)).

fof(f543,plain,
    ( spl9_80
    | spl9_19 ),
    inference(avatar_split_clause,[],[f298,f155,f541])).

fof(f298,plain,
    ( r2_hidden(sK6(sK4),sK4)
    | ~ spl9_19 ),
    inference(unit_resulting_resolution,[],[f156,f47,f48])).

fof(f536,plain,
    ( spl9_78
    | spl9_17 ),
    inference(avatar_split_clause,[],[f297,f146,f534])).

fof(f146,plain,
    ( spl9_17
  <=> ~ v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f297,plain,
    ( r2_hidden(sK6(sK3),sK3)
    | ~ spl9_17 ),
    inference(unit_resulting_resolution,[],[f147,f47,f48])).

fof(f147,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl9_17 ),
    inference(avatar_component_clause,[],[f146])).

fof(f529,plain,
    ( spl9_76
    | spl9_15 ),
    inference(avatar_split_clause,[],[f296,f139,f527])).

fof(f139,plain,
    ( spl9_15
  <=> ~ v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f296,plain,
    ( r2_hidden(sK6(sK2),sK2)
    | ~ spl9_15 ),
    inference(unit_resulting_resolution,[],[f140,f47,f48])).

fof(f140,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f139])).

fof(f512,plain,
    ( spl9_74
    | spl9_23 ),
    inference(avatar_split_clause,[],[f295,f169,f510])).

fof(f295,plain,
    ( r2_hidden(sK6(sK1),sK1)
    | ~ spl9_23 ),
    inference(unit_resulting_resolution,[],[f170,f47,f48])).

fof(f433,plain,
    ( ~ spl9_73
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f274,f115,f431])).

fof(f431,plain,
    ( spl9_73
  <=> ~ r2_hidden(sK5,sK7(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_73])])).

fof(f274,plain,
    ( ~ r2_hidden(sK5,sK7(sK1))
    | ~ spl9_10 ),
    inference(unit_resulting_resolution,[],[f116,f75])).

fof(f426,plain,
    ( ~ spl9_71
    | ~ spl9_8 ),
    inference(avatar_split_clause,[],[f273,f108,f424])).

fof(f424,plain,
    ( spl9_71
  <=> ~ r2_hidden(sK4,sK7(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_71])])).

fof(f273,plain,
    ( ~ r2_hidden(sK4,sK7(sK5))
    | ~ spl9_8 ),
    inference(unit_resulting_resolution,[],[f109,f75])).

fof(f419,plain,
    ( ~ spl9_69
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f272,f101,f417])).

fof(f417,plain,
    ( spl9_69
  <=> ~ r2_hidden(sK3,sK7(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_69])])).

fof(f272,plain,
    ( ~ r2_hidden(sK3,sK7(sK4))
    | ~ spl9_6 ),
    inference(unit_resulting_resolution,[],[f102,f75])).

fof(f412,plain,
    ( ~ spl9_67
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f271,f94,f410])).

fof(f410,plain,
    ( spl9_67
  <=> ~ r2_hidden(sK2,sK7(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_67])])).

fof(f271,plain,
    ( ~ r2_hidden(sK2,sK7(sK3))
    | ~ spl9_4 ),
    inference(unit_resulting_resolution,[],[f95,f75])).

fof(f399,plain,
    ( ~ spl9_65
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f270,f87,f397])).

fof(f397,plain,
    ( spl9_65
  <=> ~ r2_hidden(sK1,sK7(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_65])])).

fof(f270,plain,
    ( ~ r2_hidden(sK1,sK7(sK2))
    | ~ spl9_2 ),
    inference(unit_resulting_resolution,[],[f88,f75])).

fof(f392,plain,
    ( spl9_62
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f268,f115,f390])).

fof(f268,plain,
    ( r2_hidden(sK7(sK1),sK1)
    | ~ spl9_10 ),
    inference(unit_resulting_resolution,[],[f116,f53])).

fof(f385,plain,
    ( spl9_60
    | ~ spl9_8 ),
    inference(avatar_split_clause,[],[f267,f108,f383])).

fof(f267,plain,
    ( r2_hidden(sK7(sK5),sK5)
    | ~ spl9_8 ),
    inference(unit_resulting_resolution,[],[f109,f53])).

fof(f378,plain,
    ( spl9_58
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f266,f101,f376])).

fof(f266,plain,
    ( r2_hidden(sK7(sK4),sK4)
    | ~ spl9_6 ),
    inference(unit_resulting_resolution,[],[f102,f53])).

fof(f371,plain,
    ( spl9_56
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f265,f94,f369])).

fof(f265,plain,
    ( r2_hidden(sK7(sK3),sK3)
    | ~ spl9_4 ),
    inference(unit_resulting_resolution,[],[f95,f53])).

fof(f342,plain,
    ( ~ spl9_55
    | spl9_21
    | spl9_33 ),
    inference(avatar_split_clause,[],[f289,f224,f162,f340])).

fof(f340,plain,
    ( spl9_55
  <=> ~ m1_subset_1(sK1,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_55])])).

fof(f224,plain,
    ( spl9_33
  <=> ~ r2_hidden(sK1,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_33])])).

fof(f289,plain,
    ( ~ m1_subset_1(sK1,sK5)
    | ~ spl9_21
    | ~ spl9_33 ),
    inference(unit_resulting_resolution,[],[f225,f163,f48])).

fof(f225,plain,
    ( ~ r2_hidden(sK1,sK5)
    | ~ spl9_33 ),
    inference(avatar_component_clause,[],[f224])).

fof(f335,plain,
    ( ~ spl9_53
    | spl9_19
    | spl9_31 ),
    inference(avatar_split_clause,[],[f288,f217,f155,f333])).

fof(f333,plain,
    ( spl9_53
  <=> ~ m1_subset_1(sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_53])])).

fof(f217,plain,
    ( spl9_31
  <=> ~ r2_hidden(sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).

fof(f288,plain,
    ( ~ m1_subset_1(sK5,sK4)
    | ~ spl9_19
    | ~ spl9_31 ),
    inference(unit_resulting_resolution,[],[f218,f156,f48])).

fof(f218,plain,
    ( ~ r2_hidden(sK5,sK4)
    | ~ spl9_31 ),
    inference(avatar_component_clause,[],[f217])).

fof(f328,plain,
    ( ~ spl9_51
    | spl9_17
    | spl9_29 ),
    inference(avatar_split_clause,[],[f287,f210,f146,f326])).

fof(f326,plain,
    ( spl9_51
  <=> ~ m1_subset_1(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_51])])).

fof(f210,plain,
    ( spl9_29
  <=> ~ r2_hidden(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).

fof(f287,plain,
    ( ~ m1_subset_1(sK4,sK3)
    | ~ spl9_17
    | ~ spl9_29 ),
    inference(unit_resulting_resolution,[],[f211,f147,f48])).

fof(f211,plain,
    ( ~ r2_hidden(sK4,sK3)
    | ~ spl9_29 ),
    inference(avatar_component_clause,[],[f210])).

fof(f321,plain,
    ( ~ spl9_49
    | spl9_15
    | spl9_27 ),
    inference(avatar_split_clause,[],[f286,f198,f139,f319])).

fof(f319,plain,
    ( spl9_49
  <=> ~ m1_subset_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_49])])).

fof(f198,plain,
    ( spl9_27
  <=> ~ r2_hidden(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).

fof(f286,plain,
    ( ~ m1_subset_1(sK3,sK2)
    | ~ spl9_15
    | ~ spl9_27 ),
    inference(unit_resulting_resolution,[],[f199,f140,f48])).

fof(f199,plain,
    ( ~ r2_hidden(sK3,sK2)
    | ~ spl9_27 ),
    inference(avatar_component_clause,[],[f198])).

fof(f314,plain,
    ( ~ spl9_47
    | spl9_23
    | spl9_25 ),
    inference(avatar_split_clause,[],[f285,f191,f169,f312])).

fof(f312,plain,
    ( spl9_47
  <=> ~ m1_subset_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_47])])).

fof(f191,plain,
    ( spl9_25
  <=> ~ r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).

fof(f285,plain,
    ( ~ m1_subset_1(sK2,sK1)
    | ~ spl9_23
    | ~ spl9_25 ),
    inference(unit_resulting_resolution,[],[f192,f170,f48])).

fof(f192,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ spl9_25 ),
    inference(avatar_component_clause,[],[f191])).

fof(f284,plain,
    ( spl9_44
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f264,f87,f282])).

fof(f264,plain,
    ( r2_hidden(sK7(sK2),sK2)
    | ~ spl9_2 ),
    inference(unit_resulting_resolution,[],[f88,f53])).

fof(f263,plain,
    ( spl9_42
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f205,f115,f261])).

fof(f261,plain,
    ( spl9_42
  <=> m1_subset_1(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_42])])).

fof(f205,plain,
    ( m1_subset_1(sK5,sK1)
    | ~ spl9_10 ),
    inference(unit_resulting_resolution,[],[f116,f50])).

fof(f256,plain,
    ( spl9_40
    | ~ spl9_8 ),
    inference(avatar_split_clause,[],[f204,f108,f254])).

fof(f254,plain,
    ( spl9_40
  <=> m1_subset_1(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_40])])).

fof(f204,plain,
    ( m1_subset_1(sK4,sK5)
    | ~ spl9_8 ),
    inference(unit_resulting_resolution,[],[f109,f50])).

fof(f249,plain,
    ( spl9_38
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f203,f101,f247])).

fof(f247,plain,
    ( spl9_38
  <=> m1_subset_1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_38])])).

fof(f203,plain,
    ( m1_subset_1(sK3,sK4)
    | ~ spl9_6 ),
    inference(unit_resulting_resolution,[],[f102,f50])).

fof(f242,plain,
    ( spl9_36
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f202,f94,f240])).

fof(f240,plain,
    ( spl9_36
  <=> m1_subset_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_36])])).

fof(f202,plain,
    ( m1_subset_1(sK2,sK3)
    | ~ spl9_4 ),
    inference(unit_resulting_resolution,[],[f95,f50])).

fof(f235,plain,
    ( spl9_34
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f201,f87,f233])).

fof(f233,plain,
    ( spl9_34
  <=> m1_subset_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_34])])).

fof(f201,plain,
    ( m1_subset_1(sK1,sK2)
    | ~ spl9_2 ),
    inference(unit_resulting_resolution,[],[f88,f50])).

fof(f226,plain,
    ( ~ spl9_33
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f181,f115,f224])).

fof(f181,plain,
    ( ~ r2_hidden(sK1,sK5)
    | ~ spl9_10 ),
    inference(unit_resulting_resolution,[],[f116,f49])).

fof(f219,plain,
    ( ~ spl9_31
    | ~ spl9_8 ),
    inference(avatar_split_clause,[],[f180,f108,f217])).

fof(f180,plain,
    ( ~ r2_hidden(sK5,sK4)
    | ~ spl9_8 ),
    inference(unit_resulting_resolution,[],[f109,f49])).

fof(f212,plain,
    ( ~ spl9_29
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f179,f101,f210])).

fof(f179,plain,
    ( ~ r2_hidden(sK4,sK3)
    | ~ spl9_6 ),
    inference(unit_resulting_resolution,[],[f102,f49])).

fof(f200,plain,
    ( ~ spl9_27
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f178,f94,f198])).

fof(f178,plain,
    ( ~ r2_hidden(sK3,sK2)
    | ~ spl9_4 ),
    inference(unit_resulting_resolution,[],[f95,f49])).

fof(f193,plain,
    ( ~ spl9_25
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f177,f87,f191])).

fof(f177,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ spl9_2 ),
    inference(unit_resulting_resolution,[],[f88,f49])).

fof(f171,plain,
    ( ~ spl9_23
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f132,f115,f169])).

fof(f132,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl9_10 ),
    inference(unit_resulting_resolution,[],[f116,f52])).

fof(f52,plain,(
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
    file('/export/starexec/sandbox2/benchmark/ordinal1__t5_ordinal1.p',t7_boole)).

fof(f164,plain,
    ( ~ spl9_21
    | ~ spl9_8 ),
    inference(avatar_split_clause,[],[f131,f108,f162])).

fof(f131,plain,
    ( ~ v1_xboole_0(sK5)
    | ~ spl9_8 ),
    inference(unit_resulting_resolution,[],[f109,f52])).

fof(f157,plain,
    ( ~ spl9_19
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f130,f101,f155])).

fof(f130,plain,
    ( ~ v1_xboole_0(sK4)
    | ~ spl9_6 ),
    inference(unit_resulting_resolution,[],[f102,f52])).

fof(f148,plain,
    ( ~ spl9_17
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f129,f94,f146])).

fof(f129,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl9_4 ),
    inference(unit_resulting_resolution,[],[f95,f52])).

fof(f141,plain,
    ( ~ spl9_15
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f128,f87,f139])).

fof(f128,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl9_2 ),
    inference(unit_resulting_resolution,[],[f88,f52])).

fof(f127,plain,
    ( spl9_12
    | ~ spl9_0 ),
    inference(avatar_split_clause,[],[f118,f80,f125])).

fof(f125,plain,
    ( spl9_12
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f80,plain,
    ( spl9_0
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_0])])).

fof(f118,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl9_0 ),
    inference(unit_resulting_resolution,[],[f81,f46])).

fof(f46,plain,(
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
    file('/export/starexec/sandbox2/benchmark/ordinal1__t5_ordinal1.p',t6_boole)).

fof(f81,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl9_0 ),
    inference(avatar_component_clause,[],[f80])).

fof(f117,plain,(
    spl9_10 ),
    inference(avatar_split_clause,[],[f44,f115])).

fof(f44,plain,(
    r2_hidden(sK5,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( r2_hidden(sK5,sK1)
    & r2_hidden(sK4,sK5)
    & r2_hidden(sK3,sK4)
    & r2_hidden(sK2,sK3)
    & r2_hidden(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f16,f28])).

fof(f28,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( r2_hidden(X4,X0)
        & r2_hidden(X3,X4)
        & r2_hidden(X2,X3)
        & r2_hidden(X1,X2)
        & r2_hidden(X0,X1) )
   => ( r2_hidden(sK5,sK1)
      & r2_hidden(sK4,sK5)
      & r2_hidden(sK3,sK4)
      & r2_hidden(sK2,sK3)
      & r2_hidden(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( r2_hidden(X4,X0)
      & r2_hidden(X3,X4)
      & r2_hidden(X2,X3)
      & r2_hidden(X1,X2)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ~ ( r2_hidden(X4,X0)
          & r2_hidden(X3,X4)
          & r2_hidden(X2,X3)
          & r2_hidden(X1,X2)
          & r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ~ ( r2_hidden(X4,X0)
        & r2_hidden(X3,X4)
        & r2_hidden(X2,X3)
        & r2_hidden(X1,X2)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t5_ordinal1.p',t5_ordinal1)).

fof(f110,plain,(
    spl9_8 ),
    inference(avatar_split_clause,[],[f43,f108])).

fof(f43,plain,(
    r2_hidden(sK4,sK5) ),
    inference(cnf_transformation,[],[f29])).

fof(f103,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f42,f101])).

fof(f42,plain,(
    r2_hidden(sK3,sK4) ),
    inference(cnf_transformation,[],[f29])).

fof(f96,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f41,f94])).

fof(f41,plain,(
    r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f89,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f40,f87])).

fof(f40,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f82,plain,(
    spl9_0 ),
    inference(avatar_split_clause,[],[f45,f80])).

fof(f45,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t5_ordinal1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
