%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0687+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:28 EST 2020

% Result     : Theorem 1.45s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 214 expanded)
%              Number of leaves         :   30 (  91 expanded)
%              Depth                    :   10
%              Number of atoms          :  458 ( 884 expanded)
%              Number of equality atoms :  101 ( 197 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f456,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f70,f77,f86,f101,f103,f132,f192,f232,f242,f326,f396,f419,f432,f441,f447,f455])).

fof(f455,plain,
    ( ~ spl9_5
    | ~ spl9_7
    | ~ spl9_32 ),
    inference(avatar_contradiction_clause,[],[f454])).

fof(f454,plain,
    ( $false
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_32 ),
    inference(subsumption_resolution,[],[f453,f57])).

fof(f57,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK5(X0,X1) != X0
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sK5(X0,X1) = X0
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f24,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK5(X0,X1) != X0
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sK5(X0,X1) = X0
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f453,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK0))
    | ~ spl9_5
    | ~ spl9_7
    | ~ spl9_32 ),
    inference(subsumption_resolution,[],[f451,f85])).

fof(f85,plain,
    ( ! [X0] : ~ r2_hidden(X0,o_0_0_xboole_0)
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl9_5
  <=> ! [X0] : ~ r2_hidden(X0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f451,plain,
    ( r2_hidden(sK8(sK1,sK0),o_0_0_xboole_0)
    | ~ r2_hidden(sK0,k1_tarski(sK0))
    | ~ spl9_7
    | ~ spl9_32 ),
    inference(superposition,[],[f446,f99])).

fof(f99,plain,
    ( o_0_0_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl9_7
  <=> o_0_0_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f446,plain,
    ( ! [X0] :
        ( r2_hidden(sK8(sK1,sK0),k10_relat_1(sK1,X0))
        | ~ r2_hidden(sK0,X0) )
    | ~ spl9_32 ),
    inference(avatar_component_clause,[],[f445])).

fof(f445,plain,
    ( spl9_32
  <=> ! [X0] :
        ( ~ r2_hidden(sK0,X0)
        | r2_hidden(sK8(sK1,sK0),k10_relat_1(sK1,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).

fof(f447,plain,
    ( spl9_32
    | ~ spl9_9
    | ~ spl9_31 ),
    inference(avatar_split_clause,[],[f442,f438,f130,f445])).

fof(f130,plain,
    ( spl9_9
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,X1)
        | ~ r2_hidden(k4_tarski(X2,X0),sK1)
        | r2_hidden(X2,k10_relat_1(sK1,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f438,plain,
    ( spl9_31
  <=> r2_hidden(k4_tarski(sK8(sK1,sK0),sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).

fof(f442,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK0,X0)
        | r2_hidden(sK8(sK1,sK0),k10_relat_1(sK1,X0)) )
    | ~ spl9_9
    | ~ spl9_31 ),
    inference(resolution,[],[f440,f131])).

fof(f131,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(k4_tarski(X2,X0),sK1)
        | ~ r2_hidden(X0,X1)
        | r2_hidden(X2,k10_relat_1(sK1,X1)) )
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f130])).

fof(f440,plain,
    ( r2_hidden(k4_tarski(sK8(sK1,sK0),sK0),sK1)
    | ~ spl9_31 ),
    inference(avatar_component_clause,[],[f438])).

fof(f441,plain,
    ( spl9_31
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f434,f94,f438])).

fof(f94,plain,
    ( spl9_6
  <=> r2_hidden(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f434,plain,
    ( r2_hidden(k4_tarski(sK8(sK1,sK0),sK0),sK1)
    | ~ spl9_6 ),
    inference(resolution,[],[f96,f60])).

fof(f60,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,k2_relat_1(X0))
      | r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0)
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0)
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK8(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f28,f31,f30,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK6(X0,X1)),X0)
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK6(X0,X1)),X0)
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK6(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK7(X0,X1),sK6(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK8(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f96,plain,
    ( r2_hidden(sK0,k2_relat_1(sK1))
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f94])).

fof(f432,plain,
    ( spl9_6
    | spl9_7
    | ~ spl9_30 ),
    inference(avatar_contradiction_clause,[],[f431])).

fof(f431,plain,
    ( $false
    | spl9_6
    | spl9_7
    | ~ spl9_30 ),
    inference(subsumption_resolution,[],[f426,f100])).

fof(f100,plain,
    ( o_0_0_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0))
    | spl9_7 ),
    inference(avatar_component_clause,[],[f98])).

fof(f426,plain,
    ( o_0_0_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
    | spl9_6
    | ~ spl9_30 ),
    inference(resolution,[],[f418,f95])).

fof(f95,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK1))
    | spl9_6 ),
    inference(avatar_component_clause,[],[f94])).

fof(f418,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_relat_1(sK1))
        | o_0_0_xboole_0 = k10_relat_1(sK1,k1_tarski(X0)) )
    | ~ spl9_30 ),
    inference(avatar_component_clause,[],[f417])).

fof(f417,plain,
    ( spl9_30
  <=> ! [X0] :
        ( r2_hidden(X0,k2_relat_1(sK1))
        | o_0_0_xboole_0 = k10_relat_1(sK1,k1_tarski(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).

fof(f419,plain,
    ( spl9_30
    | ~ spl9_5
    | ~ spl9_24
    | ~ spl9_29 ),
    inference(avatar_split_clause,[],[f415,f394,f324,f84,f417])).

fof(f324,plain,
    ( spl9_24
  <=> ! [X2] :
        ( o_0_0_xboole_0 = k10_relat_1(sK1,k1_tarski(X2))
        | sK3(sK1,k1_tarski(X2),o_0_0_xboole_0) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).

fof(f394,plain,
    ( spl9_29
  <=> ! [X3,X4] :
        ( r2_hidden(sK2(sK1,X3,X4),X4)
        | k10_relat_1(sK1,X3) = X4
        | r2_hidden(sK3(sK1,X3,X4),k2_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).

fof(f415,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_relat_1(sK1))
        | o_0_0_xboole_0 = k10_relat_1(sK1,k1_tarski(X0)) )
    | ~ spl9_5
    | ~ spl9_24
    | ~ spl9_29 ),
    inference(subsumption_resolution,[],[f412,f85])).

fof(f412,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_relat_1(sK1))
        | r2_hidden(sK2(sK1,k1_tarski(X0),o_0_0_xboole_0),o_0_0_xboole_0)
        | o_0_0_xboole_0 = k10_relat_1(sK1,k1_tarski(X0)) )
    | ~ spl9_24
    | ~ spl9_29 ),
    inference(duplicate_literal_removal,[],[f411])).

fof(f411,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_relat_1(sK1))
        | r2_hidden(sK2(sK1,k1_tarski(X0),o_0_0_xboole_0),o_0_0_xboole_0)
        | o_0_0_xboole_0 = k10_relat_1(sK1,k1_tarski(X0))
        | o_0_0_xboole_0 = k10_relat_1(sK1,k1_tarski(X0)) )
    | ~ spl9_24
    | ~ spl9_29 ),
    inference(superposition,[],[f395,f325])).

fof(f325,plain,
    ( ! [X2] :
        ( sK3(sK1,k1_tarski(X2),o_0_0_xboole_0) = X2
        | o_0_0_xboole_0 = k10_relat_1(sK1,k1_tarski(X2)) )
    | ~ spl9_24 ),
    inference(avatar_component_clause,[],[f324])).

fof(f395,plain,
    ( ! [X4,X3] :
        ( r2_hidden(sK2(sK1,X3,X4),X4)
        | r2_hidden(sK3(sK1,X3,X4),k2_relat_1(sK1))
        | k10_relat_1(sK1,X3) = X4 )
    | ~ spl9_29 ),
    inference(avatar_component_clause,[],[f394])).

fof(f396,plain,
    ( spl9_29
    | ~ spl9_17 ),
    inference(avatar_split_clause,[],[f238,f230,f394])).

fof(f230,plain,
    ( spl9_17
  <=> ! [X1,X0] :
        ( r2_hidden(k4_tarski(sK2(sK1,X0,X1),sK3(sK1,X0,X1)),sK1)
        | r2_hidden(sK2(sK1,X0,X1),X1)
        | k10_relat_1(sK1,X0) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f238,plain,
    ( ! [X4,X3] :
        ( r2_hidden(sK2(sK1,X3,X4),X4)
        | k10_relat_1(sK1,X3) = X4
        | r2_hidden(sK3(sK1,X3,X4),k2_relat_1(sK1)) )
    | ~ spl9_17 ),
    inference(resolution,[],[f231,f59])).

fof(f59,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X6,X5),X0)
      | r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f231,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(sK2(sK1,X0,X1),sK3(sK1,X0,X1)),sK1)
        | r2_hidden(sK2(sK1,X0,X1),X1)
        | k10_relat_1(sK1,X0) = X1 )
    | ~ spl9_17 ),
    inference(avatar_component_clause,[],[f230])).

fof(f326,plain,
    ( spl9_24
    | ~ spl9_19 ),
    inference(avatar_split_clause,[],[f295,f240,f324])).

fof(f240,plain,
    ( spl9_19
  <=> ! [X10] :
        ( r2_hidden(sK3(sK1,X10,o_0_0_xboole_0),X10)
        | o_0_0_xboole_0 = k10_relat_1(sK1,X10) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f295,plain,
    ( ! [X2] :
        ( o_0_0_xboole_0 = k10_relat_1(sK1,k1_tarski(X2))
        | sK3(sK1,k1_tarski(X2),o_0_0_xboole_0) = X2 )
    | ~ spl9_19 ),
    inference(resolution,[],[f241,f58])).

fof(f58,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f241,plain,
    ( ! [X10] :
        ( r2_hidden(sK3(sK1,X10,o_0_0_xboole_0),X10)
        | o_0_0_xboole_0 = k10_relat_1(sK1,X10) )
    | ~ spl9_19 ),
    inference(avatar_component_clause,[],[f240])).

fof(f242,plain,
    ( spl9_19
    | ~ spl9_5
    | ~ spl9_15 ),
    inference(avatar_split_clause,[],[f203,f190,f84,f240])).

fof(f190,plain,
    ( spl9_15
  <=> ! [X1,X0] :
        ( r2_hidden(sK3(sK1,X0,X1),X0)
        | r2_hidden(sK2(sK1,X0,X1),X1)
        | k10_relat_1(sK1,X0) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f203,plain,
    ( ! [X10] :
        ( r2_hidden(sK3(sK1,X10,o_0_0_xboole_0),X10)
        | o_0_0_xboole_0 = k10_relat_1(sK1,X10) )
    | ~ spl9_5
    | ~ spl9_15 ),
    inference(resolution,[],[f191,f85])).

fof(f191,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(sK1,X0,X1),X0)
        | r2_hidden(sK2(sK1,X0,X1),X1)
        | k10_relat_1(sK1,X0) = X1 )
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f190])).

fof(f232,plain,
    ( spl9_17
    | ~ spl9_1 ),
    inference(avatar_split_clause,[],[f153,f62,f230])).

fof(f62,plain,
    ( spl9_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f153,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(sK2(sK1,X0,X1),sK3(sK1,X0,X1)),sK1)
        | r2_hidden(sK2(sK1,X0,X1),X1)
        | k10_relat_1(sK1,X0) = X1 )
    | ~ spl9_1 ),
    inference(resolution,[],[f40,f64])).

fof(f64,plain,
    ( v1_relat_1(sK1)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | k10_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),X4),X0) )
                | ~ r2_hidden(sK2(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK3(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0) )
                | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ( r2_hidden(sK4(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(X6,sK4(X0,X1,X6)),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f18,f21,f20,f19])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r2_hidden(k4_tarski(X3,X4),X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X3,X5),X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),X4),X0) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0) )
     => ( r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X6,X8),X0) )
     => ( r2_hidden(sK4(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(X6,sK4(X0,X1,X6)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( r2_hidden(X5,X1)
                      & r2_hidden(k4_tarski(X3,X5),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ? [X8] :
                      ( r2_hidden(X8,X1)
                      & r2_hidden(k4_tarski(X6,X8),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) ) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

fof(f192,plain,
    ( spl9_15
    | ~ spl9_1 ),
    inference(avatar_split_clause,[],[f146,f62,f190])).

fof(f146,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(sK1,X0,X1),X0)
        | r2_hidden(sK2(sK1,X0,X1),X1)
        | k10_relat_1(sK1,X0) = X1 )
    | ~ spl9_1 ),
    inference(resolution,[],[f41,f64])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | k10_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f132,plain,
    ( spl9_9
    | ~ spl9_1 ),
    inference(avatar_split_clause,[],[f121,f62,f130])).

fof(f121,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ r2_hidden(k4_tarski(X2,X0),sK1)
        | r2_hidden(X2,k10_relat_1(sK1,X1)) )
    | ~ spl9_1 ),
    inference(resolution,[],[f53,f64])).

fof(f53,plain,(
    ! [X6,X0,X7,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | r2_hidden(X6,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f103,plain,
    ( ~ spl9_6
    | ~ spl9_3
    | spl9_7 ),
    inference(avatar_split_clause,[],[f102,f98,f74,f94])).

fof(f74,plain,
    ( spl9_3
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f102,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK1))
    | ~ spl9_3
    | spl9_7 ),
    inference(subsumption_resolution,[],[f92,f100])).

fof(f92,plain,
    ( o_0_0_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
    | ~ r2_hidden(sK0,k2_relat_1(sK1))
    | ~ spl9_3 ),
    inference(forward_demodulation,[],[f35,f76])).

fof(f76,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f74])).

fof(f35,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
    | ~ r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ( k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
      | ~ r2_hidden(sK0,k2_relat_1(sK1)) )
    & ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0))
      | r2_hidden(sK0,k2_relat_1(sK1)) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).

fof(f15,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
          | ~ r2_hidden(X0,k2_relat_1(X1)) )
        & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
          | r2_hidden(X0,k2_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
        | ~ r2_hidden(sK0,k2_relat_1(sK1)) )
      & ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0))
        | r2_hidden(sK0,k2_relat_1(sK1)) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
        | ~ r2_hidden(X0,k2_relat_1(X1)) )
      & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
        | r2_hidden(X0,k2_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
        | ~ r2_hidden(X0,k2_relat_1(X1)) )
      & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
        | r2_hidden(X0,k2_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k2_relat_1(X1))
      <~> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k2_relat_1(X1))
        <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k2_relat_1(X1))
      <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

fof(f101,plain,
    ( spl9_6
    | ~ spl9_7
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f90,f74,f98,f94])).

fof(f90,plain,
    ( o_0_0_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0))
    | r2_hidden(sK0,k2_relat_1(sK1))
    | ~ spl9_3 ),
    inference(forward_demodulation,[],[f34,f76])).

fof(f34,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0))
    | r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f86,plain,
    ( spl9_5
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f78,f67,f84])).

fof(f67,plain,
    ( spl9_2
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f78,plain,
    ( ! [X0] : ~ r2_hidden(X0,o_0_0_xboole_0)
    | ~ spl9_2 ),
    inference(resolution,[],[f52,f69])).

fof(f69,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(f77,plain,
    ( spl9_3
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f71,f67,f74])).

fof(f71,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl9_2 ),
    inference(resolution,[],[f43,f69])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(f70,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f36,f67])).

fof(f36,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f65,plain,(
    spl9_1 ),
    inference(avatar_split_clause,[],[f33,f62])).

fof(f33,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

%------------------------------------------------------------------------------
