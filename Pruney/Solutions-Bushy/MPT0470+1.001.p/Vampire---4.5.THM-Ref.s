%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0470+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:02 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 153 expanded)
%              Number of leaves         :   20 (  63 expanded)
%              Depth                    :    8
%              Number of atoms          :  237 ( 472 expanded)
%              Number of equality atoms :   26 (  52 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f232,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f56,f61,f67,f86,f91,f129,f134,f229,f231])).

fof(f231,plain,
    ( ~ spl7_4
    | spl7_14 ),
    inference(avatar_contradiction_clause,[],[f230])).

fof(f230,plain,
    ( $false
    | ~ spl7_4
    | spl7_14 ),
    inference(subsumption_resolution,[],[f200,f164])).

fof(f164,plain,
    ( ! [X2,X0,X1] : ~ sP0(k1_xboole_0,X0,X1,X2)
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f68,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X1,X2,X3),X1),X0)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ! [X4] :
            ( ~ r2_hidden(k4_tarski(X4,X1),X0)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
      & ( ( r2_hidden(k4_tarski(sK6(X0,X1,X2,X3),X1),X0)
          & r2_hidden(k4_tarski(X3,sK6(X0,X1,X2,X3)),X2) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f24,f25])).

fof(f25,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(k4_tarski(X5,X1),X0)
          & r2_hidden(k4_tarski(X3,X5),X2) )
     => ( r2_hidden(k4_tarski(sK6(X0,X1,X2,X3),X1),X0)
        & r2_hidden(k4_tarski(X3,sK6(X0,X1,X2,X3)),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ! [X4] :
            ( ~ r2_hidden(k4_tarski(X4,X1),X0)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
      & ( ? [X5] :
            ( r2_hidden(k4_tarski(X5,X1),X0)
            & r2_hidden(k4_tarski(X3,X5),X2) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X1,X4,X0,X3] :
      ( ( sP0(X1,X4,X0,X3)
        | ! [X5] :
            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
            | ~ r2_hidden(k4_tarski(X3,X5),X0) ) )
      & ( ? [X5] :
            ( r2_hidden(k4_tarski(X5,X4),X1)
            & r2_hidden(k4_tarski(X3,X5),X0) )
        | ~ sP0(X1,X4,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X1,X4,X0,X3] :
      ( sP0(X1,X4,X0,X3)
    <=> ? [X5] :
          ( r2_hidden(k4_tarski(X5,X4),X1)
          & r2_hidden(k4_tarski(X3,X5),X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f68,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f60,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(f60,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl7_4
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f200,plain,
    ( sP0(k1_xboole_0,sK5(sK3,k1_xboole_0,k1_xboole_0),sK3,sK4(sK3,k1_xboole_0,k1_xboole_0))
    | ~ spl7_4
    | spl7_14 ),
    inference(unit_resulting_resolution,[],[f128,f68,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,sK5(X0,X1,X2),X0,sK4(X0,X1,X2))
      | sP1(X0,X1,X2)
      | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ~ sP0(X1,sK5(X0,X1,X2),X0,sK4(X0,X1,X2))
            | ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) )
          & ( sP0(X1,sK5(X0,X1,X2),X0,sK4(X0,X1,X2))
            | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) ) ) )
      & ( ! [X5,X6] :
            ( ( r2_hidden(k4_tarski(X5,X6),X2)
              | ~ sP0(X1,X6,X0,X5) )
            & ( sP0(X1,X6,X0,X5)
              | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f20,f21])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ sP0(X1,X4,X0,X3)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( sP0(X1,X4,X0,X3)
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ sP0(X1,sK5(X0,X1,X2),X0,sK4(X0,X1,X2))
          | ~ r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) )
        & ( sP0(X1,sK5(X0,X1,X2),X0,sK4(X0,X1,X2))
          | r2_hidden(k4_tarski(sK4(X0,X1,X2),sK5(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3,X4] :
            ( ( ~ sP0(X1,X4,X0,X3)
              | ~ r2_hidden(k4_tarski(X3,X4),X2) )
            & ( sP0(X1,X4,X0,X3)
              | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
      & ( ! [X5,X6] :
            ( ( r2_hidden(k4_tarski(X5,X6),X2)
              | ~ sP0(X1,X6,X0,X5) )
            & ( sP0(X1,X6,X0,X5)
              | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3,X4] :
            ( ( ~ sP0(X1,X4,X0,X3)
              | ~ r2_hidden(k4_tarski(X3,X4),X2) )
            & ( sP0(X1,X4,X0,X3)
              | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
      & ( ! [X3,X4] :
            ( ( r2_hidden(k4_tarski(X3,X4),X2)
              | ~ sP0(X1,X4,X0,X3) )
            & ( sP0(X1,X4,X0,X3)
              | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
    <=> ! [X3,X4] :
          ( r2_hidden(k4_tarski(X3,X4),X2)
        <=> sP0(X1,X4,X0,X3) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f128,plain,
    ( ~ sP1(sK3,k1_xboole_0,k1_xboole_0)
    | spl7_14 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl7_14
  <=> sP1(sK3,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f229,plain,
    ( ~ spl7_4
    | spl7_15 ),
    inference(avatar_contradiction_clause,[],[f228])).

fof(f228,plain,
    ( $false
    | ~ spl7_4
    | spl7_15 ),
    inference(subsumption_resolution,[],[f201,f157])).

fof(f157,plain,
    ( ! [X2,X0,X1] : ~ sP0(X0,X1,k1_xboole_0,X2)
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f68,f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X3,sK6(X0,X1,X2,X3)),X2)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f201,plain,
    ( sP0(sK3,sK5(k1_xboole_0,sK3,k1_xboole_0),k1_xboole_0,sK4(k1_xboole_0,sK3,k1_xboole_0))
    | ~ spl7_4
    | spl7_15 ),
    inference(unit_resulting_resolution,[],[f133,f68,f35])).

fof(f133,plain,
    ( ~ sP1(k1_xboole_0,sK3,k1_xboole_0)
    | spl7_15 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl7_15
  <=> sP1(k1_xboole_0,sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f134,plain,
    ( ~ spl7_15
    | spl7_1
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f118,f88,f44,f131])).

fof(f44,plain,
    ( spl7_1
  <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f88,plain,
    ( spl7_8
  <=> sP2(k1_xboole_0,sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f118,plain,
    ( ~ sP1(k1_xboole_0,sK3,k1_xboole_0)
    | spl7_1
    | ~ spl7_8 ),
    inference(unit_resulting_resolution,[],[f90,f46,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,X1) = X0
      | ~ sP1(X2,X1,X0)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( ( k5_relat_1(X2,X1) = X0
          | ~ sP1(X2,X1,X0) )
        & ( sP1(X2,X1,X0)
          | k5_relat_1(X2,X1) != X0 ) )
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ( ( k5_relat_1(X0,X1) = X2
          | ~ sP1(X0,X1,X2) )
        & ( sP1(X0,X1,X2)
          | k5_relat_1(X0,X1) != X2 ) )
      | ~ sP2(X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X2,X1,X0] :
      ( ( k5_relat_1(X0,X1) = X2
      <=> sP1(X0,X1,X2) )
      | ~ sP2(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f46,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK3)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f90,plain,
    ( sP2(k1_xboole_0,sK3,k1_xboole_0)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f88])).

fof(f129,plain,
    ( ~ spl7_14
    | spl7_2
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f119,f83,f48,f126])).

fof(f48,plain,
    ( spl7_2
  <=> k1_xboole_0 = k5_relat_1(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f83,plain,
    ( spl7_7
  <=> sP2(k1_xboole_0,k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f119,plain,
    ( ~ sP1(sK3,k1_xboole_0,k1_xboole_0)
    | spl7_2
    | ~ spl7_7 ),
    inference(unit_resulting_resolution,[],[f85,f50,f32])).

fof(f50,plain,
    ( k1_xboole_0 != k5_relat_1(sK3,k1_xboole_0)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f48])).

fof(f85,plain,
    ( sP2(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f83])).

fof(f91,plain,
    ( spl7_8
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f74,f64,f53,f88])).

fof(f53,plain,
    ( spl7_3
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f64,plain,
    ( spl7_5
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f74,plain,
    ( sP2(k1_xboole_0,sK3,k1_xboole_0)
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(unit_resulting_resolution,[],[f66,f55,f66,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( sP2(X2,X1,X0)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP2(X2,X1,X0)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f9,f13,f12,f11])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).

fof(f55,plain,
    ( v1_relat_1(sK3)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f53])).

fof(f66,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f64])).

fof(f86,plain,
    ( spl7_7
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f75,f64,f53,f83])).

fof(f75,plain,
    ( sP2(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(unit_resulting_resolution,[],[f55,f66,f66,f40])).

fof(f67,plain,
    ( spl7_5
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f62,f58,f64])).

fof(f62,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f60,f30])).

fof(f30,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f61,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f29,f58])).

fof(f29,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f56,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f27,f53])).

fof(f27,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK3,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK3) )
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f7,f15])).

fof(f15,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK3,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK3) )
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

fof(f51,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f28,f48,f44])).

fof(f28,plain,
    ( k1_xboole_0 != k5_relat_1(sK3,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK3) ),
    inference(cnf_transformation,[],[f16])).

%------------------------------------------------------------------------------
