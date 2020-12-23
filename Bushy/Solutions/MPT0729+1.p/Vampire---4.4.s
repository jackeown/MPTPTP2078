%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : ordinal1__t12_ordinal1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:24 EDT 2019

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 171 expanded)
%              Number of leaves         :   24 (  71 expanded)
%              Depth                    :   10
%              Number of atoms          :  264 ( 522 expanded)
%              Number of equality atoms :   58 ( 123 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f158,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f85,f91,f95,f105,f120,f121,f125,f129,f133,f138,f148,f149,f153,f157])).

fof(f157,plain,
    ( ~ spl5_23
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f141,f131,f155])).

fof(f155,plain,
    ( spl5_23
  <=> ~ v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f131,plain,
    ( spl5_16
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f141,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl5_16 ),
    inference(unit_resulting_resolution,[],[f132,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t12_ordinal1.p',t7_boole)).

fof(f132,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f131])).

fof(f153,plain,
    ( spl5_20
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f142,f131,f151])).

fof(f151,plain,
    ( spl5_20
  <=> m1_subset_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f142,plain,
    ( m1_subset_1(sK1,sK0)
    | ~ spl5_16 ),
    inference(unit_resulting_resolution,[],[f132,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t12_ordinal1.p',t1_subset)).

fof(f149,plain,
    ( ~ spl5_19
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f143,f131,f146])).

fof(f146,plain,
    ( spl5_19
  <=> ~ r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f143,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ spl5_16 ),
    inference(unit_resulting_resolution,[],[f132,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t12_ordinal1.p',antisymmetry_r2_hidden)).

fof(f148,plain,
    ( ~ spl5_19
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f144,f131,f146])).

fof(f144,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ spl5_16 ),
    inference(unit_resulting_resolution,[],[f132,f56])).

fof(f138,plain,
    ( spl5_18
    | ~ spl5_2
    | spl5_5 ),
    inference(avatar_split_clause,[],[f134,f89,f83,f136])).

fof(f136,plain,
    ( spl5_18
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f83,plain,
    ( spl5_2
  <=> k2_xboole_0(sK0,k1_tarski(sK0)) = k2_xboole_0(sK1,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f89,plain,
    ( spl5_5
  <=> ~ r2_hidden(sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f134,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f90,f71,f101])).

fof(f101,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_xboole_0(sK0,k1_tarski(sK0)))
        | r2_hidden(X0,sK1)
        | r2_hidden(X0,k1_tarski(sK1)) )
    | ~ spl5_2 ),
    inference(superposition,[],[f77,f84])).

fof(f84,plain,
    ( k2_xboole_0(sK0,k1_tarski(sK0)) = k2_xboole_0(sK1,k1_tarski(sK1))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f77,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_xboole_0(X0,X1))
      | r2_hidden(X4,X0)
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & ~ r2_hidden(sK4(X0,X1,X2),X0) )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( r2_hidden(sK4(X0,X1,X2),X1)
            | r2_hidden(sK4(X0,X1,X2),X0)
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f42,f43])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & ~ r2_hidden(sK4(X0,X1,X2),X0) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( r2_hidden(sK4(X0,X1,X2),X1)
          | r2_hidden(sK4(X0,X1,X2),X0)
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t12_ordinal1.p',d3_xboole_0)).

fof(f71,plain,(
    ! [X0] : r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f48,f50])).

fof(f50,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t12_ordinal1.p',d1_ordinal1)).

fof(f48,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t12_ordinal1.p',t10_ordinal1)).

fof(f90,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK1))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f89])).

fof(f133,plain,
    ( spl5_16
    | spl5_7
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f110,f103,f93,f131])).

fof(f93,plain,
    ( spl5_7
  <=> ~ r2_hidden(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f103,plain,
    ( spl5_8
  <=> r2_hidden(sK1,k2_xboole_0(sK0,k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f110,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(unit_resulting_resolution,[],[f94,f104,f77])).

fof(f104,plain,
    ( r2_hidden(sK1,k2_xboole_0(sK0,k1_tarski(sK0)))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f103])).

fof(f94,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK0))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f93])).

fof(f129,plain,
    ( ~ spl5_15
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f113,f103,f127])).

fof(f127,plain,
    ( spl5_15
  <=> ~ v1_xboole_0(k2_xboole_0(sK0,k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f113,plain,
    ( ~ v1_xboole_0(k2_xboole_0(sK0,k1_tarski(sK0)))
    | ~ spl5_8 ),
    inference(unit_resulting_resolution,[],[f104,f63])).

fof(f125,plain,
    ( spl5_12
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f114,f103,f123])).

fof(f123,plain,
    ( spl5_12
  <=> m1_subset_1(sK1,k2_xboole_0(sK0,k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f114,plain,
    ( m1_subset_1(sK1,k2_xboole_0(sK0,k1_tarski(sK0)))
    | ~ spl5_8 ),
    inference(unit_resulting_resolution,[],[f104,f57])).

fof(f121,plain,
    ( ~ spl5_11
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f115,f103,f118])).

fof(f118,plain,
    ( spl5_11
  <=> ~ r2_hidden(k2_xboole_0(sK0,k1_tarski(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f115,plain,
    ( ~ r2_hidden(k2_xboole_0(sK0,k1_tarski(sK0)),sK1)
    | ~ spl5_8 ),
    inference(unit_resulting_resolution,[],[f104,f56])).

fof(f120,plain,
    ( ~ spl5_11
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f116,f103,f118])).

fof(f116,plain,
    ( ~ r2_hidden(k2_xboole_0(sK0,k1_tarski(sK0)),sK1)
    | ~ spl5_8 ),
    inference(unit_resulting_resolution,[],[f104,f56])).

fof(f105,plain,
    ( spl5_8
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f100,f83,f103])).

fof(f100,plain,
    ( r2_hidden(sK1,k2_xboole_0(sK0,k1_tarski(sK0)))
    | ~ spl5_2 ),
    inference(superposition,[],[f71,f84])).

fof(f95,plain,
    ( ~ spl5_7
    | spl5_1 ),
    inference(avatar_split_clause,[],[f86,f79,f93])).

fof(f79,plain,
    ( spl5_1
  <=> sK0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f86,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK0))
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f80,f74])).

fof(f74,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f37,f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t12_ordinal1.p',d1_tarski)).

fof(f80,plain,
    ( sK0 != sK1
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f79])).

fof(f91,plain,
    ( ~ spl5_5
    | spl5_1 ),
    inference(avatar_split_clause,[],[f87,f79,f89])).

fof(f87,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK1))
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f80,f74])).

fof(f85,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f70,f83])).

fof(f70,plain,(
    k2_xboole_0(sK0,k1_tarski(sK0)) = k2_xboole_0(sK1,k1_tarski(sK1)) ),
    inference(definition_unfolding,[],[f45,f50,f50])).

fof(f45,plain,(
    k1_ordinal1(sK0) = k1_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( sK0 != sK1
    & k1_ordinal1(sK0) = k1_ordinal1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f32])).

fof(f32,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_ordinal1(X0) = k1_ordinal1(X1) )
   => ( sK0 != sK1
      & k1_ordinal1(sK0) = k1_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_ordinal1(X0) = k1_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_ordinal1(X0) = k1_ordinal1(X1)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( k1_ordinal1(X0) = k1_ordinal1(X1)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t12_ordinal1.p',t12_ordinal1)).

fof(f81,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f46,f79])).

fof(f46,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
