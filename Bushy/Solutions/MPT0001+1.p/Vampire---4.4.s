%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : xboole_0__t1_xboole_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:18 EDT 2019

% Result     : Theorem 1.30s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 180 expanded)
%              Number of leaves         :   15 (  62 expanded)
%              Depth                    :   10
%              Number of atoms          :  348 (1076 expanded)
%              Number of equality atoms :   26 (  98 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f130,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f77,f81,f82,f88,f103,f109,f114,f122,f123,f129])).

fof(f129,plain,
    ( spl5_3
    | ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f127])).

fof(f127,plain,
    ( $false
    | ~ spl5_3
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f66,f124])).

fof(f124,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl5_6 ),
    inference(resolution,[],[f94,f57])).

fof(f57,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f22])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_0__t1_xboole_0.p',d5_xboole_0)).

fof(f94,plain,
    ( r2_hidden(sK0,k4_xboole_0(sK2,sK1))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl5_6
  <=> r2_hidden(sK0,k4_xboole_0(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f66,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl5_3
  <=> ~ r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f123,plain,
    ( spl5_6
    | spl5_8
    | ~ spl5_0 ),
    inference(avatar_split_clause,[],[f118,f79,f96,f93])).

fof(f96,plain,
    ( spl5_8
  <=> r2_hidden(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f79,plain,
    ( spl5_0
  <=> r2_hidden(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_0])])).

fof(f118,plain,
    ( r2_hidden(sK0,k4_xboole_0(sK1,sK2))
    | r2_hidden(sK0,k4_xboole_0(sK2,sK1))
    | ~ spl5_0 ),
    inference(resolution,[],[f80,f60])).

fof(f60,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_xboole_0(X0,X1))
      | r2_hidden(X4,X0)
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f26,f27])).

fof(f27,plain,(
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

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_0__t1_xboole_0.p',d3_xboole_0)).

fof(f80,plain,
    ( r2_hidden(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)))
    | ~ spl5_0 ),
    inference(avatar_component_clause,[],[f79])).

fof(f122,plain,
    ( spl5_5
    | ~ spl5_8 ),
    inference(avatar_contradiction_clause,[],[f120])).

fof(f120,plain,
    ( $false
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f73,f115])).

fof(f115,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl5_8 ),
    inference(resolution,[],[f97,f57])).

fof(f97,plain,
    ( r2_hidden(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f96])).

fof(f73,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl5_5
  <=> ~ r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f114,plain,
    ( ~ spl5_5
    | spl5_2
    | spl5_1 ),
    inference(avatar_split_clause,[],[f113,f62,f75,f72])).

fof(f75,plain,
    ( spl5_2
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f62,plain,
    ( spl5_1
  <=> ~ r2_hidden(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f113,plain,
    ( r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK0,sK1)
    | ~ spl5_1 ),
    inference(resolution,[],[f111,f55])).

fof(f55,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f111,plain,
    ( ~ r2_hidden(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl5_1 ),
    inference(resolution,[],[f63,f59])).

fof(f59,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f63,plain,
    ( ~ r2_hidden(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f109,plain,
    ( ~ spl5_4
    | ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f108])).

fof(f108,plain,
    ( $false
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f69,f106])).

fof(f106,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ spl5_6 ),
    inference(resolution,[],[f94,f56])).

fof(f56,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f69,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl5_4
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f103,plain,
    ( ~ spl5_2
    | ~ spl5_8 ),
    inference(avatar_contradiction_clause,[],[f102])).

fof(f102,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f76,f100])).

fof(f100,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ spl5_8 ),
    inference(resolution,[],[f97,f56])).

fof(f76,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f88,plain,
    ( ~ spl5_3
    | spl5_4
    | spl5_1 ),
    inference(avatar_split_clause,[],[f87,f62,f68,f65])).

fof(f87,plain,
    ( r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,sK2)
    | ~ spl5_1 ),
    inference(resolution,[],[f85,f55])).

fof(f85,plain,
    ( ~ r2_hidden(sK0,k4_xboole_0(sK2,sK1))
    | ~ spl5_1 ),
    inference(resolution,[],[f63,f58])).

fof(f58,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f82,plain,
    ( spl5_0
    | spl5_4
    | spl5_2 ),
    inference(avatar_split_clause,[],[f53,f75,f68,f79])).

fof(f53,plain,
    ( r2_hidden(sK0,sK2)
    | r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))) ),
    inference(definition_unfolding,[],[f29,f36])).

fof(f36,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/xboole_0__t1_xboole_0.p',d6_xboole_0)).

fof(f29,plain,
    ( r2_hidden(sK0,sK2)
    | r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k5_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ( ( ( r2_hidden(sK0,sK1)
          | ~ r2_hidden(sK0,sK2) )
        & ( r2_hidden(sK0,sK2)
          | ~ r2_hidden(sK0,sK1) ) )
      | ~ r2_hidden(sK0,k5_xboole_0(sK1,sK2)) )
    & ( ( ( ~ r2_hidden(sK0,sK2)
          | ~ r2_hidden(sK0,sK1) )
        & ( r2_hidden(sK0,sK2)
          | r2_hidden(sK0,sK1) ) )
      | r2_hidden(sK0,k5_xboole_0(sK1,sK2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( ( ( ( r2_hidden(X0,X1)
              | ~ r2_hidden(X0,X2) )
            & ( r2_hidden(X0,X2)
              | ~ r2_hidden(X0,X1) ) )
          | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) )
        & ( ( ( ~ r2_hidden(X0,X2)
              | ~ r2_hidden(X0,X1) )
            & ( r2_hidden(X0,X2)
              | r2_hidden(X0,X1) ) )
          | r2_hidden(X0,k5_xboole_0(X1,X2)) ) )
   => ( ( ( ( r2_hidden(sK0,sK1)
            | ~ r2_hidden(sK0,sK2) )
          & ( r2_hidden(sK0,sK2)
            | ~ r2_hidden(sK0,sK1) ) )
        | ~ r2_hidden(sK0,k5_xboole_0(sK1,sK2)) )
      & ( ( ( ~ r2_hidden(sK0,sK2)
            | ~ r2_hidden(sK0,sK1) )
          & ( r2_hidden(sK0,sK2)
            | r2_hidden(sK0,sK1) ) )
        | r2_hidden(sK0,k5_xboole_0(sK1,sK2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ( ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <~> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,k5_xboole_0(X1,X2))
      <=> ~ ( r2_hidden(X0,X1)
          <=> r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_0__t1_xboole_0.p',t1_xboole_0)).

fof(f81,plain,
    ( spl5_0
    | ~ spl5_5
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f52,f65,f72,f79])).

fof(f52,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))) ),
    inference(definition_unfolding,[],[f30,f36])).

fof(f30,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k5_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f77,plain,
    ( ~ spl5_1
    | ~ spl5_5
    | spl5_2 ),
    inference(avatar_split_clause,[],[f51,f75,f72,f62])).

fof(f51,plain,
    ( r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))) ),
    inference(definition_unfolding,[],[f31,f36])).

fof(f31,plain,
    ( r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,k5_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f70,plain,
    ( ~ spl5_1
    | ~ spl5_3
    | spl5_4 ),
    inference(avatar_split_clause,[],[f50,f68,f65,f62])).

fof(f50,plain,
    ( r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))) ),
    inference(definition_unfolding,[],[f32,f36])).

fof(f32,plain,
    ( r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK0,k5_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
