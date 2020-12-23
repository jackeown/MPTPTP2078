%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:02 EST 2020

% Result     : Theorem 1.21s
% Output     : Refutation 1.21s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 180 expanded)
%              Number of leaves         :   12 (  62 expanded)
%              Depth                    :   10
%              Number of atoms          :  342 (1076 expanded)
%              Number of equality atoms :   26 (  98 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f124,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f73,f75,f76,f82,f97,f103,f108,f116,f117,f123])).

fof(f123,plain,
    ( spl5_2
    | ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f121])).

fof(f121,plain,
    ( $false
    | spl5_2
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f66,f118])).

fof(f118,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl5_4 ),
    inference(resolution,[],[f88,f57])).

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
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f88,plain,
    ( r2_hidden(sK0,k4_xboole_0(sK2,sK1))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl5_4
  <=> r2_hidden(sK0,k4_xboole_0(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f66,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl5_2
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f117,plain,
    ( spl5_4
    | spl5_5
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f112,f62,f90,f87])).

fof(f90,plain,
    ( spl5_5
  <=> r2_hidden(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f62,plain,
    ( spl5_1
  <=> r2_hidden(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f112,plain,
    ( r2_hidden(sK0,k4_xboole_0(sK1,sK2))
    | r2_hidden(sK0,k4_xboole_0(sK2,sK1))
    | ~ spl5_1 ),
    inference(resolution,[],[f74,f60])).

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
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f74,plain,
    ( r2_hidden(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f116,plain,
    ( spl5_3
    | ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f114])).

fof(f114,plain,
    ( $false
    | spl5_3
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f71,f109])).

fof(f109,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl5_5 ),
    inference(resolution,[],[f91,f57])).

fof(f91,plain,
    ( r2_hidden(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f90])).

fof(f71,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl5_3
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f108,plain,
    ( ~ spl5_3
    | spl5_2
    | spl5_1 ),
    inference(avatar_split_clause,[],[f107,f62,f65,f68])).

fof(f107,plain,
    ( r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK0,sK1)
    | spl5_1 ),
    inference(resolution,[],[f105,f55])).

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

fof(f105,plain,
    ( ~ r2_hidden(sK0,k4_xboole_0(sK1,sK2))
    | spl5_1 ),
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
    | spl5_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f103,plain,
    ( ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f102])).

fof(f102,plain,
    ( $false
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f69,f100])).

fof(f100,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ spl5_4 ),
    inference(resolution,[],[f88,f56])).

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
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f68])).

fof(f97,plain,
    ( ~ spl5_2
    | ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f96])).

fof(f96,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f72,f94])).

fof(f94,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ spl5_5 ),
    inference(resolution,[],[f91,f56])).

fof(f72,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f82,plain,
    ( ~ spl5_2
    | spl5_3
    | spl5_1 ),
    inference(avatar_split_clause,[],[f81,f62,f68,f65])).

fof(f81,plain,
    ( r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,sK2)
    | spl5_1 ),
    inference(resolution,[],[f79,f55])).

fof(f79,plain,
    ( ~ r2_hidden(sK0,k4_xboole_0(sK2,sK1))
    | spl5_1 ),
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

fof(f76,plain,
    ( spl5_1
    | spl5_3
    | spl5_2 ),
    inference(avatar_split_clause,[],[f53,f65,f68,f62])).

fof(f53,plain,
    ( r2_hidden(sK0,sK2)
    | r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))) ),
    inference(definition_unfolding,[],[f29,f36])).

fof(f36,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

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
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,k5_xboole_0(X1,X2))
      <=> ~ ( r2_hidden(X0,X1)
          <=> r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f75,plain,
    ( spl5_1
    | ~ spl5_3
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f52,f65,f68,f62])).

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

fof(f73,plain,
    ( ~ spl5_1
    | ~ spl5_3
    | spl5_2 ),
    inference(avatar_split_clause,[],[f51,f65,f68,f62])).

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
    | ~ spl5_2
    | spl5_3 ),
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
