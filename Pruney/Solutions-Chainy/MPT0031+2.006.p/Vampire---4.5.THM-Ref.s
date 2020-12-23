%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 238 expanded)
%              Number of leaves         :   14 (  88 expanded)
%              Depth                    :   10
%              Number of atoms          :  314 (1396 expanded)
%              Number of equality atoms :   35 ( 177 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f238,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f62,f63,f83,f145,f146,f152,f186,f190,f191,f204,f205,f206,f207,f237])).

fof(f237,plain,
    ( spl6_2
    | spl6_5
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f232,f95,f80,f54])).

fof(f54,plain,
    ( spl6_2
  <=> r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f80,plain,
    ( spl6_5
  <=> r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f95,plain,
    ( spl6_7
  <=> r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k2_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f232,plain,
    ( r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),sK2)
    | r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),sK0)
    | ~ spl6_7 ),
    inference(resolution,[],[f96,f36])).

fof(f36,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f15,f16])).

fof(f16,plain,(
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

fof(f15,plain,(
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
    inference(rectify,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f96,plain,
    ( r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k2_xboole_0(sK0,sK2))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f95])).

fof(f207,plain,
    ( ~ spl6_5
    | spl6_7 ),
    inference(avatar_split_clause,[],[f181,f95,f80])).

fof(f181,plain,
    ( ~ r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),sK2)
    | spl6_7 ),
    inference(resolution,[],[f97,f34])).

fof(f34,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f97,plain,
    ( ~ r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k2_xboole_0(sK0,sK2))
    | spl6_7 ),
    inference(avatar_component_clause,[],[f95])).

fof(f206,plain,
    ( ~ spl6_4
    | spl6_6 ),
    inference(avatar_split_clause,[],[f121,f91,f76])).

fof(f76,plain,
    ( spl6_4
  <=> r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f91,plain,
    ( spl6_6
  <=> r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f121,plain,
    ( ~ r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),sK1)
    | spl6_6 ),
    inference(resolution,[],[f93,f34])).

fof(f93,plain,
    ( ~ r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k2_xboole_0(sK0,sK1))
    | spl6_6 ),
    inference(avatar_component_clause,[],[f91])).

fof(f205,plain,
    ( spl6_5
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f199,f58,f80])).

fof(f58,plain,
    ( spl6_3
  <=> r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f199,plain,
    ( r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),sK2)
    | ~ spl6_3 ),
    inference(resolution,[],[f60,f32])).

fof(f32,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f11])).

fof(f11,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f60,plain,
    ( r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k3_xboole_0(sK1,sK2))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f204,plain,
    ( spl6_4
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f198,f58,f76])).

fof(f198,plain,
    ( r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),sK1)
    | ~ spl6_3 ),
    inference(resolution,[],[f60,f33])).

fof(f33,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f191,plain,
    ( ~ spl6_2
    | spl6_6 ),
    inference(avatar_split_clause,[],[f120,f91,f54])).

fof(f120,plain,
    ( ~ r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),sK0)
    | spl6_6 ),
    inference(resolution,[],[f93,f35])).

fof(f35,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f190,plain,
    ( ~ spl6_6
    | ~ spl6_7
    | spl6_1 ),
    inference(avatar_split_clause,[],[f85,f50,f95,f91])).

fof(f50,plain,
    ( spl6_1
  <=> r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f85,plain,
    ( ~ r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k2_xboole_0(sK0,sK2))
    | ~ r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k2_xboole_0(sK0,sK1))
    | spl6_1 ),
    inference(resolution,[],[f51,f31])).

fof(f31,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f51,plain,
    ( ~ r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f186,plain,
    ( ~ spl6_2
    | spl6_7 ),
    inference(avatar_contradiction_clause,[],[f179])).

fof(f179,plain,
    ( $false
    | ~ spl6_2
    | spl6_7 ),
    inference(resolution,[],[f97,f65])).

fof(f65,plain,
    ( ! [X0] : r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k2_xboole_0(sK0,X0))
    | ~ spl6_2 ),
    inference(resolution,[],[f56,f35])).

fof(f56,plain,
    ( r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f152,plain,
    ( spl6_2
    | spl6_4
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f147,f91,f76,f54])).

fof(f147,plain,
    ( r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),sK1)
    | r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),sK0)
    | ~ spl6_6 ),
    inference(resolution,[],[f92,f36])).

fof(f92,plain,
    ( r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k2_xboole_0(sK0,sK1))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f91])).

fof(f146,plain,
    ( spl6_7
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f140,f50,f95])).

fof(f140,plain,
    ( r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k2_xboole_0(sK0,sK2))
    | ~ spl6_1 ),
    inference(resolution,[],[f52,f32])).

fof(f52,plain,
    ( r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f145,plain,
    ( spl6_6
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f139,f50,f91])).

fof(f139,plain,
    ( r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k2_xboole_0(sK0,sK1))
    | ~ spl6_1 ),
    inference(resolution,[],[f52,f33])).

fof(f83,plain,
    ( ~ spl6_4
    | ~ spl6_5
    | spl6_3 ),
    inference(avatar_split_clause,[],[f70,f58,f80,f76])).

fof(f70,plain,
    ( ~ r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),sK2)
    | ~ r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),sK1)
    | spl6_3 ),
    inference(resolution,[],[f59,f31])).

fof(f59,plain,
    ( ~ r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k3_xboole_0(sK1,sK2))
    | spl6_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f63,plain,
    ( ~ spl6_1
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f48,f58,f50])).

fof(f48,plain,
    ( ~ r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k3_xboole_0(sK1,sK2))
    | ~ r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))) ),
    inference(resolution,[],[f38,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( sQ5_eqProxy(k2_xboole_0(X0,X1),X2)
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f30,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( sQ5_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ5_eqProxy])])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f38,plain,(
    ~ sQ5_eqProxy(k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))) ),
    inference(equality_proxy_replacement,[],[f18,f37])).

fof(f18,plain,(
    k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f6])).

fof(f6,plain,
    ( ? [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) != k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))
   => k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) != k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_xboole_1)).

fof(f62,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f47,f54,f50])).

fof(f47,plain,
    ( ~ r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),sK0)
    | ~ r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))) ),
    inference(resolution,[],[f38,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( sQ5_eqProxy(k2_xboole_0(X0,X1),X2)
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f29,f37])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f61,plain,
    ( spl6_1
    | spl6_2
    | spl6_3 ),
    inference(avatar_split_clause,[],[f46,f58,f54,f50])).

fof(f46,plain,
    ( r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k3_xboole_0(sK1,sK2))
    | r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),sK0)
    | r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))) ),
    inference(resolution,[],[f38,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( sQ5_eqProxy(k2_xboole_0(X0,X1),X2)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f28,f37])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:19:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (2418)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.46  % (2412)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.46  % (2402)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.46  % (2412)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f238,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f61,f62,f63,f83,f145,f146,f152,f186,f190,f191,f204,f205,f206,f207,f237])).
% 0.21/0.46  fof(f237,plain,(
% 0.21/0.46    spl6_2 | spl6_5 | ~spl6_7),
% 0.21/0.46    inference(avatar_split_clause,[],[f232,f95,f80,f54])).
% 0.21/0.46  fof(f54,plain,(
% 0.21/0.46    spl6_2 <=> r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.46  fof(f80,plain,(
% 0.21/0.46    spl6_5 <=> r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),sK2)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.46  fof(f95,plain,(
% 0.21/0.46    spl6_7 <=> r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k2_xboole_0(sK0,sK2))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.46  fof(f232,plain,(
% 0.21/0.46    r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),sK2) | r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),sK0) | ~spl6_7),
% 0.21/0.46    inference(resolution,[],[f96,f36])).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k2_xboole_0(X0,X1))) )),
% 0.21/0.46    inference(equality_resolution,[],[f25])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.21/0.46    inference(cnf_transformation,[],[f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK4(X0,X1,X2),X1) & ~r2_hidden(sK4(X0,X1,X2),X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f15,f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK4(X0,X1,X2),X1) & ~r2_hidden(sK4(X0,X1,X2),X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.46    inference(rectify,[],[f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.46    inference(flattening,[],[f13])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.46    inference(nnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.21/0.46  fof(f96,plain,(
% 0.21/0.46    r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k2_xboole_0(sK0,sK2)) | ~spl6_7),
% 0.21/0.46    inference(avatar_component_clause,[],[f95])).
% 0.21/0.46  fof(f207,plain,(
% 0.21/0.46    ~spl6_5 | spl6_7),
% 0.21/0.46    inference(avatar_split_clause,[],[f181,f95,f80])).
% 0.21/0.46  fof(f181,plain,(
% 0.21/0.46    ~r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),sK2) | spl6_7),
% 0.21/0.46    inference(resolution,[],[f97,f34])).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 0.21/0.46    inference(equality_resolution,[],[f27])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 0.21/0.46    inference(cnf_transformation,[],[f17])).
% 0.21/0.46  fof(f97,plain,(
% 0.21/0.46    ~r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k2_xboole_0(sK0,sK2)) | spl6_7),
% 0.21/0.46    inference(avatar_component_clause,[],[f95])).
% 0.21/0.46  fof(f206,plain,(
% 0.21/0.46    ~spl6_4 | spl6_6),
% 0.21/0.46    inference(avatar_split_clause,[],[f121,f91,f76])).
% 0.21/0.46  fof(f76,plain,(
% 0.21/0.46    spl6_4 <=> r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.46  fof(f91,plain,(
% 0.21/0.46    spl6_6 <=> r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k2_xboole_0(sK0,sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.46  fof(f121,plain,(
% 0.21/0.46    ~r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),sK1) | spl6_6),
% 0.21/0.46    inference(resolution,[],[f93,f34])).
% 0.21/0.46  fof(f93,plain,(
% 0.21/0.46    ~r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k2_xboole_0(sK0,sK1)) | spl6_6),
% 0.21/0.46    inference(avatar_component_clause,[],[f91])).
% 0.21/0.46  fof(f205,plain,(
% 0.21/0.46    spl6_5 | ~spl6_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f199,f58,f80])).
% 0.21/0.46  fof(f58,plain,(
% 0.21/0.46    spl6_3 <=> r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k3_xboole_0(sK1,sK2))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.46  fof(f199,plain,(
% 0.21/0.46    r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),sK2) | ~spl6_3),
% 0.21/0.46    inference(resolution,[],[f60,f32])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 0.21/0.46    inference(equality_resolution,[],[f20])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.21/0.46    inference(cnf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.46    inference(rectify,[],[f9])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.46    inference(flattening,[],[f8])).
% 0.21/0.46  fof(f8,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.46    inference(nnf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.21/0.46  fof(f60,plain,(
% 0.21/0.46    r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k3_xboole_0(sK1,sK2)) | ~spl6_3),
% 0.21/0.46    inference(avatar_component_clause,[],[f58])).
% 0.21/0.46  fof(f204,plain,(
% 0.21/0.46    spl6_4 | ~spl6_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f198,f58,f76])).
% 0.21/0.46  fof(f198,plain,(
% 0.21/0.46    r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),sK1) | ~spl6_3),
% 0.21/0.46    inference(resolution,[],[f60,f33])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 0.21/0.46    inference(equality_resolution,[],[f19])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.21/0.46    inference(cnf_transformation,[],[f12])).
% 0.21/0.46  fof(f191,plain,(
% 0.21/0.46    ~spl6_2 | spl6_6),
% 0.21/0.46    inference(avatar_split_clause,[],[f120,f91,f54])).
% 0.21/0.46  fof(f120,plain,(
% 0.21/0.46    ~r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),sK0) | spl6_6),
% 0.21/0.46    inference(resolution,[],[f93,f35])).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 0.21/0.46    inference(equality_resolution,[],[f26])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 0.21/0.46    inference(cnf_transformation,[],[f17])).
% 0.21/0.46  fof(f190,plain,(
% 0.21/0.46    ~spl6_6 | ~spl6_7 | spl6_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f85,f50,f95,f91])).
% 0.21/0.46  fof(f50,plain,(
% 0.21/0.46    spl6_1 <=> r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.46  fof(f85,plain,(
% 0.21/0.46    ~r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k2_xboole_0(sK0,sK2)) | ~r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k2_xboole_0(sK0,sK1)) | spl6_1),
% 0.21/0.46    inference(resolution,[],[f51,f31])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_xboole_0(X0,X1)) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 0.21/0.46    inference(equality_resolution,[],[f21])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 0.21/0.46    inference(cnf_transformation,[],[f12])).
% 0.21/0.46  fof(f51,plain,(
% 0.21/0.46    ~r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))) | spl6_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f50])).
% 0.21/0.46  fof(f186,plain,(
% 0.21/0.46    ~spl6_2 | spl6_7),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f179])).
% 0.21/0.46  fof(f179,plain,(
% 0.21/0.46    $false | (~spl6_2 | spl6_7)),
% 0.21/0.46    inference(resolution,[],[f97,f65])).
% 0.21/0.46  fof(f65,plain,(
% 0.21/0.46    ( ! [X0] : (r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k2_xboole_0(sK0,X0))) ) | ~spl6_2),
% 0.21/0.46    inference(resolution,[],[f56,f35])).
% 0.21/0.46  fof(f56,plain,(
% 0.21/0.46    r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),sK0) | ~spl6_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f54])).
% 0.21/0.46  fof(f152,plain,(
% 0.21/0.46    spl6_2 | spl6_4 | ~spl6_6),
% 0.21/0.46    inference(avatar_split_clause,[],[f147,f91,f76,f54])).
% 0.21/0.46  fof(f147,plain,(
% 0.21/0.46    r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),sK1) | r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),sK0) | ~spl6_6),
% 0.21/0.46    inference(resolution,[],[f92,f36])).
% 0.21/0.46  fof(f92,plain,(
% 0.21/0.46    r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k2_xboole_0(sK0,sK1)) | ~spl6_6),
% 0.21/0.46    inference(avatar_component_clause,[],[f91])).
% 0.21/0.46  fof(f146,plain,(
% 0.21/0.46    spl6_7 | ~spl6_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f140,f50,f95])).
% 0.21/0.46  fof(f140,plain,(
% 0.21/0.46    r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k2_xboole_0(sK0,sK2)) | ~spl6_1),
% 0.21/0.46    inference(resolution,[],[f52,f32])).
% 0.21/0.46  fof(f52,plain,(
% 0.21/0.46    r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))) | ~spl6_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f50])).
% 0.21/0.46  fof(f145,plain,(
% 0.21/0.46    spl6_6 | ~spl6_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f139,f50,f91])).
% 0.21/0.46  fof(f139,plain,(
% 0.21/0.46    r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k2_xboole_0(sK0,sK1)) | ~spl6_1),
% 0.21/0.46    inference(resolution,[],[f52,f33])).
% 0.21/0.46  fof(f83,plain,(
% 0.21/0.46    ~spl6_4 | ~spl6_5 | spl6_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f70,f58,f80,f76])).
% 0.21/0.46  fof(f70,plain,(
% 0.21/0.46    ~r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),sK2) | ~r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),sK1) | spl6_3),
% 0.21/0.46    inference(resolution,[],[f59,f31])).
% 0.21/0.46  fof(f59,plain,(
% 0.21/0.46    ~r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k3_xboole_0(sK1,sK2)) | spl6_3),
% 0.21/0.46    inference(avatar_component_clause,[],[f58])).
% 0.21/0.46  fof(f63,plain,(
% 0.21/0.46    ~spl6_1 | ~spl6_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f48,f58,f50])).
% 0.21/0.46  fof(f48,plain,(
% 0.21/0.46    ~r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k3_xboole_0(sK1,sK2)) | ~r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)))),
% 0.21/0.46    inference(resolution,[],[f38,f42])).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (sQ5_eqProxy(k2_xboole_0(X0,X1),X2) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 0.21/0.46    inference(equality_proxy_replacement,[],[f30,f37])).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    ! [X1,X0] : (sQ5_eqProxy(X0,X1) <=> X0 = X1)),
% 0.21/0.46    introduced(equality_proxy_definition,[new_symbols(naming,[sQ5_eqProxy])])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f17])).
% 0.21/0.46  fof(f38,plain,(
% 0.21/0.46    ~sQ5_eqProxy(k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)))),
% 0.21/0.46    inference(equality_proxy_replacement,[],[f18,f37])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),
% 0.21/0.46    inference(cnf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,plain,(
% 0.21/0.46    k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f6])).
% 0.21/0.46  fof(f6,plain,(
% 0.21/0.46    ? [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) != k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) => k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f5,plain,(
% 0.21/0.46    ? [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) != k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 0.21/0.46    inference(ennf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 0.21/0.46    inference(negated_conjecture,[],[f3])).
% 0.21/0.46  fof(f3,conjecture,(
% 0.21/0.46    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_xboole_1)).
% 0.21/0.46  fof(f62,plain,(
% 0.21/0.46    ~spl6_1 | ~spl6_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f47,f54,f50])).
% 0.21/0.46  fof(f47,plain,(
% 0.21/0.46    ~r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),sK0) | ~r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)))),
% 0.21/0.46    inference(resolution,[],[f38,f43])).
% 0.21/0.46  fof(f43,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (sQ5_eqProxy(k2_xboole_0(X0,X1),X2) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 0.21/0.46    inference(equality_proxy_replacement,[],[f29,f37])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f17])).
% 0.21/0.46  fof(f61,plain,(
% 0.21/0.46    spl6_1 | spl6_2 | spl6_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f46,f58,f54,f50])).
% 0.21/0.46  fof(f46,plain,(
% 0.21/0.46    r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k3_xboole_0(sK1,sK2)) | r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),sK0) | r2_hidden(sK4(sK0,k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)))),
% 0.21/0.46    inference(resolution,[],[f38,f44])).
% 0.21/0.46  fof(f44,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (sQ5_eqProxy(k2_xboole_0(X0,X1),X2) | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 0.21/0.46    inference(equality_proxy_replacement,[],[f28,f37])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f17])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (2412)------------------------------
% 0.21/0.46  % (2412)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (2412)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (2412)Memory used [KB]: 6140
% 0.21/0.46  % (2412)Time elapsed: 0.061 s
% 0.21/0.46  % (2412)------------------------------
% 0.21/0.46  % (2412)------------------------------
% 0.21/0.46  % (2399)Success in time 0.113 s
%------------------------------------------------------------------------------
