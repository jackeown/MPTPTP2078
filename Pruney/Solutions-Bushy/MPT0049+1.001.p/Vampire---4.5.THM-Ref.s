%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0049+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:15 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 237 expanded)
%              Number of leaves         :   14 (  89 expanded)
%              Depth                    :    9
%              Number of atoms          :  309 (1393 expanded)
%              Number of equality atoms :   35 ( 177 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f202,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f62,f63,f83,f110,f149,f162,f163,f165,f166,f167,f168,f197,f198,f200])).

fof(f200,plain,
    ( spl6_5
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f191,f107,f80])).

fof(f80,plain,
    ( spl6_5
  <=> r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f107,plain,
    ( spl6_8
  <=> r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f191,plain,
    ( r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),sK1)
    | ~ spl6_8 ),
    inference(resolution,[],[f109,f36])).

fof(f36,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f15,f16])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
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
    inference(rectify,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f109,plain,
    ( r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),k4_xboole_0(sK1,sK2))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f107])).

fof(f198,plain,
    ( ~ spl6_4
    | spl6_3
    | spl6_7 ),
    inference(avatar_split_clause,[],[f186,f103,f59,f76])).

fof(f76,plain,
    ( spl6_4
  <=> r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f59,plain,
    ( spl6_3
  <=> r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f103,plain,
    ( spl6_7
  <=> r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f186,plain,
    ( r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),sK2)
    | ~ r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),sK0)
    | spl6_7 ),
    inference(resolution,[],[f104,f34])).

fof(f34,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f104,plain,
    ( ~ r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK2))
    | spl6_7 ),
    inference(avatar_component_clause,[],[f103])).

fof(f197,plain,
    ( ~ spl6_3
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f192,f107,f59])).

fof(f192,plain,
    ( ~ r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),sK2)
    | ~ spl6_8 ),
    inference(resolution,[],[f109,f35])).

fof(f35,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f168,plain,
    ( ~ spl6_4
    | spl6_2 ),
    inference(avatar_split_clause,[],[f90,f54,f76])).

fof(f54,plain,
    ( spl6_2
  <=> r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f90,plain,
    ( ~ r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),sK0)
    | spl6_2 ),
    inference(resolution,[],[f55,f32])).

fof(f32,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & ~ r2_hidden(sK3(X0,X1,X2),X0) )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( r2_hidden(sK3(X0,X1,X2),X1)
            | r2_hidden(sK3(X0,X1,X2),X0)
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f11])).

fof(f11,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & ~ r2_hidden(sK3(X0,X1,X2),X0) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( r2_hidden(sK3(X0,X1,X2),X1)
          | r2_hidden(sK3(X0,X1,X2),X0)
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
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
    inference(rectify,[],[f9])).

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

fof(f8,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f55,plain,
    ( ~ r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),k2_xboole_0(sK0,sK1))
    | spl6_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f167,plain,
    ( ~ spl6_5
    | spl6_2 ),
    inference(avatar_split_clause,[],[f91,f54,f80])).

fof(f91,plain,
    ( ~ r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),sK1)
    | spl6_2 ),
    inference(resolution,[],[f55,f31])).

fof(f31,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f166,plain,
    ( ~ spl6_7
    | spl6_1 ),
    inference(avatar_split_clause,[],[f124,f50,f103])).

fof(f50,plain,
    ( spl6_1
  <=> r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f124,plain,
    ( ~ r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK2))
    | spl6_1 ),
    inference(resolution,[],[f51,f32])).

fof(f51,plain,
    ( ~ r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f165,plain,
    ( ~ spl6_8
    | spl6_1 ),
    inference(avatar_split_clause,[],[f125,f50,f107])).

fof(f125,plain,
    ( ~ r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),k4_xboole_0(sK1,sK2))
    | spl6_1 ),
    inference(resolution,[],[f51,f31])).

fof(f163,plain,
    ( ~ spl6_3
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f157,f103,f59])).

fof(f157,plain,
    ( ~ r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),sK2)
    | ~ spl6_7 ),
    inference(resolution,[],[f105,f35])).

fof(f105,plain,
    ( r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK2))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f103])).

fof(f162,plain,
    ( spl6_4
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f156,f103,f76])).

fof(f156,plain,
    ( r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),sK0)
    | ~ spl6_7 ),
    inference(resolution,[],[f105,f36])).

fof(f149,plain,
    ( ~ spl6_5
    | spl6_3
    | spl6_8 ),
    inference(avatar_split_clause,[],[f144,f107,f59,f80])).

fof(f144,plain,
    ( r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),sK2)
    | ~ r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),sK1)
    | spl6_8 ),
    inference(resolution,[],[f108,f34])).

fof(f108,plain,
    ( ~ r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),k4_xboole_0(sK1,sK2))
    | spl6_8 ),
    inference(avatar_component_clause,[],[f107])).

fof(f110,plain,
    ( spl6_7
    | spl6_8
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f97,f50,f107,f103])).

fof(f97,plain,
    ( r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),k4_xboole_0(sK1,sK2))
    | r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),k4_xboole_0(sK0,sK2))
    | ~ spl6_1 ),
    inference(resolution,[],[f52,f33])).

fof(f33,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f52,plain,
    ( r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f83,plain,
    ( spl6_4
    | spl6_5
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f70,f54,f80,f76])).

fof(f70,plain,
    ( r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),sK1)
    | r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),sK0)
    | ~ spl6_2 ),
    inference(resolution,[],[f56,f33])).

fof(f56,plain,
    ( r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),k2_xboole_0(sK0,sK1))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f63,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | spl6_3 ),
    inference(avatar_split_clause,[],[f48,f59,f54,f50])).

fof(f48,plain,
    ( r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),sK2)
    | ~ r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),k2_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f38,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( sQ5_eqProxy(k4_xboole_0(X0,X1),X2)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f30,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( sQ5_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ5_eqProxy])])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f38,plain,(
    ~ sQ5_eqProxy(k4_xboole_0(k2_xboole_0(sK0,sK1),sK2),k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))) ),
    inference(equality_proxy_replacement,[],[f18,f37])).

fof(f18,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f6])).

fof(f6,plain,
    ( ? [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) != k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))
   => k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) != k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).

fof(f62,plain,
    ( spl6_1
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f47,f59,f50])).

fof(f47,plain,
    ( ~ r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),sK2)
    | r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f38,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( sQ5_eqProxy(k4_xboole_0(X0,X1),X2)
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f29,f37])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f57,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f46,f54,f50])).

fof(f46,plain,
    ( r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),k2_xboole_0(sK0,sK1))
    | r2_hidden(sK4(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f38,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( sQ5_eqProxy(k4_xboole_0(X0,X1),X2)
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f28,f37])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

%------------------------------------------------------------------------------
