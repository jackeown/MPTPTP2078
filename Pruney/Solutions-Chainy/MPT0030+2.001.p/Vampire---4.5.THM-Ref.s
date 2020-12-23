%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 227 expanded)
%              Number of leaves         :   14 (  83 expanded)
%              Depth                    :   10
%              Number of atoms          :  301 (1373 expanded)
%              Number of equality atoms :   35 ( 177 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f185,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f62,f63,f83,f117,f131,f144,f163,f178,f179,f180,f183,f184])).

fof(f184,plain,
    ( spl6_2
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f171,f160,f54])).

fof(f54,plain,
    ( spl6_2
  <=> r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f160,plain,
    ( spl6_8
  <=> r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k3_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f171,plain,
    ( r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK0)
    | ~ spl6_8 ),
    inference(resolution,[],[f162,f36])).

fof(f36,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f15,f16])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
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
    inference(rectify,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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

fof(f162,plain,
    ( r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k3_xboole_0(sK0,sK2))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f160])).

fof(f183,plain,
    ( spl6_5
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f172,f160,f80])).

fof(f80,plain,
    ( spl6_5
  <=> r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f172,plain,
    ( r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK2)
    | ~ spl6_8 ),
    inference(resolution,[],[f162,f35])).

fof(f35,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f180,plain,
    ( spl6_2
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f164,f156,f54])).

fof(f156,plain,
    ( spl6_7
  <=> r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f164,plain,
    ( r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK0)
    | ~ spl6_7 ),
    inference(resolution,[],[f158,f36])).

fof(f158,plain,
    ( r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k3_xboole_0(sK0,sK1))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f156])).

fof(f179,plain,
    ( spl6_4
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f165,f156,f76])).

fof(f76,plain,
    ( spl6_4
  <=> r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f165,plain,
    ( r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK1)
    | ~ spl6_7 ),
    inference(resolution,[],[f158,f35])).

fof(f178,plain,
    ( ~ spl6_4
    | spl6_3 ),
    inference(avatar_split_clause,[],[f138,f59,f76])).

fof(f59,plain,
    ( spl6_3
  <=> r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f138,plain,
    ( ~ r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK1)
    | spl6_3 ),
    inference(resolution,[],[f60,f32])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f60,plain,
    ( ~ r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(sK1,sK2))
    | spl6_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f163,plain,
    ( spl6_7
    | spl6_8
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f150,f50,f160,f156])).

fof(f50,plain,
    ( spl6_1
  <=> r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f150,plain,
    ( r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k3_xboole_0(sK0,sK2))
    | r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k3_xboole_0(sK0,sK1))
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
    ( r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f144,plain,
    ( ~ spl6_5
    | spl6_3 ),
    inference(avatar_split_clause,[],[f139,f59,f80])).

fof(f139,plain,
    ( ~ r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK2)
    | spl6_3 ),
    inference(resolution,[],[f60,f31])).

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

fof(f131,plain,
    ( ~ spl6_2
    | ~ spl6_5
    | spl6_1 ),
    inference(avatar_split_clause,[],[f126,f50,f80,f54])).

fof(f126,plain,
    ( ~ r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK2)
    | ~ r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK0)
    | spl6_1 ),
    inference(resolution,[],[f87,f34])).

fof(f34,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f87,plain,
    ( ~ r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k3_xboole_0(sK0,sK2))
    | spl6_1 ),
    inference(resolution,[],[f51,f31])).

fof(f51,plain,
    ( ~ r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f117,plain,
    ( ~ spl6_2
    | ~ spl6_4
    | spl6_1 ),
    inference(avatar_split_clause,[],[f112,f50,f76,f54])).

fof(f112,plain,
    ( ~ r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK1)
    | ~ r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK0)
    | spl6_1 ),
    inference(resolution,[],[f86,f34])).

fof(f86,plain,
    ( ~ r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k3_xboole_0(sK0,sK1))
    | spl6_1 ),
    inference(resolution,[],[f51,f32])).

fof(f83,plain,
    ( spl6_4
    | spl6_5
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f70,f59,f80,f76])).

fof(f70,plain,
    ( r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK2)
    | r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK1)
    | ~ spl6_3 ),
    inference(resolution,[],[f61,f33])).

fof(f61,plain,
    ( r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(sK1,sK2))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f63,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f48,f59,f54,f50])).

fof(f48,plain,
    ( ~ r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(sK1,sK2))
    | ~ r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK0)
    | ~ r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))) ),
    inference(resolution,[],[f38,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( sQ5_eqProxy(k3_xboole_0(X0,X1),X2)
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
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
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f38,plain,(
    ~ sQ5_eqProxy(k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))) ),
    inference(equality_proxy_replacement,[],[f18,f37])).

fof(f18,plain,(
    k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f6])).

fof(f6,plain,
    ( ? [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) != k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))
   => k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) != k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f62,plain,
    ( spl6_1
    | spl6_3 ),
    inference(avatar_split_clause,[],[f47,f59,f50])).

fof(f47,plain,
    ( r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(sK1,sK2))
    | r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))) ),
    inference(resolution,[],[f38,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( sQ5_eqProxy(k3_xboole_0(X0,X1),X2)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f29,f37])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f57,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f46,f54,f50])).

fof(f46,plain,
    ( r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK0)
    | r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))) ),
    inference(resolution,[],[f38,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( sQ5_eqProxy(k3_xboole_0(X0,X1),X2)
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f28,f37])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:20:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.44  % (32240)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.45  % (32256)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.47  % (32251)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.47  % (32244)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (32251)Refutation not found, incomplete strategy% (32251)------------------------------
% 0.21/0.47  % (32251)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (32251)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (32251)Memory used [KB]: 1535
% 0.21/0.47  % (32251)Time elapsed: 0.051 s
% 0.21/0.47  % (32251)------------------------------
% 0.21/0.47  % (32251)------------------------------
% 0.21/0.47  % (32243)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (32252)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (32252)Refutation not found, incomplete strategy% (32252)------------------------------
% 0.21/0.49  % (32252)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (32250)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (32252)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (32252)Memory used [KB]: 10618
% 0.21/0.49  % (32252)Time elapsed: 0.070 s
% 0.21/0.49  % (32252)------------------------------
% 0.21/0.49  % (32252)------------------------------
% 0.21/0.50  % (32238)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (32239)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (32238)Refutation not found, incomplete strategy% (32238)------------------------------
% 0.21/0.50  % (32238)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (32238)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (32238)Memory used [KB]: 6140
% 0.21/0.50  % (32238)Time elapsed: 0.084 s
% 0.21/0.50  % (32238)------------------------------
% 0.21/0.50  % (32238)------------------------------
% 0.21/0.50  % (32239)Refutation not found, incomplete strategy% (32239)------------------------------
% 0.21/0.50  % (32239)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (32239)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (32239)Memory used [KB]: 10490
% 0.21/0.50  % (32239)Time elapsed: 0.083 s
% 0.21/0.50  % (32239)------------------------------
% 0.21/0.50  % (32239)------------------------------
% 0.21/0.50  % (32253)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.50  % (32253)Refutation not found, incomplete strategy% (32253)------------------------------
% 0.21/0.50  % (32253)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (32253)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (32253)Memory used [KB]: 6012
% 0.21/0.50  % (32253)Time elapsed: 0.051 s
% 0.21/0.50  % (32253)------------------------------
% 0.21/0.50  % (32253)------------------------------
% 0.21/0.50  % (32248)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.50  % (32246)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.50  % (32254)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.51  % (32242)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.51  % (32255)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.51  % (32241)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (32241)Refutation not found, incomplete strategy% (32241)------------------------------
% 0.21/0.51  % (32241)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (32241)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (32241)Memory used [KB]: 10490
% 0.21/0.51  % (32241)Time elapsed: 0.092 s
% 0.21/0.51  % (32241)------------------------------
% 0.21/0.51  % (32241)------------------------------
% 0.21/0.51  % (32249)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.51  % (32250)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f185,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f57,f62,f63,f83,f117,f131,f144,f163,f178,f179,f180,f183,f184])).
% 0.21/0.51  fof(f184,plain,(
% 0.21/0.51    spl6_2 | ~spl6_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f171,f160,f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    spl6_2 <=> r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.51  fof(f160,plain,(
% 0.21/0.51    spl6_8 <=> r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k3_xboole_0(sK0,sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.21/0.51  fof(f171,plain,(
% 0.21/0.51    r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK0) | ~spl6_8),
% 0.21/0.51    inference(resolution,[],[f162,f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 0.21/0.51    inference(equality_resolution,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f15,f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.51    inference(rectify,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.51    inference(flattening,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.51    inference(nnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.21/0.51  fof(f162,plain,(
% 0.21/0.51    r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k3_xboole_0(sK0,sK2)) | ~spl6_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f160])).
% 0.21/0.51  fof(f183,plain,(
% 0.21/0.51    spl6_5 | ~spl6_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f172,f160,f80])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    spl6_5 <=> r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.51  fof(f172,plain,(
% 0.21/0.51    r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK2) | ~spl6_8),
% 0.21/0.51    inference(resolution,[],[f162,f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 0.21/0.51    inference(equality_resolution,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f180,plain,(
% 0.21/0.51    spl6_2 | ~spl6_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f164,f156,f54])).
% 0.21/0.51  fof(f156,plain,(
% 0.21/0.51    spl6_7 <=> r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k3_xboole_0(sK0,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.51  fof(f164,plain,(
% 0.21/0.51    r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK0) | ~spl6_7),
% 0.21/0.51    inference(resolution,[],[f158,f36])).
% 0.21/0.51  fof(f158,plain,(
% 0.21/0.51    r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k3_xboole_0(sK0,sK1)) | ~spl6_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f156])).
% 0.21/0.51  fof(f179,plain,(
% 0.21/0.51    spl6_4 | ~spl6_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f165,f156,f76])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    spl6_4 <=> r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.51  fof(f165,plain,(
% 0.21/0.51    r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK1) | ~spl6_7),
% 0.21/0.51    inference(resolution,[],[f158,f35])).
% 0.21/0.51  fof(f178,plain,(
% 0.21/0.51    ~spl6_4 | spl6_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f138,f59,f76])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    spl6_3 <=> r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(sK1,sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.51  fof(f138,plain,(
% 0.21/0.51    ~r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK1) | spl6_3),
% 0.21/0.51    inference(resolution,[],[f60,f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 0.21/0.51    inference(equality_resolution,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK3(X0,X1,X2),X1) & ~r2_hidden(sK3(X0,X1,X2),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK3(X0,X1,X2),X1) & ~r2_hidden(sK3(X0,X1,X2),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.51    inference(rectify,[],[f9])).
% 0.21/0.51  fof(f9,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.51    inference(flattening,[],[f8])).
% 0.21/0.51  fof(f8,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.51    inference(nnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    ~r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(sK1,sK2)) | spl6_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f59])).
% 0.21/0.51  fof(f163,plain,(
% 0.21/0.51    spl6_7 | spl6_8 | ~spl6_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f150,f50,f160,f156])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    spl6_1 <=> r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.51  fof(f150,plain,(
% 0.21/0.51    r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k3_xboole_0(sK0,sK2)) | r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k3_xboole_0(sK0,sK1)) | ~spl6_1),
% 0.21/0.51    inference(resolution,[],[f52,f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k2_xboole_0(X0,X1))) )),
% 0.21/0.51    inference(equality_resolution,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))) | ~spl6_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f50])).
% 0.21/0.51  fof(f144,plain,(
% 0.21/0.51    ~spl6_5 | spl6_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f139,f59,f80])).
% 0.21/0.51  fof(f139,plain,(
% 0.21/0.51    ~r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK2) | spl6_3),
% 0.21/0.51    inference(resolution,[],[f60,f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 0.21/0.51    inference(equality_resolution,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f131,plain,(
% 0.21/0.51    ~spl6_2 | ~spl6_5 | spl6_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f126,f50,f80,f54])).
% 0.21/0.51  fof(f126,plain,(
% 0.21/0.51    ~r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK2) | ~r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK0) | spl6_1),
% 0.21/0.51    inference(resolution,[],[f87,f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_xboole_0(X0,X1)) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 0.21/0.51    inference(equality_resolution,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    ~r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k3_xboole_0(sK0,sK2)) | spl6_1),
% 0.21/0.51    inference(resolution,[],[f51,f31])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ~r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))) | spl6_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f50])).
% 0.21/0.51  fof(f117,plain,(
% 0.21/0.51    ~spl6_2 | ~spl6_4 | spl6_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f112,f50,f76,f54])).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    ~r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK1) | ~r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK0) | spl6_1),
% 0.21/0.51    inference(resolution,[],[f86,f34])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    ~r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k3_xboole_0(sK0,sK1)) | spl6_1),
% 0.21/0.51    inference(resolution,[],[f51,f32])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    spl6_4 | spl6_5 | ~spl6_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f70,f59,f80,f76])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK2) | r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK1) | ~spl6_3),
% 0.21/0.51    inference(resolution,[],[f61,f33])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(sK1,sK2)) | ~spl6_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f59])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    ~spl6_1 | ~spl6_2 | ~spl6_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f48,f59,f54,f50])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ~r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(sK1,sK2)) | ~r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK0) | ~r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)))),
% 0.21/0.51    inference(resolution,[],[f38,f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (sQ5_eqProxy(k3_xboole_0(X0,X1),X2) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 0.21/0.51    inference(equality_proxy_replacement,[],[f30,f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ! [X1,X0] : (sQ5_eqProxy(X0,X1) <=> X0 = X1)),
% 0.21/0.51    introduced(equality_proxy_definition,[new_symbols(naming,[sQ5_eqProxy])])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ~sQ5_eqProxy(k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)))),
% 0.21/0.51    inference(equality_proxy_replacement,[],[f18,f37])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,plain,(
% 0.21/0.51    k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f6])).
% 0.21/0.51  fof(f6,plain,(
% 0.21/0.51    ? [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) != k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) => k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f5,plain,(
% 0.21/0.51    ? [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) != k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.21/0.51    inference(negated_conjecture,[],[f3])).
% 0.21/0.51  fof(f3,conjecture,(
% 0.21/0.51    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    spl6_1 | spl6_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f47,f59,f50])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(sK1,sK2)) | r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)))),
% 0.21/0.51    inference(resolution,[],[f38,f43])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (sQ5_eqProxy(k3_xboole_0(X0,X1),X2) | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 0.21/0.51    inference(equality_proxy_replacement,[],[f29,f37])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    spl6_1 | spl6_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f46,f54,f50])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK0) | r2_hidden(sK4(sK0,k2_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)))),
% 0.21/0.51    inference(resolution,[],[f38,f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (sQ5_eqProxy(k3_xboole_0(X0,X1),X2) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 0.21/0.51    inference(equality_proxy_replacement,[],[f28,f37])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (32250)------------------------------
% 0.21/0.51  % (32250)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (32250)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (32250)Memory used [KB]: 6140
% 0.21/0.51  % (32250)Time elapsed: 0.076 s
% 0.21/0.51  % (32250)------------------------------
% 0.21/0.51  % (32250)------------------------------
% 0.21/0.51  % (32249)Refutation not found, incomplete strategy% (32249)------------------------------
% 0.21/0.51  % (32249)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (32249)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (32249)Memory used [KB]: 10618
% 0.21/0.51  % (32249)Time elapsed: 0.091 s
% 0.21/0.51  % (32249)------------------------------
% 0.21/0.51  % (32249)------------------------------
% 0.21/0.51  % (32237)Success in time 0.155 s
%------------------------------------------------------------------------------
