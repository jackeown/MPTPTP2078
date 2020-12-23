%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:41 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 461 expanded)
%              Number of leaves         :   20 ( 173 expanded)
%              Depth                    :   10
%              Number of atoms          :  424 (2853 expanded)
%              Number of equality atoms :   35 ( 330 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f706,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f138,f159,f316,f321,f322,f346,f349,f350,f477,f478,f479,f490,f491,f492,f494,f499,f503,f509,f510,f511,f512,f516,f573,f581,f582,f583,f701,f704,f705])).

fof(f705,plain,
    ( spl6_12
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f568,f152,f204])).

fof(f204,plain,
    ( spl6_12
  <=> r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f152,plain,
    ( spl6_9
  <=> r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f568,plain,
    ( r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k2_xboole_0(sK1,sK2))
    | ~ spl6_9 ),
    inference(resolution,[],[f153,f32])).

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

fof(f153,plain,
    ( r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f152])).

fof(f704,plain,
    ( ~ spl6_6
    | spl6_2 ),
    inference(avatar_split_clause,[],[f524,f54,f86])).

fof(f86,plain,
    ( spl6_6
  <=> r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f54,plain,
    ( spl6_2
  <=> r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f524,plain,
    ( ~ r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(sK0,sK1))
    | spl6_2 ),
    inference(resolution,[],[f55,f35])).

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

fof(f55,plain,
    ( ~ r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)))
    | spl6_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f701,plain,
    ( spl6_13
    | spl6_4
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f696,f204,f71,f318])).

fof(f318,plain,
    ( spl6_13
  <=> r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f71,plain,
    ( spl6_4
  <=> r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f696,plain,
    ( r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK2)
    | r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK1)
    | ~ spl6_12 ),
    inference(resolution,[],[f205,f36])).

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

fof(f205,plain,
    ( r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k2_xboole_0(sK1,sK2))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f204])).

fof(f583,plain,
    ( spl6_5
    | spl6_13
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f464,f200,f318,f75])).

fof(f75,plain,
    ( spl6_5
  <=> r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f200,plain,
    ( spl6_11
  <=> r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f464,plain,
    ( r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK1)
    | r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK0)
    | ~ spl6_11 ),
    inference(resolution,[],[f201,f36])).

fof(f201,plain,
    ( r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k2_xboole_0(sK0,sK1))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f200])).

fof(f582,plain,
    ( ~ spl6_4
    | ~ spl6_5
    | spl6_3 ),
    inference(avatar_split_clause,[],[f518,f58,f75,f71])).

fof(f58,plain,
    ( spl6_3
  <=> r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f518,plain,
    ( ~ r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK0)
    | ~ r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK2)
    | spl6_3 ),
    inference(resolution,[],[f59,f31])).

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

fof(f59,plain,
    ( ~ r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(sK2,sK0))
    | spl6_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f581,plain,
    ( spl6_4
    | spl6_5
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f132,f50,f75,f71])).

fof(f50,plain,
    ( spl6_1
  <=> r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f132,plain,
    ( r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK0)
    | r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK2)
    | ~ spl6_1 ),
    inference(resolution,[],[f109,f36])).

fof(f109,plain,
    ( r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k2_xboole_0(sK2,sK0))
    | ~ spl6_1 ),
    inference(resolution,[],[f52,f32])).

fof(f52,plain,
    ( r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0)))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f573,plain,
    ( spl6_11
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f567,f152,f200])).

fof(f567,plain,
    ( r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k2_xboole_0(sK0,sK1))
    | ~ spl6_9 ),
    inference(resolution,[],[f153,f33])).

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

fof(f516,plain,
    ( spl6_1
    | spl6_3
    | spl6_8
    | spl6_2 ),
    inference(avatar_split_clause,[],[f99,f54,f95,f58,f50])).

fof(f95,plain,
    ( spl6_8
  <=> sQ5_eqProxy(k2_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0)),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f99,plain,
    ( sQ5_eqProxy(k2_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0)),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0)))
    | r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(sK2,sK0))
    | r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0)))
    | spl6_2 ),
    inference(resolution,[],[f55,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( sQ5_eqProxy(k2_xboole_0(X0,X1),X2)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f28,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( sQ5_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ5_eqProxy])])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f512,plain,
    ( spl6_13
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f333,f90,f318])).

fof(f90,plain,
    ( spl6_7
  <=> r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f333,plain,
    ( r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK1)
    | ~ spl6_7 ),
    inference(resolution,[],[f92,f33])).

fof(f92,plain,
    ( r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(sK1,sK2))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f90])).

fof(f511,plain,
    ( spl6_4
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f334,f90,f71])).

fof(f334,plain,
    ( r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK2)
    | ~ spl6_7 ),
    inference(resolution,[],[f92,f32])).

fof(f510,plain,
    ( ~ spl6_5
    | spl6_11 ),
    inference(avatar_split_clause,[],[f308,f200,f75])).

fof(f308,plain,
    ( ~ r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK0)
    | spl6_11 ),
    inference(resolution,[],[f202,f35])).

fof(f202,plain,
    ( ~ r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k2_xboole_0(sK0,sK1))
    | spl6_11 ),
    inference(avatar_component_clause,[],[f200])).

fof(f509,plain,
    ( ~ spl6_11
    | ~ spl6_12
    | spl6_9 ),
    inference(avatar_split_clause,[],[f194,f152,f204,f200])).

fof(f194,plain,
    ( ~ r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k2_xboole_0(sK1,sK2))
    | ~ r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k2_xboole_0(sK0,sK1))
    | spl6_9 ),
    inference(resolution,[],[f154,f31])).

fof(f154,plain,
    ( ~ r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)))
    | spl6_9 ),
    inference(avatar_component_clause,[],[f152])).

fof(f503,plain,
    ( spl6_9
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f108,f50,f152])).

fof(f108,plain,
    ( r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)))
    | ~ spl6_1 ),
    inference(resolution,[],[f52,f33])).

fof(f499,plain,
    ( spl6_1
    | spl6_2
    | spl6_8
    | spl6_4 ),
    inference(avatar_split_clause,[],[f220,f71,f95,f54,f50])).

fof(f220,plain,
    ( sQ5_eqProxy(k2_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0)),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0)))
    | r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)))
    | r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0)))
    | spl6_4 ),
    inference(resolution,[],[f116,f44])).

fof(f116,plain,
    ( ! [X2] : ~ r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(sK2,X2))
    | spl6_4 ),
    inference(resolution,[],[f73,f33])).

fof(f73,plain,
    ( ~ r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK2)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f71])).

fof(f494,plain,
    ( spl6_5
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f160,f86,f75])).

fof(f160,plain,
    ( r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK0)
    | ~ spl6_6 ),
    inference(resolution,[],[f88,f33])).

fof(f88,plain,
    ( r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(sK0,sK1))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f86])).

fof(f492,plain,
    ( ~ spl6_13
    | spl6_12 ),
    inference(avatar_split_clause,[],[f469,f204,f318])).

fof(f469,plain,
    ( ~ r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK1)
    | spl6_12 ),
    inference(resolution,[],[f206,f35])).

fof(f206,plain,
    ( ~ r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k2_xboole_0(sK1,sK2))
    | spl6_12 ),
    inference(avatar_component_clause,[],[f204])).

fof(f491,plain,
    ( ~ spl6_4
    | spl6_12 ),
    inference(avatar_split_clause,[],[f470,f204,f71])).

fof(f470,plain,
    ( ~ r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK2)
    | spl6_12 ),
    inference(resolution,[],[f206,f34])).

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

fof(f490,plain,
    ( ~ spl6_13
    | ~ spl6_4
    | spl6_7 ),
    inference(avatar_split_clause,[],[f127,f90,f71,f318])).

fof(f127,plain,
    ( ~ r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK2)
    | ~ r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK1)
    | spl6_7 ),
    inference(resolution,[],[f91,f31])).

fof(f91,plain,
    ( ~ r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(sK1,sK2))
    | spl6_7 ),
    inference(avatar_component_clause,[],[f90])).

fof(f479,plain,
    ( ~ spl6_4
    | spl6_10 ),
    inference(avatar_split_clause,[],[f171,f156,f71])).

fof(f156,plain,
    ( spl6_10
  <=> r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k2_xboole_0(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f171,plain,
    ( ~ r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK2)
    | spl6_10 ),
    inference(resolution,[],[f158,f35])).

fof(f158,plain,
    ( ~ r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k2_xboole_0(sK2,sK0))
    | spl6_10 ),
    inference(avatar_component_clause,[],[f156])).

fof(f478,plain,
    ( ~ spl6_5
    | spl6_10 ),
    inference(avatar_split_clause,[],[f172,f156,f75])).

fof(f172,plain,
    ( ~ r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK0)
    | spl6_10 ),
    inference(resolution,[],[f158,f34])).

fof(f477,plain,
    ( spl6_5
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f353,f58,f75])).

fof(f353,plain,
    ( r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK0)
    | ~ spl6_3 ),
    inference(resolution,[],[f60,f32])).

fof(f60,plain,
    ( r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(sK2,sK0))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f350,plain,
    ( ~ spl6_7
    | spl6_2 ),
    inference(avatar_split_clause,[],[f101,f54,f90])).

fof(f101,plain,
    ( ~ r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(sK1,sK2))
    | spl6_2 ),
    inference(resolution,[],[f55,f34])).

fof(f349,plain,(
    ~ spl6_8 ),
    inference(avatar_contradiction_clause,[],[f348])).

fof(f348,plain,
    ( $false
    | ~ spl6_8 ),
    inference(resolution,[],[f97,f38])).

fof(f38,plain,(
    ~ sQ5_eqProxy(k2_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0)),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))) ),
    inference(equality_proxy_replacement,[],[f18,f37])).

fof(f18,plain,(
    k2_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0)) != k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    k2_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0)) != k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f6])).

fof(f6,plain,
    ( ? [X0,X1,X2] : k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) != k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0))
   => k2_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0)) != k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0)) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1,X2] : k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) != k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0)) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) = k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0)) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) = k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_xboole_1)).

fof(f97,plain,
    ( sQ5_eqProxy(k2_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0)),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0)))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f95])).

fof(f346,plain,
    ( spl6_13
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f161,f86,f318])).

fof(f161,plain,
    ( r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK1)
    | ~ spl6_6 ),
    inference(resolution,[],[f88,f32])).

fof(f322,plain,
    ( ~ spl6_13
    | spl6_11 ),
    inference(avatar_split_clause,[],[f309,f200,f318])).

fof(f309,plain,
    ( ~ r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK1)
    | spl6_11 ),
    inference(resolution,[],[f202,f34])).

fof(f321,plain,
    ( ~ spl6_5
    | ~ spl6_13
    | spl6_6 ),
    inference(avatar_split_clause,[],[f122,f86,f318,f75])).

fof(f122,plain,
    ( ~ r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK1)
    | ~ r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK0)
    | spl6_6 ),
    inference(resolution,[],[f87,f31])).

fof(f87,plain,
    ( ~ r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(sK0,sK1))
    | spl6_6 ),
    inference(avatar_component_clause,[],[f86])).

fof(f316,plain,
    ( spl6_6
    | spl6_7
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f80,f54,f90,f86])).

fof(f80,plain,
    ( r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(sK1,sK2))
    | r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(sK0,sK1))
    | ~ spl6_2 ),
    inference(resolution,[],[f56,f36])).

fof(f56,plain,
    ( r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f159,plain,
    ( ~ spl6_9
    | ~ spl6_10
    | spl6_1 ),
    inference(avatar_split_clause,[],[f146,f50,f156,f152])).

fof(f146,plain,
    ( ~ r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k2_xboole_0(sK2,sK0))
    | ~ r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)))
    | spl6_1 ),
    inference(resolution,[],[f51,f31])).

fof(f51,plain,
    ( ~ r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0)))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f138,plain,
    ( ~ spl6_1
    | spl6_8
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f79,f54,f95,f50])).

fof(f79,plain,
    ( sQ5_eqProxy(k2_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0)),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0)))
    | ~ r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0)))
    | ~ spl6_2 ),
    inference(resolution,[],[f56,f43])).

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

fof(f63,plain,
    ( ~ spl6_1
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f48,f58,f50])).

fof(f48,plain,
    ( ~ r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(sK2,sK0))
    | ~ r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))) ),
    inference(resolution,[],[f38,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( sQ5_eqProxy(k2_xboole_0(X0,X1),X2)
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f30,f37])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:24:54 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (4390)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.47  % (4380)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.47  % (4388)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.47  % (4388)Refutation not found, incomplete strategy% (4388)------------------------------
% 0.22/0.47  % (4388)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (4388)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (4388)Memory used [KB]: 1535
% 0.22/0.47  % (4388)Time elapsed: 0.004 s
% 0.22/0.47  % (4388)------------------------------
% 0.22/0.47  % (4388)------------------------------
% 0.22/0.48  % (4382)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.48  % (4377)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.48  % (4390)Refutation not found, incomplete strategy% (4390)------------------------------
% 0.22/0.48  % (4390)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (4390)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (4390)Memory used [KB]: 6140
% 0.22/0.48  % (4390)Time elapsed: 0.068 s
% 0.22/0.48  % (4390)------------------------------
% 0.22/0.48  % (4390)------------------------------
% 0.22/0.48  % (4378)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.49  % (4393)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.49  % (4386)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.49  % (4383)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.49  % (4386)Refutation not found, incomplete strategy% (4386)------------------------------
% 0.22/0.49  % (4386)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (4386)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (4386)Memory used [KB]: 10618
% 0.22/0.49  % (4386)Time elapsed: 0.083 s
% 0.22/0.49  % (4386)------------------------------
% 0.22/0.49  % (4386)------------------------------
% 0.22/0.50  % (4392)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.50  % (4394)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.50  % (4379)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.50  % (4375)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.50  % (4375)Refutation not found, incomplete strategy% (4375)------------------------------
% 0.22/0.50  % (4375)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (4375)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (4375)Memory used [KB]: 6140
% 0.22/0.50  % (4375)Time elapsed: 0.085 s
% 0.22/0.50  % (4375)------------------------------
% 0.22/0.50  % (4375)------------------------------
% 0.22/0.50  % (4387)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (4385)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.50  % (4378)Refutation not found, incomplete strategy% (4378)------------------------------
% 0.22/0.50  % (4378)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (4378)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (4378)Memory used [KB]: 10490
% 0.22/0.50  % (4378)Time elapsed: 0.086 s
% 0.22/0.50  % (4378)------------------------------
% 0.22/0.50  % (4378)------------------------------
% 0.22/0.50  % (4389)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.50  % (4376)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (4376)Refutation not found, incomplete strategy% (4376)------------------------------
% 0.22/0.51  % (4376)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (4376)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (4376)Memory used [KB]: 10490
% 0.22/0.51  % (4376)Time elapsed: 0.078 s
% 0.22/0.51  % (4376)------------------------------
% 0.22/0.51  % (4376)------------------------------
% 0.22/0.51  % (4389)Refutation not found, incomplete strategy% (4389)------------------------------
% 0.22/0.51  % (4389)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (4389)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (4389)Memory used [KB]: 10618
% 0.22/0.51  % (4389)Time elapsed: 0.098 s
% 0.22/0.51  % (4389)------------------------------
% 0.22/0.51  % (4389)------------------------------
% 0.22/0.51  % (4391)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.51  % (4381)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.52  % (4387)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f706,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f63,f138,f159,f316,f321,f322,f346,f349,f350,f477,f478,f479,f490,f491,f492,f494,f499,f503,f509,f510,f511,f512,f516,f573,f581,f582,f583,f701,f704,f705])).
% 0.22/0.52  fof(f705,plain,(
% 0.22/0.52    spl6_12 | ~spl6_9),
% 0.22/0.52    inference(avatar_split_clause,[],[f568,f152,f204])).
% 0.22/0.52  fof(f204,plain,(
% 0.22/0.52    spl6_12 <=> r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k2_xboole_0(sK1,sK2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.22/0.52  fof(f152,plain,(
% 0.22/0.52    spl6_9 <=> r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.22/0.52  fof(f568,plain,(
% 0.22/0.52    r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k2_xboole_0(sK1,sK2)) | ~spl6_9),
% 0.22/0.52    inference(resolution,[],[f153,f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 0.22/0.52    inference(equality_resolution,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.22/0.52    inference(cnf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f11])).
% 0.22/0.52  fof(f11,plain,(
% 0.22/0.52    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f10,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.22/0.52    inference(rectify,[],[f9])).
% 0.22/0.52  fof(f9,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.22/0.52    inference(flattening,[],[f8])).
% 0.22/0.52  fof(f8,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.22/0.52    inference(nnf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.22/0.52  fof(f153,plain,(
% 0.22/0.52    r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2))) | ~spl6_9),
% 0.22/0.52    inference(avatar_component_clause,[],[f152])).
% 0.22/0.52  fof(f704,plain,(
% 0.22/0.52    ~spl6_6 | spl6_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f524,f54,f86])).
% 0.22/0.52  fof(f86,plain,(
% 0.22/0.52    spl6_6 <=> r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(sK0,sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    spl6_2 <=> r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.52  fof(f524,plain,(
% 0.22/0.52    ~r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(sK0,sK1)) | spl6_2),
% 0.22/0.52    inference(resolution,[],[f55,f35])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 0.22/0.52    inference(equality_resolution,[],[f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK4(X0,X1,X2),X1) & ~r2_hidden(sK4(X0,X1,X2),X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f15,f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK4(X0,X1,X2),X1) & ~r2_hidden(sK4(X0,X1,X2),X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.22/0.52    inference(rectify,[],[f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.22/0.52    inference(flattening,[],[f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.22/0.52    inference(nnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    ~r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2))) | spl6_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f54])).
% 0.22/0.52  fof(f701,plain,(
% 0.22/0.52    spl6_13 | spl6_4 | ~spl6_12),
% 0.22/0.52    inference(avatar_split_clause,[],[f696,f204,f71,f318])).
% 0.22/0.52  fof(f318,plain,(
% 0.22/0.52    spl6_13 <=> r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.22/0.52  fof(f71,plain,(
% 0.22/0.52    spl6_4 <=> r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.52  fof(f696,plain,(
% 0.22/0.52    r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK2) | r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK1) | ~spl6_12),
% 0.22/0.52    inference(resolution,[],[f205,f36])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k2_xboole_0(X0,X1))) )),
% 0.22/0.52    inference(equality_resolution,[],[f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f205,plain,(
% 0.22/0.52    r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k2_xboole_0(sK1,sK2)) | ~spl6_12),
% 0.22/0.52    inference(avatar_component_clause,[],[f204])).
% 0.22/0.52  fof(f583,plain,(
% 0.22/0.52    spl6_5 | spl6_13 | ~spl6_11),
% 0.22/0.52    inference(avatar_split_clause,[],[f464,f200,f318,f75])).
% 0.22/0.52  fof(f75,plain,(
% 0.22/0.52    spl6_5 <=> r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.22/0.52  fof(f200,plain,(
% 0.22/0.52    spl6_11 <=> r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k2_xboole_0(sK0,sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.22/0.52  fof(f464,plain,(
% 0.22/0.52    r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK1) | r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK0) | ~spl6_11),
% 0.22/0.52    inference(resolution,[],[f201,f36])).
% 0.22/0.52  fof(f201,plain,(
% 0.22/0.52    r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k2_xboole_0(sK0,sK1)) | ~spl6_11),
% 0.22/0.52    inference(avatar_component_clause,[],[f200])).
% 0.22/0.52  fof(f582,plain,(
% 0.22/0.52    ~spl6_4 | ~spl6_5 | spl6_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f518,f58,f75,f71])).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    spl6_3 <=> r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(sK2,sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.52  fof(f518,plain,(
% 0.22/0.52    ~r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK0) | ~r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK2) | spl6_3),
% 0.22/0.52    inference(resolution,[],[f59,f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_xboole_0(X0,X1)) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 0.22/0.52    inference(equality_resolution,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 0.22/0.52    inference(cnf_transformation,[],[f12])).
% 0.22/0.52  fof(f59,plain,(
% 0.22/0.52    ~r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(sK2,sK0)) | spl6_3),
% 0.22/0.52    inference(avatar_component_clause,[],[f58])).
% 0.22/0.52  fof(f581,plain,(
% 0.22/0.52    spl6_4 | spl6_5 | ~spl6_1),
% 0.22/0.52    inference(avatar_split_clause,[],[f132,f50,f75,f71])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    spl6_1 <=> r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.52  fof(f132,plain,(
% 0.22/0.52    r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK0) | r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK2) | ~spl6_1),
% 0.22/0.52    inference(resolution,[],[f109,f36])).
% 0.22/0.52  fof(f109,plain,(
% 0.22/0.52    r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k2_xboole_0(sK2,sK0)) | ~spl6_1),
% 0.22/0.52    inference(resolution,[],[f52,f32])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))) | ~spl6_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f50])).
% 0.22/0.52  fof(f573,plain,(
% 0.22/0.52    spl6_11 | ~spl6_9),
% 0.22/0.52    inference(avatar_split_clause,[],[f567,f152,f200])).
% 0.22/0.52  fof(f567,plain,(
% 0.22/0.52    r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k2_xboole_0(sK0,sK1)) | ~spl6_9),
% 0.22/0.52    inference(resolution,[],[f153,f33])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 0.22/0.52    inference(equality_resolution,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.22/0.52    inference(cnf_transformation,[],[f12])).
% 0.22/0.52  fof(f516,plain,(
% 0.22/0.52    spl6_1 | spl6_3 | spl6_8 | spl6_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f99,f54,f95,f58,f50])).
% 0.22/0.52  fof(f95,plain,(
% 0.22/0.52    spl6_8 <=> sQ5_eqProxy(k2_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0)),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.22/0.52  fof(f99,plain,(
% 0.22/0.52    sQ5_eqProxy(k2_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0)),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))) | r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(sK2,sK0)) | r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))) | spl6_2),
% 0.22/0.52    inference(resolution,[],[f55,f44])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (sQ5_eqProxy(k2_xboole_0(X0,X1),X2) | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 0.22/0.52    inference(equality_proxy_replacement,[],[f28,f37])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ! [X1,X0] : (sQ5_eqProxy(X0,X1) <=> X0 = X1)),
% 0.22/0.52    introduced(equality_proxy_definition,[new_symbols(naming,[sQ5_eqProxy])])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f512,plain,(
% 0.22/0.52    spl6_13 | ~spl6_7),
% 0.22/0.52    inference(avatar_split_clause,[],[f333,f90,f318])).
% 0.22/0.52  fof(f90,plain,(
% 0.22/0.52    spl6_7 <=> r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(sK1,sK2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.22/0.52  fof(f333,plain,(
% 0.22/0.52    r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK1) | ~spl6_7),
% 0.22/0.52    inference(resolution,[],[f92,f33])).
% 0.22/0.52  fof(f92,plain,(
% 0.22/0.52    r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(sK1,sK2)) | ~spl6_7),
% 0.22/0.52    inference(avatar_component_clause,[],[f90])).
% 0.22/0.52  fof(f511,plain,(
% 0.22/0.52    spl6_4 | ~spl6_7),
% 0.22/0.52    inference(avatar_split_clause,[],[f334,f90,f71])).
% 0.22/0.52  fof(f334,plain,(
% 0.22/0.52    r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK2) | ~spl6_7),
% 0.22/0.52    inference(resolution,[],[f92,f32])).
% 0.22/0.52  fof(f510,plain,(
% 0.22/0.52    ~spl6_5 | spl6_11),
% 0.22/0.52    inference(avatar_split_clause,[],[f308,f200,f75])).
% 0.22/0.52  fof(f308,plain,(
% 0.22/0.52    ~r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK0) | spl6_11),
% 0.22/0.52    inference(resolution,[],[f202,f35])).
% 0.22/0.52  fof(f202,plain,(
% 0.22/0.52    ~r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k2_xboole_0(sK0,sK1)) | spl6_11),
% 0.22/0.52    inference(avatar_component_clause,[],[f200])).
% 0.22/0.52  fof(f509,plain,(
% 0.22/0.52    ~spl6_11 | ~spl6_12 | spl6_9),
% 0.22/0.52    inference(avatar_split_clause,[],[f194,f152,f204,f200])).
% 0.22/0.52  fof(f194,plain,(
% 0.22/0.52    ~r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k2_xboole_0(sK1,sK2)) | ~r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k2_xboole_0(sK0,sK1)) | spl6_9),
% 0.22/0.52    inference(resolution,[],[f154,f31])).
% 0.22/0.52  fof(f154,plain,(
% 0.22/0.52    ~r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2))) | spl6_9),
% 0.22/0.52    inference(avatar_component_clause,[],[f152])).
% 0.22/0.52  fof(f503,plain,(
% 0.22/0.52    spl6_9 | ~spl6_1),
% 0.22/0.52    inference(avatar_split_clause,[],[f108,f50,f152])).
% 0.22/0.52  fof(f108,plain,(
% 0.22/0.52    r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2))) | ~spl6_1),
% 0.22/0.52    inference(resolution,[],[f52,f33])).
% 0.22/0.52  fof(f499,plain,(
% 0.22/0.52    spl6_1 | spl6_2 | spl6_8 | spl6_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f220,f71,f95,f54,f50])).
% 0.22/0.52  fof(f220,plain,(
% 0.22/0.52    sQ5_eqProxy(k2_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0)),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))) | r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2))) | r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))) | spl6_4),
% 0.22/0.52    inference(resolution,[],[f116,f44])).
% 0.22/0.52  fof(f116,plain,(
% 0.22/0.52    ( ! [X2] : (~r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(sK2,X2))) ) | spl6_4),
% 0.22/0.52    inference(resolution,[],[f73,f33])).
% 0.22/0.52  fof(f73,plain,(
% 0.22/0.52    ~r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK2) | spl6_4),
% 0.22/0.52    inference(avatar_component_clause,[],[f71])).
% 0.22/0.52  fof(f494,plain,(
% 0.22/0.52    spl6_5 | ~spl6_6),
% 0.22/0.52    inference(avatar_split_clause,[],[f160,f86,f75])).
% 0.22/0.52  fof(f160,plain,(
% 0.22/0.52    r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK0) | ~spl6_6),
% 0.22/0.52    inference(resolution,[],[f88,f33])).
% 0.22/0.52  fof(f88,plain,(
% 0.22/0.52    r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(sK0,sK1)) | ~spl6_6),
% 0.22/0.52    inference(avatar_component_clause,[],[f86])).
% 0.22/0.52  fof(f492,plain,(
% 0.22/0.52    ~spl6_13 | spl6_12),
% 0.22/0.52    inference(avatar_split_clause,[],[f469,f204,f318])).
% 0.22/0.52  fof(f469,plain,(
% 0.22/0.52    ~r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK1) | spl6_12),
% 0.22/0.52    inference(resolution,[],[f206,f35])).
% 0.22/0.52  fof(f206,plain,(
% 0.22/0.52    ~r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k2_xboole_0(sK1,sK2)) | spl6_12),
% 0.22/0.52    inference(avatar_component_clause,[],[f204])).
% 0.22/0.52  fof(f491,plain,(
% 0.22/0.52    ~spl6_4 | spl6_12),
% 0.22/0.52    inference(avatar_split_clause,[],[f470,f204,f71])).
% 0.22/0.52  fof(f470,plain,(
% 0.22/0.52    ~r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK2) | spl6_12),
% 0.22/0.52    inference(resolution,[],[f206,f34])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 0.22/0.52    inference(equality_resolution,[],[f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f490,plain,(
% 0.22/0.52    ~spl6_13 | ~spl6_4 | spl6_7),
% 0.22/0.52    inference(avatar_split_clause,[],[f127,f90,f71,f318])).
% 0.22/0.52  fof(f127,plain,(
% 0.22/0.52    ~r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK2) | ~r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK1) | spl6_7),
% 0.22/0.52    inference(resolution,[],[f91,f31])).
% 0.22/0.52  fof(f91,plain,(
% 0.22/0.52    ~r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(sK1,sK2)) | spl6_7),
% 0.22/0.52    inference(avatar_component_clause,[],[f90])).
% 0.22/0.52  fof(f479,plain,(
% 0.22/0.52    ~spl6_4 | spl6_10),
% 0.22/0.52    inference(avatar_split_clause,[],[f171,f156,f71])).
% 0.22/0.52  fof(f156,plain,(
% 0.22/0.52    spl6_10 <=> r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k2_xboole_0(sK2,sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.22/0.52  fof(f171,plain,(
% 0.22/0.52    ~r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK2) | spl6_10),
% 0.22/0.52    inference(resolution,[],[f158,f35])).
% 0.22/0.52  fof(f158,plain,(
% 0.22/0.52    ~r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k2_xboole_0(sK2,sK0)) | spl6_10),
% 0.22/0.52    inference(avatar_component_clause,[],[f156])).
% 0.22/0.52  fof(f478,plain,(
% 0.22/0.52    ~spl6_5 | spl6_10),
% 0.22/0.52    inference(avatar_split_clause,[],[f172,f156,f75])).
% 0.22/0.52  fof(f172,plain,(
% 0.22/0.52    ~r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK0) | spl6_10),
% 0.22/0.52    inference(resolution,[],[f158,f34])).
% 0.22/0.52  fof(f477,plain,(
% 0.22/0.52    spl6_5 | ~spl6_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f353,f58,f75])).
% 0.22/0.52  fof(f353,plain,(
% 0.22/0.52    r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK0) | ~spl6_3),
% 0.22/0.52    inference(resolution,[],[f60,f32])).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(sK2,sK0)) | ~spl6_3),
% 0.22/0.52    inference(avatar_component_clause,[],[f58])).
% 0.22/0.52  fof(f350,plain,(
% 0.22/0.52    ~spl6_7 | spl6_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f101,f54,f90])).
% 0.22/0.52  fof(f101,plain,(
% 0.22/0.52    ~r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(sK1,sK2)) | spl6_2),
% 0.22/0.52    inference(resolution,[],[f55,f34])).
% 0.22/0.52  fof(f349,plain,(
% 0.22/0.52    ~spl6_8),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f348])).
% 0.22/0.52  fof(f348,plain,(
% 0.22/0.52    $false | ~spl6_8),
% 0.22/0.52    inference(resolution,[],[f97,f38])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ~sQ5_eqProxy(k2_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0)),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0)))),
% 0.22/0.52    inference(equality_proxy_replacement,[],[f18,f37])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    k2_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0)) != k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),
% 0.22/0.52    inference(cnf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,plain,(
% 0.22/0.52    k2_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0)) != k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f6])).
% 0.22/0.52  fof(f6,plain,(
% 0.22/0.52    ? [X0,X1,X2] : k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) != k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0)) => k2_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0)) != k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f5,plain,(
% 0.22/0.52    ? [X0,X1,X2] : k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) != k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) = k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0))),
% 0.22/0.52    inference(negated_conjecture,[],[f3])).
% 0.22/0.52  fof(f3,conjecture,(
% 0.22/0.52    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) = k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_xboole_1)).
% 0.22/0.52  fof(f97,plain,(
% 0.22/0.52    sQ5_eqProxy(k2_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0)),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))) | ~spl6_8),
% 0.22/0.52    inference(avatar_component_clause,[],[f95])).
% 0.22/0.52  fof(f346,plain,(
% 0.22/0.52    spl6_13 | ~spl6_6),
% 0.22/0.52    inference(avatar_split_clause,[],[f161,f86,f318])).
% 0.22/0.52  fof(f161,plain,(
% 0.22/0.52    r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK1) | ~spl6_6),
% 0.22/0.52    inference(resolution,[],[f88,f32])).
% 0.22/0.52  fof(f322,plain,(
% 0.22/0.52    ~spl6_13 | spl6_11),
% 0.22/0.52    inference(avatar_split_clause,[],[f309,f200,f318])).
% 0.22/0.52  fof(f309,plain,(
% 0.22/0.52    ~r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK1) | spl6_11),
% 0.22/0.52    inference(resolution,[],[f202,f34])).
% 0.22/0.52  fof(f321,plain,(
% 0.22/0.52    ~spl6_5 | ~spl6_13 | spl6_6),
% 0.22/0.52    inference(avatar_split_clause,[],[f122,f86,f318,f75])).
% 0.22/0.52  fof(f122,plain,(
% 0.22/0.52    ~r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK1) | ~r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK0) | spl6_6),
% 0.22/0.52    inference(resolution,[],[f87,f31])).
% 0.22/0.52  fof(f87,plain,(
% 0.22/0.52    ~r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(sK0,sK1)) | spl6_6),
% 0.22/0.52    inference(avatar_component_clause,[],[f86])).
% 0.22/0.52  fof(f316,plain,(
% 0.22/0.52    spl6_6 | spl6_7 | ~spl6_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f80,f54,f90,f86])).
% 0.22/0.52  fof(f80,plain,(
% 0.22/0.52    r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(sK1,sK2)) | r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(sK0,sK1)) | ~spl6_2),
% 0.22/0.52    inference(resolution,[],[f56,f36])).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2))) | ~spl6_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f54])).
% 0.22/0.52  fof(f159,plain,(
% 0.22/0.52    ~spl6_9 | ~spl6_10 | spl6_1),
% 0.22/0.52    inference(avatar_split_clause,[],[f146,f50,f156,f152])).
% 0.22/0.52  fof(f146,plain,(
% 0.22/0.52    ~r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k2_xboole_0(sK2,sK0)) | ~r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2))) | spl6_1),
% 0.22/0.52    inference(resolution,[],[f51,f31])).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    ~r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))) | spl6_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f50])).
% 0.22/0.52  fof(f138,plain,(
% 0.22/0.52    ~spl6_1 | spl6_8 | ~spl6_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f79,f54,f95,f50])).
% 0.22/0.52  fof(f79,plain,(
% 0.22/0.52    sQ5_eqProxy(k2_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0)),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))) | ~r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))) | ~spl6_2),
% 0.22/0.52    inference(resolution,[],[f56,f43])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (sQ5_eqProxy(k2_xboole_0(X0,X1),X2) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 0.22/0.52    inference(equality_proxy_replacement,[],[f29,f37])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    ~spl6_1 | ~spl6_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f48,f58,f50])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    ~r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(sK2,sK0)) | ~r2_hidden(sK4(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0)))),
% 0.22/0.52    inference(resolution,[],[f38,f42])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (sQ5_eqProxy(k2_xboole_0(X0,X1),X2) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 0.22/0.52    inference(equality_proxy_replacement,[],[f30,f37])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (4387)------------------------------
% 0.22/0.52  % (4387)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (4387)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (4387)Memory used [KB]: 6396
% 0.22/0.52  % (4387)Time elapsed: 0.089 s
% 0.22/0.52  % (4387)------------------------------
% 0.22/0.52  % (4387)------------------------------
% 0.22/0.52  % (4374)Success in time 0.158 s
%------------------------------------------------------------------------------
