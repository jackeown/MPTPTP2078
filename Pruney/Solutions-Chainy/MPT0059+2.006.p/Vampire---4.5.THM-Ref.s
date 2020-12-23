%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:13 EST 2020

% Result     : Theorem 1.72s
% Output     : Refutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 227 expanded)
%              Number of leaves         :   16 (  83 expanded)
%              Depth                    :   10
%              Number of atoms          :  390 (1373 expanded)
%              Number of equality atoms :   47 ( 177 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f274,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f90,f95,f96,f122,f182,f205,f221,f239,f267,f268,f269,f272,f273])).

fof(f273,plain,
    ( spl8_2
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f257,f236,f87])).

fof(f87,plain,
    ( spl8_2
  <=> r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f236,plain,
    ( spl8_8
  <=> r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k3_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f257,plain,
    ( r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK0)
    | ~ spl8_8 ),
    inference(resolution,[],[f238,f60])).

fof(f60,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f22])).

fof(f22,plain,(
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

fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f238,plain,
    ( r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k3_xboole_0(sK0,sK2))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f236])).

fof(f272,plain,
    ( spl8_5
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f258,f236,f119])).

fof(f119,plain,
    ( spl8_5
  <=> r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f258,plain,
    ( r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK2)
    | ~ spl8_8 ),
    inference(resolution,[],[f238,f59])).

fof(f59,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f269,plain,
    ( spl8_2
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f247,f232,f87])).

fof(f232,plain,
    ( spl8_7
  <=> r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f247,plain,
    ( r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK0)
    | ~ spl8_7 ),
    inference(resolution,[],[f234,f66])).

fof(f66,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK6(X0,X1,X2),X1)
            | ~ r2_hidden(sK6(X0,X1,X2),X0)
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK6(X0,X1,X2),X1)
              & r2_hidden(sK6(X0,X1,X2),X0) )
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f31,f32])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK6(X0,X1,X2),X1)
          | ~ r2_hidden(sK6(X0,X1,X2),X0)
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK6(X0,X1,X2),X1)
            & r2_hidden(sK6(X0,X1,X2),X0) )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f234,plain,
    ( r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k4_xboole_0(sK0,sK1))
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f232])).

fof(f268,plain,
    ( ~ spl8_4
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f248,f232,f115])).

fof(f115,plain,
    ( spl8_4
  <=> r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f248,plain,
    ( ~ r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK1)
    | ~ spl8_7 ),
    inference(resolution,[],[f234,f65])).

fof(f65,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f267,plain,
    ( spl8_4
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f211,f92,f115])).

fof(f92,plain,
    ( spl8_3
  <=> r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f211,plain,
    ( r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK1)
    | ~ spl8_3 ),
    inference(resolution,[],[f93,f66])).

fof(f93,plain,
    ( r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k4_xboole_0(sK1,sK2))
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f92])).

fof(f239,plain,
    ( spl8_7
    | spl8_8
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f222,f83,f236,f232])).

fof(f83,plain,
    ( spl8_1
  <=> r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f222,plain,
    ( r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k3_xboole_0(sK0,sK2))
    | r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k4_xboole_0(sK0,sK1))
    | ~ spl8_1 ),
    inference(resolution,[],[f85,f63])).

fof(f63,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
              & ~ r2_hidden(sK5(X0,X1,X2),X0) )
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( r2_hidden(sK5(X0,X1,X2),X1)
            | r2_hidden(sK5(X0,X1,X2),X0)
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f26,f27])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            & ~ r2_hidden(sK5(X0,X1,X2),X0) )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( r2_hidden(sK5(X0,X1,X2),X1)
          | r2_hidden(sK5(X0,X1,X2),X0)
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f85,plain,
    ( r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f83])).

fof(f221,plain,
    ( ~ spl8_5
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f212,f92,f119])).

fof(f212,plain,
    ( ~ r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK2)
    | ~ spl8_3 ),
    inference(resolution,[],[f93,f65])).

fof(f205,plain,
    ( ~ spl8_2
    | ~ spl8_5
    | spl8_1 ),
    inference(avatar_split_clause,[],[f197,f83,f119,f87])).

fof(f197,plain,
    ( ~ r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK2)
    | ~ r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK0)
    | spl8_1 ),
    inference(resolution,[],[f126,f58])).

fof(f58,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f126,plain,
    ( ~ r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k3_xboole_0(sK0,sK2))
    | spl8_1 ),
    inference(resolution,[],[f84,f61])).

fof(f61,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f84,plain,
    ( ~ r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f83])).

fof(f182,plain,
    ( ~ spl8_2
    | spl8_4
    | spl8_1 ),
    inference(avatar_split_clause,[],[f174,f83,f115,f87])).

fof(f174,plain,
    ( r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK1)
    | ~ r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK0)
    | spl8_1 ),
    inference(resolution,[],[f125,f64])).

fof(f64,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f125,plain,
    ( ~ r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k4_xboole_0(sK0,sK1))
    | spl8_1 ),
    inference(resolution,[],[f84,f62])).

fof(f62,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f122,plain,
    ( ~ spl8_4
    | spl8_5
    | spl8_3 ),
    inference(avatar_split_clause,[],[f106,f92,f119,f115])).

fof(f106,plain,
    ( r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK2)
    | ~ r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK1)
    | spl8_3 ),
    inference(resolution,[],[f94,f64])).

fof(f94,plain,
    ( ~ r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k4_xboole_0(sK1,sK2))
    | spl8_3 ),
    inference(avatar_component_clause,[],[f92])).

fof(f96,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | spl8_3 ),
    inference(avatar_split_clause,[],[f81,f92,f87,f83])).

fof(f81,plain,
    ( r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k4_xboole_0(sK1,sK2))
    | ~ r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK0)
    | ~ r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))) ),
    inference(resolution,[],[f68,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( sQ7_eqProxy(k4_xboole_0(X0,X1),X2)
      | r2_hidden(sK6(X0,X1,X2),X1)
      | ~ r2_hidden(sK6(X0,X1,X2),X0)
      | ~ r2_hidden(sK6(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f56,f67])).

fof(f67,plain,(
    ! [X1,X0] :
      ( sQ7_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ7_eqProxy])])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK6(X0,X1,X2),X1)
      | ~ r2_hidden(sK6(X0,X1,X2),X0)
      | ~ r2_hidden(sK6(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f68,plain,(
    ~ sQ7_eqProxy(k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))) ),
    inference(equality_proxy_replacement,[],[f34,f67])).

fof(f34,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))
   => k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f95,plain,
    ( spl8_1
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f80,f92,f83])).

fof(f80,plain,
    ( ~ r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k4_xboole_0(sK1,sK2))
    | r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))) ),
    inference(resolution,[],[f68,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( sQ7_eqProxy(k4_xboole_0(X0,X1),X2)
      | ~ r2_hidden(sK6(X0,X1,X2),X1)
      | r2_hidden(sK6(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f55,f67])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK6(X0,X1,X2),X1)
      | r2_hidden(sK6(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f90,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f79,f87,f83])).

fof(f79,plain,
    ( r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK0)
    | r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))) ),
    inference(resolution,[],[f68,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( sQ7_eqProxy(k4_xboole_0(X0,X1),X2)
      | r2_hidden(sK6(X0,X1,X2),X0)
      | r2_hidden(sK6(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f54,f67])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK6(X0,X1,X2),X0)
      | r2_hidden(sK6(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:30:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.54  % (29791)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.55  % (29796)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.55  % (29805)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.56  % (29811)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.37/0.56  % (29813)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.37/0.56  % (29813)Refutation not found, incomplete strategy% (29813)------------------------------
% 1.37/0.56  % (29813)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.56  % (29813)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.56  
% 1.37/0.56  % (29813)Memory used [KB]: 10618
% 1.37/0.56  % (29813)Time elapsed: 0.131 s
% 1.37/0.56  % (29813)------------------------------
% 1.37/0.56  % (29813)------------------------------
% 1.37/0.57  % (29806)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.37/0.58  % (29803)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.37/0.58  % (29811)Refutation not found, incomplete strategy% (29811)------------------------------
% 1.37/0.58  % (29811)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.58  % (29811)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.58  
% 1.37/0.58  % (29811)Memory used [KB]: 10746
% 1.37/0.58  % (29811)Time elapsed: 0.151 s
% 1.37/0.58  % (29811)------------------------------
% 1.37/0.58  % (29811)------------------------------
% 1.37/0.58  % (29801)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.72/0.59  % (29795)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.72/0.59  % (29814)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.72/0.59  % (29800)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.72/0.60  % (29806)Refutation found. Thanks to Tanya!
% 1.72/0.60  % SZS status Theorem for theBenchmark
% 1.72/0.60  % SZS output start Proof for theBenchmark
% 1.72/0.60  fof(f274,plain,(
% 1.72/0.60    $false),
% 1.72/0.60    inference(avatar_sat_refutation,[],[f90,f95,f96,f122,f182,f205,f221,f239,f267,f268,f269,f272,f273])).
% 1.72/0.60  fof(f273,plain,(
% 1.72/0.60    spl8_2 | ~spl8_8),
% 1.72/0.60    inference(avatar_split_clause,[],[f257,f236,f87])).
% 1.72/0.60  fof(f87,plain,(
% 1.72/0.60    spl8_2 <=> r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK0)),
% 1.72/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.72/0.60  fof(f236,plain,(
% 1.72/0.60    spl8_8 <=> r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k3_xboole_0(sK0,sK2))),
% 1.72/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 1.72/0.60  fof(f257,plain,(
% 1.72/0.60    r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK0) | ~spl8_8),
% 1.72/0.60    inference(resolution,[],[f238,f60])).
% 1.72/0.60  fof(f60,plain,(
% 1.72/0.60    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 1.72/0.60    inference(equality_resolution,[],[f39])).
% 1.72/0.60  fof(f39,plain,(
% 1.72/0.60    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.72/0.60    inference(cnf_transformation,[],[f23])).
% 1.72/0.60  fof(f23,plain,(
% 1.72/0.60    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.72/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f22])).
% 1.72/0.60  fof(f22,plain,(
% 1.72/0.60    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.72/0.60    introduced(choice_axiom,[])).
% 1.72/0.60  fof(f21,plain,(
% 1.72/0.60    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.72/0.60    inference(rectify,[],[f20])).
% 1.72/0.60  fof(f20,plain,(
% 1.72/0.60    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.72/0.60    inference(flattening,[],[f19])).
% 1.72/0.60  fof(f19,plain,(
% 1.72/0.60    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.72/0.60    inference(nnf_transformation,[],[f3])).
% 1.72/0.60  fof(f3,axiom,(
% 1.72/0.60    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.72/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.72/0.60  fof(f238,plain,(
% 1.72/0.60    r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k3_xboole_0(sK0,sK2)) | ~spl8_8),
% 1.72/0.60    inference(avatar_component_clause,[],[f236])).
% 1.72/0.60  fof(f272,plain,(
% 1.72/0.60    spl8_5 | ~spl8_8),
% 1.72/0.60    inference(avatar_split_clause,[],[f258,f236,f119])).
% 1.72/0.60  fof(f119,plain,(
% 1.72/0.60    spl8_5 <=> r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK2)),
% 1.72/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 1.72/0.60  fof(f258,plain,(
% 1.72/0.60    r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK2) | ~spl8_8),
% 1.72/0.60    inference(resolution,[],[f238,f59])).
% 1.72/0.60  fof(f59,plain,(
% 1.72/0.60    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 1.72/0.60    inference(equality_resolution,[],[f40])).
% 1.72/0.60  fof(f40,plain,(
% 1.72/0.60    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.72/0.60    inference(cnf_transformation,[],[f23])).
% 1.72/0.60  fof(f269,plain,(
% 1.72/0.60    spl8_2 | ~spl8_7),
% 1.72/0.60    inference(avatar_split_clause,[],[f247,f232,f87])).
% 1.72/0.60  fof(f232,plain,(
% 1.72/0.60    spl8_7 <=> r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k4_xboole_0(sK0,sK1))),
% 1.72/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 1.72/0.60  fof(f247,plain,(
% 1.72/0.60    r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK0) | ~spl8_7),
% 1.72/0.60    inference(resolution,[],[f234,f66])).
% 1.72/0.60  fof(f66,plain,(
% 1.72/0.60    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 1.72/0.60    inference(equality_resolution,[],[f51])).
% 1.72/0.60  fof(f51,plain,(
% 1.72/0.60    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.72/0.60    inference(cnf_transformation,[],[f33])).
% 1.72/0.60  fof(f33,plain,(
% 1.72/0.60    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((~r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),X0)) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.72/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f31,f32])).
% 1.72/0.60  fof(f32,plain,(
% 1.72/0.60    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((~r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),X0)) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 1.72/0.60    introduced(choice_axiom,[])).
% 1.72/0.60  fof(f31,plain,(
% 1.72/0.60    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.72/0.60    inference(rectify,[],[f30])).
% 1.72/0.60  fof(f30,plain,(
% 1.72/0.60    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.72/0.60    inference(flattening,[],[f29])).
% 1.72/0.60  fof(f29,plain,(
% 1.72/0.60    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.72/0.60    inference(nnf_transformation,[],[f4])).
% 1.72/0.60  fof(f4,axiom,(
% 1.72/0.60    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.72/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.72/0.60  fof(f234,plain,(
% 1.72/0.60    r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k4_xboole_0(sK0,sK1)) | ~spl8_7),
% 1.72/0.60    inference(avatar_component_clause,[],[f232])).
% 1.72/0.60  fof(f268,plain,(
% 1.72/0.60    ~spl8_4 | ~spl8_7),
% 1.72/0.60    inference(avatar_split_clause,[],[f248,f232,f115])).
% 1.72/0.60  fof(f115,plain,(
% 1.72/0.60    spl8_4 <=> r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK1)),
% 1.72/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.72/0.60  fof(f248,plain,(
% 1.72/0.60    ~r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK1) | ~spl8_7),
% 1.72/0.60    inference(resolution,[],[f234,f65])).
% 1.72/0.60  fof(f65,plain,(
% 1.72/0.60    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 1.72/0.60    inference(equality_resolution,[],[f52])).
% 1.72/0.60  fof(f52,plain,(
% 1.72/0.60    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.72/0.60    inference(cnf_transformation,[],[f33])).
% 1.72/0.60  fof(f267,plain,(
% 1.72/0.60    spl8_4 | ~spl8_3),
% 1.72/0.60    inference(avatar_split_clause,[],[f211,f92,f115])).
% 1.72/0.60  fof(f92,plain,(
% 1.72/0.60    spl8_3 <=> r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k4_xboole_0(sK1,sK2))),
% 1.72/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.72/0.60  fof(f211,plain,(
% 1.72/0.60    r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK1) | ~spl8_3),
% 1.72/0.60    inference(resolution,[],[f93,f66])).
% 1.72/0.60  fof(f93,plain,(
% 1.72/0.60    r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k4_xboole_0(sK1,sK2)) | ~spl8_3),
% 1.72/0.60    inference(avatar_component_clause,[],[f92])).
% 1.72/0.60  fof(f239,plain,(
% 1.72/0.60    spl8_7 | spl8_8 | ~spl8_1),
% 1.72/0.60    inference(avatar_split_clause,[],[f222,f83,f236,f232])).
% 1.72/0.60  fof(f83,plain,(
% 1.72/0.60    spl8_1 <=> r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)))),
% 1.72/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.72/0.60  fof(f222,plain,(
% 1.72/0.60    r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k3_xboole_0(sK0,sK2)) | r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k4_xboole_0(sK0,sK1)) | ~spl8_1),
% 1.72/0.60    inference(resolution,[],[f85,f63])).
% 1.72/0.60  fof(f63,plain,(
% 1.72/0.60    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k2_xboole_0(X0,X1))) )),
% 1.72/0.60    inference(equality_resolution,[],[f45])).
% 1.72/0.60  fof(f45,plain,(
% 1.72/0.60    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.72/0.60    inference(cnf_transformation,[],[f28])).
% 1.72/0.60  fof(f28,plain,(
% 1.72/0.60    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK5(X0,X1,X2),X1) & ~r2_hidden(sK5(X0,X1,X2),X0)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.72/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f26,f27])).
% 1.72/0.60  fof(f27,plain,(
% 1.72/0.60    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK5(X0,X1,X2),X1) & ~r2_hidden(sK5(X0,X1,X2),X0)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 1.72/0.60    introduced(choice_axiom,[])).
% 1.72/0.60  fof(f26,plain,(
% 1.72/0.60    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.72/0.60    inference(rectify,[],[f25])).
% 1.72/0.60  fof(f25,plain,(
% 1.72/0.60    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.72/0.60    inference(flattening,[],[f24])).
% 1.72/0.60  fof(f24,plain,(
% 1.72/0.60    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.72/0.60    inference(nnf_transformation,[],[f2])).
% 1.72/0.60  fof(f2,axiom,(
% 1.72/0.60    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.72/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.72/0.60  fof(f85,plain,(
% 1.72/0.60    r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))) | ~spl8_1),
% 1.72/0.60    inference(avatar_component_clause,[],[f83])).
% 1.72/0.60  fof(f221,plain,(
% 1.72/0.60    ~spl8_5 | ~spl8_3),
% 1.72/0.60    inference(avatar_split_clause,[],[f212,f92,f119])).
% 1.72/0.60  fof(f212,plain,(
% 1.72/0.60    ~r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK2) | ~spl8_3),
% 1.72/0.60    inference(resolution,[],[f93,f65])).
% 1.72/0.60  fof(f205,plain,(
% 1.72/0.60    ~spl8_2 | ~spl8_5 | spl8_1),
% 1.72/0.60    inference(avatar_split_clause,[],[f197,f83,f119,f87])).
% 1.72/0.60  fof(f197,plain,(
% 1.72/0.60    ~r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK2) | ~r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK0) | spl8_1),
% 1.72/0.60    inference(resolution,[],[f126,f58])).
% 1.72/0.60  fof(f58,plain,(
% 1.72/0.60    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_xboole_0(X0,X1)) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 1.72/0.60    inference(equality_resolution,[],[f41])).
% 1.72/0.60  fof(f41,plain,(
% 1.72/0.60    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 1.72/0.60    inference(cnf_transformation,[],[f23])).
% 1.72/0.60  fof(f126,plain,(
% 1.72/0.60    ~r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k3_xboole_0(sK0,sK2)) | spl8_1),
% 1.72/0.60    inference(resolution,[],[f84,f61])).
% 1.72/0.60  fof(f61,plain,(
% 1.72/0.60    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 1.72/0.60    inference(equality_resolution,[],[f47])).
% 1.72/0.60  fof(f47,plain,(
% 1.72/0.60    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 1.72/0.60    inference(cnf_transformation,[],[f28])).
% 1.72/0.60  fof(f84,plain,(
% 1.72/0.60    ~r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))) | spl8_1),
% 1.72/0.60    inference(avatar_component_clause,[],[f83])).
% 1.72/0.60  fof(f182,plain,(
% 1.72/0.60    ~spl8_2 | spl8_4 | spl8_1),
% 1.72/0.60    inference(avatar_split_clause,[],[f174,f83,f115,f87])).
% 1.72/0.60  fof(f174,plain,(
% 1.72/0.60    r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK1) | ~r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK0) | spl8_1),
% 1.72/0.60    inference(resolution,[],[f125,f64])).
% 1.72/0.60  fof(f64,plain,(
% 1.72/0.60    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 1.72/0.60    inference(equality_resolution,[],[f53])).
% 1.72/0.60  fof(f53,plain,(
% 1.72/0.60    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 1.72/0.60    inference(cnf_transformation,[],[f33])).
% 1.72/0.60  fof(f125,plain,(
% 1.72/0.60    ~r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k4_xboole_0(sK0,sK1)) | spl8_1),
% 1.72/0.60    inference(resolution,[],[f84,f62])).
% 1.72/0.60  fof(f62,plain,(
% 1.72/0.60    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 1.72/0.60    inference(equality_resolution,[],[f46])).
% 1.72/0.60  fof(f46,plain,(
% 1.72/0.60    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 1.72/0.60    inference(cnf_transformation,[],[f28])).
% 1.72/0.60  fof(f122,plain,(
% 1.72/0.60    ~spl8_4 | spl8_5 | spl8_3),
% 1.72/0.60    inference(avatar_split_clause,[],[f106,f92,f119,f115])).
% 1.72/0.60  fof(f106,plain,(
% 1.72/0.60    r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK2) | ~r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK1) | spl8_3),
% 1.72/0.60    inference(resolution,[],[f94,f64])).
% 1.72/0.60  fof(f94,plain,(
% 1.72/0.60    ~r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k4_xboole_0(sK1,sK2)) | spl8_3),
% 1.72/0.60    inference(avatar_component_clause,[],[f92])).
% 1.72/0.60  fof(f96,plain,(
% 1.72/0.60    ~spl8_1 | ~spl8_2 | spl8_3),
% 1.72/0.60    inference(avatar_split_clause,[],[f81,f92,f87,f83])).
% 1.72/0.60  fof(f81,plain,(
% 1.72/0.60    r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k4_xboole_0(sK1,sK2)) | ~r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK0) | ~r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)))),
% 1.72/0.60    inference(resolution,[],[f68,f75])).
% 1.72/0.60  fof(f75,plain,(
% 1.72/0.60    ( ! [X2,X0,X1] : (sQ7_eqProxy(k4_xboole_0(X0,X1),X2) | r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) )),
% 1.72/0.60    inference(equality_proxy_replacement,[],[f56,f67])).
% 1.72/0.60  fof(f67,plain,(
% 1.72/0.60    ! [X1,X0] : (sQ7_eqProxy(X0,X1) <=> X0 = X1)),
% 1.72/0.60    introduced(equality_proxy_definition,[new_symbols(naming,[sQ7_eqProxy])])).
% 1.72/0.60  fof(f56,plain,(
% 1.72/0.60    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) )),
% 1.72/0.60    inference(cnf_transformation,[],[f33])).
% 1.72/0.60  fof(f68,plain,(
% 1.72/0.60    ~sQ7_eqProxy(k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)))),
% 1.72/0.60    inference(equality_proxy_replacement,[],[f34,f67])).
% 1.72/0.60  fof(f34,plain,(
% 1.72/0.60    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),
% 1.72/0.60    inference(cnf_transformation,[],[f14])).
% 1.72/0.60  fof(f14,plain,(
% 1.72/0.60    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),
% 1.72/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f13])).
% 1.72/0.60  fof(f13,plain,(
% 1.72/0.60    ? [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) => k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),
% 1.72/0.60    introduced(choice_axiom,[])).
% 1.72/0.60  fof(f9,plain,(
% 1.72/0.60    ? [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 1.72/0.60    inference(ennf_transformation,[],[f8])).
% 1.72/0.60  fof(f8,negated_conjecture,(
% 1.72/0.60    ~! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 1.72/0.60    inference(negated_conjecture,[],[f7])).
% 1.72/0.60  fof(f7,conjecture,(
% 1.72/0.60    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 1.72/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).
% 1.72/0.60  fof(f95,plain,(
% 1.72/0.60    spl8_1 | ~spl8_3),
% 1.72/0.60    inference(avatar_split_clause,[],[f80,f92,f83])).
% 1.72/0.60  fof(f80,plain,(
% 1.72/0.60    ~r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k4_xboole_0(sK1,sK2)) | r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)))),
% 1.72/0.60    inference(resolution,[],[f68,f76])).
% 1.72/0.60  fof(f76,plain,(
% 1.72/0.60    ( ! [X2,X0,X1] : (sQ7_eqProxy(k4_xboole_0(X0,X1),X2) | ~r2_hidden(sK6(X0,X1,X2),X1) | r2_hidden(sK6(X0,X1,X2),X2)) )),
% 1.72/0.60    inference(equality_proxy_replacement,[],[f55,f67])).
% 1.72/0.60  fof(f55,plain,(
% 1.72/0.60    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK6(X0,X1,X2),X1) | r2_hidden(sK6(X0,X1,X2),X2)) )),
% 1.72/0.60    inference(cnf_transformation,[],[f33])).
% 1.72/0.60  fof(f90,plain,(
% 1.72/0.60    spl8_1 | spl8_2),
% 1.72/0.60    inference(avatar_split_clause,[],[f79,f87,f83])).
% 1.72/0.60  fof(f79,plain,(
% 1.72/0.60    r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),sK0) | r2_hidden(sK6(sK0,k4_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)))),
% 1.72/0.60    inference(resolution,[],[f68,f77])).
% 1.72/0.60  fof(f77,plain,(
% 1.72/0.60    ( ! [X2,X0,X1] : (sQ7_eqProxy(k4_xboole_0(X0,X1),X2) | r2_hidden(sK6(X0,X1,X2),X0) | r2_hidden(sK6(X0,X1,X2),X2)) )),
% 1.72/0.60    inference(equality_proxy_replacement,[],[f54,f67])).
% 1.72/0.60  fof(f54,plain,(
% 1.72/0.60    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK6(X0,X1,X2),X0) | r2_hidden(sK6(X0,X1,X2),X2)) )),
% 1.72/0.60    inference(cnf_transformation,[],[f33])).
% 1.72/0.60  % SZS output end Proof for theBenchmark
% 1.72/0.60  % (29806)------------------------------
% 1.72/0.60  % (29806)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.60  % (29806)Termination reason: Refutation
% 1.72/0.60  
% 1.72/0.60  % (29806)Memory used [KB]: 6268
% 1.72/0.60  % (29806)Time elapsed: 0.119 s
% 1.72/0.60  % (29806)------------------------------
% 1.72/0.60  % (29806)------------------------------
% 1.72/0.60  % (29797)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.72/0.60  % (29790)Success in time 0.233 s
%------------------------------------------------------------------------------
