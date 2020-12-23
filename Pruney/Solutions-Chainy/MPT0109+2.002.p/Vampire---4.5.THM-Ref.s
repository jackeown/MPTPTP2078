%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:28 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 317 expanded)
%              Number of leaves         :   19 ( 116 expanded)
%              Depth                    :   10
%              Number of atoms          :  481 (1795 expanded)
%              Number of equality atoms :   47 ( 207 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1309,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f87,f88,f265,f514,f516,f552,f932,f1019,f1033,f1047,f1294,f1300,f1302,f1303,f1304,f1305,f1306,f1307,f1308])).

fof(f1308,plain,
    ( ~ spl7_4
    | spl7_6 ),
    inference(avatar_split_clause,[],[f1282,f262,f114])).

fof(f114,plain,
    ( spl7_4
  <=> r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f262,plain,
    ( spl7_6
  <=> r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f1282,plain,
    ( ~ r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),sK1)
    | spl7_6 ),
    inference(resolution,[],[f263,f57])).

% (29766)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f57,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f23,f24])).

fof(f24,plain,(
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

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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

fof(f263,plain,
    ( ~ r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k2_xboole_0(sK1,sK2))
    | spl7_6 ),
    inference(avatar_component_clause,[],[f262])).

fof(f1307,plain,
    ( ~ spl7_6
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f1022,f925,f262])).

fof(f925,plain,
    ( spl7_9
  <=> r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f1022,plain,
    ( ~ r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k2_xboole_0(sK1,sK2))
    | ~ spl7_9 ),
    inference(resolution,[],[f927,f51])).

fof(f51,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f14])).

fof(f14,plain,(
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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f12])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f927,plain,
    ( r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f925])).

fof(f1306,plain,
    ( spl7_4
    | spl7_5
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f501,f262,f118,f114])).

fof(f118,plain,
    ( spl7_5
  <=> r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f501,plain,
    ( r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),sK2)
    | r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),sK1)
    | ~ spl7_6 ),
    inference(resolution,[],[f264,f58])).

fof(f58,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f264,plain,
    ( r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k2_xboole_0(sK1,sK2))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f262])).

fof(f1305,plain,
    ( spl7_4
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f1008,f549,f114])).

fof(f549,plain,
    ( spl7_8
  <=> r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f1008,plain,
    ( r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),sK1)
    | ~ spl7_8 ),
    inference(resolution,[],[f550,f54])).

fof(f54,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f19])).

fof(f19,plain,(
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

fof(f18,plain,(
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
    inference(rectify,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f550,plain,
    ( r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k3_xboole_0(sK0,sK1))
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f549])).

fof(f1304,plain,
    ( spl7_8
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f969,f929,f549])).

fof(f929,plain,
    ( spl7_10
  <=> r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f969,plain,
    ( r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k3_xboole_0(sK0,sK1))
    | ~ spl7_10 ),
    inference(resolution,[],[f931,f55])).

fof(f55,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f931,plain,
    ( r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f929])).

fof(f1303,plain,
    ( spl7_5
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f970,f929,f118])).

fof(f970,plain,
    ( r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),sK2)
    | ~ spl7_10 ),
    inference(resolution,[],[f931,f54])).

% (29766)Refutation not found, incomplete strategy% (29766)------------------------------
% (29766)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (29766)Termination reason: Refutation not found, incomplete strategy

% (29766)Memory used [KB]: 10490
% (29766)Time elapsed: 0.069 s
% (29766)------------------------------
% (29766)------------------------------
fof(f1302,plain,
    ( spl7_4
    | spl7_5
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f272,f84,f118,f114])).

fof(f84,plain,
    ( spl7_3
  <=> r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k5_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f272,plain,
    ( r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),sK2)
    | r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),sK1)
    | ~ spl7_3 ),
    inference(resolution,[],[f85,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f85,plain,
    ( r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k5_xboole_0(sK1,sK2))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f84])).

fof(f1300,plain,
    ( ~ spl7_4
    | ~ spl7_5
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f273,f84,f118,f114])).

fof(f273,plain,
    ( ~ r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),sK2)
    | ~ r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),sK1)
    | ~ spl7_3 ),
    inference(resolution,[],[f85,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1294,plain,
    ( ~ spl7_5
    | spl7_6 ),
    inference(avatar_contradiction_clause,[],[f1281])).

fof(f1281,plain,
    ( $false
    | ~ spl7_5
    | spl7_6 ),
    inference(resolution,[],[f263,f535])).

fof(f535,plain,
    ( ! [X8] : r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k2_xboole_0(X8,sK2))
    | ~ spl7_5 ),
    inference(resolution,[],[f120,f56])).

fof(f56,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f120,plain,
    ( r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),sK2)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f118])).

fof(f1047,plain,
    ( ~ spl7_2
    | ~ spl7_4
    | spl7_8 ),
    inference(avatar_split_clause,[],[f887,f549,f114,f79])).

fof(f79,plain,
    ( spl7_2
  <=> r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f887,plain,
    ( ~ r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),sK1)
    | ~ r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),sK0)
    | spl7_8 ),
    inference(resolution,[],[f551,f53])).

fof(f53,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f551,plain,
    ( ~ r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k3_xboole_0(sK0,sK1))
    | spl7_8 ),
    inference(avatar_component_clause,[],[f549])).

fof(f1033,plain,
    ( spl7_2
    | ~ spl7_9 ),
    inference(avatar_contradiction_clause,[],[f1020])).

fof(f1020,plain,
    ( $false
    | spl7_2
    | ~ spl7_9 ),
    inference(resolution,[],[f927,f907])).

fof(f907,plain,
    ( ! [X5] : ~ r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k4_xboole_0(sK0,X5))
    | spl7_2 ),
    inference(resolution,[],[f80,f52])).

fof(f52,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f80,plain,
    ( ~ r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),sK0)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f79])).

fof(f1019,plain,
    ( spl7_2
    | ~ spl7_8 ),
    inference(avatar_contradiction_clause,[],[f1006])).

fof(f1006,plain,
    ( $false
    | spl7_2
    | ~ spl7_8 ),
    inference(resolution,[],[f550,f909])).

fof(f909,plain,
    ( ! [X7] : ~ r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k3_xboole_0(sK0,X7))
    | spl7_2 ),
    inference(resolution,[],[f80,f55])).

fof(f932,plain,
    ( spl7_9
    | spl7_10
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f913,f75,f929,f925])).

fof(f75,plain,
    ( spl7_1
  <=> r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f913,plain,
    ( r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))
    | r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ spl7_1 ),
    inference(resolution,[],[f77,f58])).

fof(f77,plain,
    ( r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2)))
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f552,plain,
    ( ~ spl7_8
    | ~ spl7_5
    | spl7_1 ),
    inference(avatar_split_clause,[],[f537,f75,f118,f549])).

fof(f537,plain,
    ( ~ r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),sK2)
    | ~ r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k3_xboole_0(sK0,sK1))
    | spl7_1 ),
    inference(resolution,[],[f316,f53])).

fof(f316,plain,
    ( ~ r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))
    | spl7_1 ),
    inference(resolution,[],[f76,f56])).

fof(f76,plain,
    ( ~ r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2)))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f516,plain,
    ( ~ spl7_5
    | spl7_4
    | spl7_3 ),
    inference(avatar_split_clause,[],[f102,f84,f114,f118])).

fof(f102,plain,
    ( r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),sK1)
    | ~ r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),sK2)
    | spl7_3 ),
    inference(resolution,[],[f86,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f86,plain,
    ( ~ r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k5_xboole_0(sK1,sK2))
    | spl7_3 ),
    inference(avatar_component_clause,[],[f84])).

fof(f514,plain,
    ( ~ spl7_4
    | spl7_5
    | spl7_3 ),
    inference(avatar_split_clause,[],[f101,f84,f118,f114])).

fof(f101,plain,
    ( r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),sK2)
    | ~ r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),sK1)
    | spl7_3 ),
    inference(resolution,[],[f86,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f265,plain,
    ( ~ spl7_2
    | spl7_6
    | spl7_1 ),
    inference(avatar_split_clause,[],[f250,f75,f262,f79])).

fof(f250,plain,
    ( r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k2_xboole_0(sK1,sK2))
    | ~ r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),sK0)
    | spl7_1 ),
    inference(resolution,[],[f125,f50])).

fof(f50,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f125,plain,
    ( ~ r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)))
    | spl7_1 ),
    inference(resolution,[],[f76,f57])).

fof(f88,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | spl7_3 ),
    inference(avatar_split_clause,[],[f73,f84,f79,f75])).

fof(f73,plain,
    ( r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k5_xboole_0(sK1,sK2))
    | ~ r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),sK0)
    | ~ r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))) ),
    inference(resolution,[],[f60,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( sQ6_eqProxy(k4_xboole_0(X0,X1),X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f33,f59])).

fof(f59,plain,(
    ! [X1,X0] :
      ( sQ6_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ6_eqProxy])])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f60,plain,(
    ~ sQ6_eqProxy(k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))) ),
    inference(equality_proxy_replacement,[],[f27,f59])).

fof(f27,plain,(
    k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2] : k4_xboole_0(X0,k5_xboole_0(X1,X2)) != k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k3_xboole_0(k3_xboole_0(X0,X1),X2))
   => k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2)) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] : k4_xboole_0(X0,k5_xboole_0(X1,X2)) != k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] : k4_xboole_0(X0,k5_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k5_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_xboole_1)).

fof(f87,plain,
    ( spl7_1
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f72,f84,f75])).

fof(f72,plain,
    ( ~ r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k5_xboole_0(sK1,sK2))
    | r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))) ),
    inference(resolution,[],[f60,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( sQ6_eqProxy(k4_xboole_0(X0,X1),X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f32,f59])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f82,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f71,f79,f75])).

fof(f71,plain,
    ( r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),sK0)
    | r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))) ),
    inference(resolution,[],[f60,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( sQ6_eqProxy(k4_xboole_0(X0,X1),X2)
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f31,f59])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:42:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.43  % (29771)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.46  % (29780)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.46  % (29779)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.47  % (29777)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (29779)Refutation not found, incomplete strategy% (29779)------------------------------
% 0.21/0.47  % (29779)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (29779)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (29779)Memory used [KB]: 10618
% 0.21/0.47  % (29779)Time elapsed: 0.078 s
% 0.21/0.47  % (29779)------------------------------
% 0.21/0.47  % (29779)------------------------------
% 0.21/0.48  % (29780)Refutation not found, incomplete strategy% (29780)------------------------------
% 0.21/0.48  % (29780)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (29780)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (29780)Memory used [KB]: 6140
% 0.21/0.48  % (29780)Time elapsed: 0.066 s
% 0.21/0.48  % (29780)------------------------------
% 0.21/0.48  % (29780)------------------------------
% 0.21/0.50  % (29777)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f1309,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f82,f87,f88,f265,f514,f516,f552,f932,f1019,f1033,f1047,f1294,f1300,f1302,f1303,f1304,f1305,f1306,f1307,f1308])).
% 0.21/0.50  fof(f1308,plain,(
% 0.21/0.50    ~spl7_4 | spl7_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f1282,f262,f114])).
% 0.21/0.50  fof(f114,plain,(
% 0.21/0.50    spl7_4 <=> r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.50  fof(f262,plain,(
% 0.21/0.50    spl7_6 <=> r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k2_xboole_0(sK1,sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.50  fof(f1282,plain,(
% 0.21/0.50    ~r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),sK1) | spl7_6),
% 0.21/0.50    inference(resolution,[],[f263,f57])).
% 0.21/0.50  % (29766)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK5(X0,X1,X2),X1) & ~r2_hidden(sK5(X0,X1,X2),X0)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f23,f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK5(X0,X1,X2),X1) & ~r2_hidden(sK5(X0,X1,X2),X0)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.50    inference(rectify,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.50    inference(flattening,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.50    inference(nnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.21/0.50  fof(f263,plain,(
% 0.21/0.50    ~r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k2_xboole_0(sK1,sK2)) | spl7_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f262])).
% 0.21/0.50  fof(f1307,plain,(
% 0.21/0.50    ~spl7_6 | ~spl7_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f1022,f925,f262])).
% 0.21/0.50  fof(f925,plain,(
% 0.21/0.50    spl7_9 <=> r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.21/0.50  fof(f1022,plain,(
% 0.21/0.50    ~r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k2_xboole_0(sK1,sK2)) | ~spl7_9),
% 0.21/0.50    inference(resolution,[],[f927,f51])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 0.21/0.50    inference(equality_resolution,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.50    inference(rectify,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.50    inference(flattening,[],[f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.50    inference(nnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.21/0.50  fof(f927,plain,(
% 0.21/0.50    r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) | ~spl7_9),
% 0.21/0.50    inference(avatar_component_clause,[],[f925])).
% 0.21/0.50  fof(f1306,plain,(
% 0.21/0.50    spl7_4 | spl7_5 | ~spl7_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f501,f262,f118,f114])).
% 0.21/0.50  fof(f118,plain,(
% 0.21/0.50    spl7_5 <=> r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.50  fof(f501,plain,(
% 0.21/0.50    r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),sK2) | r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),sK1) | ~spl7_6),
% 0.21/0.50    inference(resolution,[],[f264,f58])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k2_xboole_0(X0,X1))) )),
% 0.21/0.50    inference(equality_resolution,[],[f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f264,plain,(
% 0.21/0.50    r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k2_xboole_0(sK1,sK2)) | ~spl7_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f262])).
% 0.21/0.50  fof(f1305,plain,(
% 0.21/0.50    spl7_4 | ~spl7_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f1008,f549,f114])).
% 0.21/0.50  fof(f549,plain,(
% 0.21/0.50    spl7_8 <=> r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k3_xboole_0(sK0,sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.21/0.50  fof(f1008,plain,(
% 0.21/0.50    r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),sK1) | ~spl7_8),
% 0.21/0.50    inference(resolution,[],[f550,f54])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 0.21/0.50    inference(equality_resolution,[],[f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.50    inference(rectify,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.50    inference(flattening,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.50    inference(nnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.21/0.50  fof(f550,plain,(
% 0.21/0.50    r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k3_xboole_0(sK0,sK1)) | ~spl7_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f549])).
% 0.21/0.50  fof(f1304,plain,(
% 0.21/0.50    spl7_8 | ~spl7_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f969,f929,f549])).
% 0.21/0.50  fof(f929,plain,(
% 0.21/0.50    spl7_10 <=> r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.21/0.50  fof(f969,plain,(
% 0.21/0.50    r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k3_xboole_0(sK0,sK1)) | ~spl7_10),
% 0.21/0.50    inference(resolution,[],[f931,f55])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 0.21/0.50    inference(equality_resolution,[],[f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f931,plain,(
% 0.21/0.50    r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2)) | ~spl7_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f929])).
% 0.21/0.50  fof(f1303,plain,(
% 0.21/0.50    spl7_5 | ~spl7_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f970,f929,f118])).
% 0.21/0.50  fof(f970,plain,(
% 0.21/0.50    r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),sK2) | ~spl7_10),
% 0.21/0.50    inference(resolution,[],[f931,f54])).
% 0.21/0.50  % (29766)Refutation not found, incomplete strategy% (29766)------------------------------
% 0.21/0.50  % (29766)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (29766)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (29766)Memory used [KB]: 10490
% 0.21/0.50  % (29766)Time elapsed: 0.069 s
% 0.21/0.50  % (29766)------------------------------
% 0.21/0.50  % (29766)------------------------------
% 0.21/0.50  fof(f1302,plain,(
% 0.21/0.50    spl7_4 | spl7_5 | ~spl7_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f272,f84,f118,f114])).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    spl7_3 <=> r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k5_xboole_0(sK1,sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.50  fof(f272,plain,(
% 0.21/0.50    r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),sK2) | r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),sK1) | ~spl7_3),
% 0.21/0.50    inference(resolution,[],[f85,f46])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 0.21/0.50    inference(nnf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k5_xboole_0(sK1,sK2)) | ~spl7_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f84])).
% 0.21/0.50  fof(f1300,plain,(
% 0.21/0.50    ~spl7_4 | ~spl7_5 | ~spl7_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f273,f84,f118,f114])).
% 0.21/0.50  fof(f273,plain,(
% 0.21/0.50    ~r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),sK2) | ~r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),sK1) | ~spl7_3),
% 0.21/0.50    inference(resolution,[],[f85,f47])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f1294,plain,(
% 0.21/0.50    ~spl7_5 | spl7_6),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f1281])).
% 0.21/0.50  fof(f1281,plain,(
% 0.21/0.50    $false | (~spl7_5 | spl7_6)),
% 0.21/0.50    inference(resolution,[],[f263,f535])).
% 0.21/0.50  fof(f535,plain,(
% 0.21/0.50    ( ! [X8] : (r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k2_xboole_0(X8,sK2))) ) | ~spl7_5),
% 0.21/0.50    inference(resolution,[],[f120,f56])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 0.21/0.50    inference(equality_resolution,[],[f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f120,plain,(
% 0.21/0.50    r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),sK2) | ~spl7_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f118])).
% 0.21/0.50  fof(f1047,plain,(
% 0.21/0.50    ~spl7_2 | ~spl7_4 | spl7_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f887,f549,f114,f79])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    spl7_2 <=> r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.50  fof(f887,plain,(
% 0.21/0.50    ~r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),sK1) | ~r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),sK0) | spl7_8),
% 0.21/0.50    inference(resolution,[],[f551,f53])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_xboole_0(X0,X1)) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f551,plain,(
% 0.21/0.50    ~r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k3_xboole_0(sK0,sK1)) | spl7_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f549])).
% 0.21/0.50  fof(f1033,plain,(
% 0.21/0.50    spl7_2 | ~spl7_9),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f1020])).
% 0.21/0.50  fof(f1020,plain,(
% 0.21/0.50    $false | (spl7_2 | ~spl7_9)),
% 0.21/0.50    inference(resolution,[],[f927,f907])).
% 0.21/0.50  fof(f907,plain,(
% 0.21/0.50    ( ! [X5] : (~r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k4_xboole_0(sK0,X5))) ) | spl7_2),
% 0.21/0.50    inference(resolution,[],[f80,f52])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 0.21/0.50    inference(equality_resolution,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    ~r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),sK0) | spl7_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f79])).
% 0.21/0.50  fof(f1019,plain,(
% 0.21/0.50    spl7_2 | ~spl7_8),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f1006])).
% 0.21/0.50  fof(f1006,plain,(
% 0.21/0.50    $false | (spl7_2 | ~spl7_8)),
% 0.21/0.50    inference(resolution,[],[f550,f909])).
% 0.21/0.50  fof(f909,plain,(
% 0.21/0.50    ( ! [X7] : (~r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k3_xboole_0(sK0,X7))) ) | spl7_2),
% 0.21/0.50    inference(resolution,[],[f80,f55])).
% 0.21/0.50  fof(f932,plain,(
% 0.21/0.50    spl7_9 | spl7_10 | ~spl7_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f913,f75,f929,f925])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    spl7_1 <=> r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.50  fof(f913,plain,(
% 0.21/0.50    r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2)) | r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) | ~spl7_1),
% 0.21/0.50    inference(resolution,[],[f77,f58])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))) | ~spl7_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f75])).
% 0.21/0.50  fof(f552,plain,(
% 0.21/0.50    ~spl7_8 | ~spl7_5 | spl7_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f537,f75,f118,f549])).
% 0.21/0.50  fof(f537,plain,(
% 0.21/0.50    ~r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),sK2) | ~r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k3_xboole_0(sK0,sK1)) | spl7_1),
% 0.21/0.50    inference(resolution,[],[f316,f53])).
% 0.21/0.50  fof(f316,plain,(
% 0.21/0.50    ~r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2)) | spl7_1),
% 0.21/0.50    inference(resolution,[],[f76,f56])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    ~r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))) | spl7_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f75])).
% 0.21/0.50  fof(f516,plain,(
% 0.21/0.50    ~spl7_5 | spl7_4 | spl7_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f102,f84,f114,f118])).
% 0.21/0.50  fof(f102,plain,(
% 0.21/0.50    r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),sK1) | ~r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),sK2) | spl7_3),
% 0.21/0.50    inference(resolution,[],[f86,f49])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    ~r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k5_xboole_0(sK1,sK2)) | spl7_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f84])).
% 0.21/0.50  fof(f514,plain,(
% 0.21/0.50    ~spl7_4 | spl7_5 | spl7_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f101,f84,f118,f114])).
% 0.21/0.50  fof(f101,plain,(
% 0.21/0.50    r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),sK2) | ~r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),sK1) | spl7_3),
% 0.21/0.50    inference(resolution,[],[f86,f48])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f265,plain,(
% 0.21/0.50    ~spl7_2 | spl7_6 | spl7_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f250,f75,f262,f79])).
% 0.21/0.50  fof(f250,plain,(
% 0.21/0.50    r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k2_xboole_0(sK1,sK2)) | ~r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),sK0) | spl7_1),
% 0.21/0.50    inference(resolution,[],[f125,f50])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f125,plain,(
% 0.21/0.50    ~r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) | spl7_1),
% 0.21/0.50    inference(resolution,[],[f76,f57])).
% 0.21/0.50  fof(f88,plain,(
% 0.21/0.50    ~spl7_1 | ~spl7_2 | spl7_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f73,f84,f79,f75])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k5_xboole_0(sK1,sK2)) | ~r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),sK0) | ~r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2)))),
% 0.21/0.50    inference(resolution,[],[f60,f61])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (sQ6_eqProxy(k4_xboole_0(X0,X1),X2) | r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) )),
% 0.21/0.50    inference(equality_proxy_replacement,[],[f33,f59])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    ! [X1,X0] : (sQ6_eqProxy(X0,X1) <=> X0 = X1)),
% 0.21/0.50    introduced(equality_proxy_definition,[new_symbols(naming,[sQ6_eqProxy])])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ~sQ6_eqProxy(k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2)))),
% 0.21/0.50    inference(equality_proxy_replacement,[],[f27,f59])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f9])).
% 0.21/0.50  fof(f9,plain,(
% 0.21/0.50    ? [X0,X1,X2] : k4_xboole_0(X0,k5_xboole_0(X1,X2)) != k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k3_xboole_0(k3_xboole_0(X0,X1),X2)) => k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f7,plain,(
% 0.21/0.50    ? [X0,X1,X2] : k4_xboole_0(X0,k5_xboole_0(X1,X2)) != k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k3_xboole_0(k3_xboole_0(X0,X1),X2))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2] : k4_xboole_0(X0,k5_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k3_xboole_0(k3_xboole_0(X0,X1),X2))),
% 0.21/0.50    inference(negated_conjecture,[],[f5])).
% 0.21/0.50  fof(f5,conjecture,(
% 0.21/0.50    ! [X0,X1,X2] : k4_xboole_0(X0,k5_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k3_xboole_0(k3_xboole_0(X0,X1),X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_xboole_1)).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    spl7_1 | ~spl7_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f72,f84,f75])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    ~r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k5_xboole_0(sK1,sK2)) | r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2)))),
% 0.21/0.50    inference(resolution,[],[f60,f62])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (sQ6_eqProxy(k4_xboole_0(X0,X1),X2) | ~r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 0.21/0.50    inference(equality_proxy_replacement,[],[f32,f59])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    spl7_1 | spl7_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f71,f79,f75])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),sK0) | r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))),k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2)))),
% 0.21/0.50    inference(resolution,[],[f60,f63])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (sQ6_eqProxy(k4_xboole_0(X0,X1),X2) | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 0.21/0.50    inference(equality_proxy_replacement,[],[f31,f59])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (29777)------------------------------
% 0.21/0.50  % (29777)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (29777)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (29777)Memory used [KB]: 6780
% 0.21/0.50  % (29777)Time elapsed: 0.063 s
% 0.21/0.50  % (29777)------------------------------
% 0.21/0.50  % (29777)------------------------------
% 0.21/0.50  % (29764)Success in time 0.142 s
%------------------------------------------------------------------------------
