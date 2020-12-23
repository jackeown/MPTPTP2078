%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0060+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:16 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 224 expanded)
%              Number of leaves         :   16 (  83 expanded)
%              Depth                    :   10
%              Number of atoms          :  399 (1307 expanded)
%              Number of equality atoms :   47 ( 167 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f299,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f75,f80,f81,f115,f162,f182,f207,f208,f211,f233,f234,f296,f297,f298])).

fof(f298,plain,
    ( ~ spl7_6
    | spl7_3 ),
    inference(avatar_split_clause,[],[f90,f77,f159])).

fof(f159,plain,
    ( spl7_6
  <=> r2_hidden(sK5(sK0,k2_xboole_0(sK1,sK2),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f77,plain,
    ( spl7_3
  <=> r2_hidden(sK5(sK0,k2_xboole_0(sK1,sK2),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f90,plain,
    ( ~ r2_hidden(sK5(sK0,k2_xboole_0(sK1,sK2),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),sK1)
    | spl7_3 ),
    inference(resolution,[],[f79,f47])).

fof(f47,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f16,f17])).

fof(f17,plain,(
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

fof(f16,plain,(
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
    inference(rectify,[],[f15])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f14])).

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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f79,plain,
    ( ~ r2_hidden(sK5(sK0,k2_xboole_0(sK1,sK2),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),k2_xboole_0(sK1,sK2))
    | spl7_3 ),
    inference(avatar_component_clause,[],[f77])).

fof(f297,plain,
    ( spl7_6
    | spl7_7
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f242,f77,f179,f159])).

fof(f179,plain,
    ( spl7_7
  <=> r2_hidden(sK5(sK0,k2_xboole_0(sK1,sK2),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f242,plain,
    ( r2_hidden(sK5(sK0,k2_xboole_0(sK1,sK2),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),sK2)
    | r2_hidden(sK5(sK0,k2_xboole_0(sK1,sK2),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),sK1)
    | ~ spl7_3 ),
    inference(resolution,[],[f78,f48])).

fof(f48,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f78,plain,
    ( r2_hidden(sK5(sK0,k2_xboole_0(sK1,sK2),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),k2_xboole_0(sK1,sK2))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f77])).

fof(f296,plain,
    ( ~ spl7_7
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f289,f112,f179])).

fof(f112,plain,
    ( spl7_5
  <=> r2_hidden(sK5(sK0,k2_xboole_0(sK1,sK2),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f289,plain,
    ( ~ r2_hidden(sK5(sK0,k2_xboole_0(sK1,sK2),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),sK2)
    | ~ spl7_5 ),
    inference(resolution,[],[f113,f50])).

fof(f50,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f21,f22])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(sK5(X0,X1,X2),X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f113,plain,
    ( r2_hidden(sK5(sK0,k2_xboole_0(sK1,sK2),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),k4_xboole_0(sK0,sK2))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f112])).

fof(f234,plain,
    ( ~ spl7_6
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f164,f108,f159])).

fof(f108,plain,
    ( spl7_4
  <=> r2_hidden(sK5(sK0,k2_xboole_0(sK1,sK2),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f164,plain,
    ( ~ r2_hidden(sK5(sK0,k2_xboole_0(sK1,sK2),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),sK1)
    | ~ spl7_4 ),
    inference(resolution,[],[f109,f50])).

fof(f109,plain,
    ( r2_hidden(sK5(sK0,k2_xboole_0(sK1,sK2),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),k4_xboole_0(sK0,sK1))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f108])).

fof(f233,plain,
    ( spl7_3
    | ~ spl7_7 ),
    inference(avatar_contradiction_clause,[],[f226])).

fof(f226,plain,
    ( $false
    | spl7_3
    | ~ spl7_7 ),
    inference(resolution,[],[f181,f91])).

fof(f91,plain,
    ( ~ r2_hidden(sK5(sK0,k2_xboole_0(sK1,sK2),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),sK2)
    | spl7_3 ),
    inference(resolution,[],[f79,f46])).

fof(f46,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f181,plain,
    ( r2_hidden(sK5(sK0,k2_xboole_0(sK1,sK2),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),sK2)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f179])).

fof(f211,plain,
    ( spl7_2
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f163,f108,f72])).

fof(f72,plain,
    ( spl7_2
  <=> r2_hidden(sK5(sK0,k2_xboole_0(sK1,sK2),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f163,plain,
    ( r2_hidden(sK5(sK0,k2_xboole_0(sK1,sK2),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),sK0)
    | ~ spl7_4 ),
    inference(resolution,[],[f109,f51])).

fof(f51,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f208,plain,
    ( spl7_5
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f200,f68,f112])).

fof(f68,plain,
    ( spl7_1
  <=> r2_hidden(sK5(sK0,k2_xboole_0(sK1,sK2),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f200,plain,
    ( r2_hidden(sK5(sK0,k2_xboole_0(sK1,sK2),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),k4_xboole_0(sK0,sK2))
    | ~ spl7_1 ),
    inference(resolution,[],[f70,f44])).

fof(f44,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f11,f12])).

fof(f12,plain,(
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

fof(f11,plain,(
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
    inference(rectify,[],[f10])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f9])).

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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f70,plain,
    ( r2_hidden(sK5(sK0,k2_xboole_0(sK1,sK2),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)))
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f68])).

fof(f207,plain,
    ( spl7_4
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f199,f68,f108])).

fof(f199,plain,
    ( r2_hidden(sK5(sK0,k2_xboole_0(sK1,sK2),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),k4_xboole_0(sK0,sK1))
    | ~ spl7_1 ),
    inference(resolution,[],[f70,f45])).

fof(f45,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f182,plain,
    ( ~ spl7_2
    | spl7_7
    | spl7_5 ),
    inference(avatar_split_clause,[],[f171,f112,f179,f72])).

fof(f171,plain,
    ( r2_hidden(sK5(sK0,k2_xboole_0(sK1,sK2),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),sK2)
    | ~ r2_hidden(sK5(sK0,k2_xboole_0(sK1,sK2),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),sK0)
    | spl7_5 ),
    inference(resolution,[],[f114,f49])).

fof(f49,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f114,plain,
    ( ~ r2_hidden(sK5(sK0,k2_xboole_0(sK1,sK2),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),k4_xboole_0(sK0,sK2))
    | spl7_5 ),
    inference(avatar_component_clause,[],[f112])).

fof(f162,plain,
    ( ~ spl7_2
    | spl7_6
    | spl7_4 ),
    inference(avatar_split_clause,[],[f151,f108,f159,f72])).

fof(f151,plain,
    ( r2_hidden(sK5(sK0,k2_xboole_0(sK1,sK2),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),sK1)
    | ~ r2_hidden(sK5(sK0,k2_xboole_0(sK1,sK2),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),sK0)
    | spl7_4 ),
    inference(resolution,[],[f110,f49])).

fof(f110,plain,
    ( ~ r2_hidden(sK5(sK0,k2_xboole_0(sK1,sK2),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),k4_xboole_0(sK0,sK1))
    | spl7_4 ),
    inference(avatar_component_clause,[],[f108])).

fof(f115,plain,
    ( ~ spl7_4
    | ~ spl7_5
    | spl7_1 ),
    inference(avatar_split_clause,[],[f100,f68,f112,f108])).

fof(f100,plain,
    ( ~ r2_hidden(sK5(sK0,k2_xboole_0(sK1,sK2),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),k4_xboole_0(sK0,sK2))
    | ~ r2_hidden(sK5(sK0,k2_xboole_0(sK1,sK2),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),k4_xboole_0(sK0,sK1))
    | spl7_1 ),
    inference(resolution,[],[f69,f43])).

fof(f43,plain,(
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
    inference(cnf_transformation,[],[f13])).

fof(f69,plain,
    ( ~ r2_hidden(sK5(sK0,k2_xboole_0(sK1,sK2),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f68])).

fof(f81,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | spl7_3 ),
    inference(avatar_split_clause,[],[f66,f77,f72,f68])).

fof(f66,plain,
    ( r2_hidden(sK5(sK0,k2_xboole_0(sK1,sK2),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),k2_xboole_0(sK1,sK2))
    | ~ r2_hidden(sK5(sK0,k2_xboole_0(sK1,sK2),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),sK0)
    | ~ r2_hidden(sK5(sK0,k2_xboole_0(sK1,sK2),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))) ),
    inference(resolution,[],[f53,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( sQ6_eqProxy(k4_xboole_0(X0,X1),X2)
      | r2_hidden(sK5(X0,X1,X2),X1)
      | ~ r2_hidden(sK5(X0,X1,X2),X0)
      | ~ r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f42,f52])).

fof(f52,plain,(
    ! [X1,X0] :
      ( sQ6_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ6_eqProxy])])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK5(X0,X1,X2),X1)
      | ~ r2_hidden(sK5(X0,X1,X2),X0)
      | ~ r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f53,plain,(
    ~ sQ6_eqProxy(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))) ),
    inference(equality_proxy_replacement,[],[f24,f52])).

fof(f24,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f7])).

fof(f7,plain,
    ( ? [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))
   => k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_xboole_1)).

fof(f80,plain,
    ( spl7_1
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f65,f77,f68])).

fof(f65,plain,
    ( ~ r2_hidden(sK5(sK0,k2_xboole_0(sK1,sK2),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),k2_xboole_0(sK1,sK2))
    | r2_hidden(sK5(sK0,k2_xboole_0(sK1,sK2),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))) ),
    inference(resolution,[],[f53,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( sQ6_eqProxy(k4_xboole_0(X0,X1),X2)
      | ~ r2_hidden(sK5(X0,X1,X2),X1)
      | r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f41,f52])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK5(X0,X1,X2),X1)
      | r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f75,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f64,f72,f68])).

fof(f64,plain,
    ( r2_hidden(sK5(sK0,k2_xboole_0(sK1,sK2),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),sK0)
    | r2_hidden(sK5(sK0,k2_xboole_0(sK1,sK2),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))) ),
    inference(resolution,[],[f53,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( sQ6_eqProxy(k4_xboole_0(X0,X1),X2)
      | r2_hidden(sK5(X0,X1,X2),X0)
      | r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f40,f52])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK5(X0,X1,X2),X0)
      | r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f23])).

%------------------------------------------------------------------------------
