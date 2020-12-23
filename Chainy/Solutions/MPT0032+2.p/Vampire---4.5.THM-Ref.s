%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0032+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:04 EST 2020

% Result     : Theorem 14.75s
% Output     : Refutation 14.75s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 495 expanded)
%              Number of leaves         :   24 ( 174 expanded)
%              Depth                    :   11
%              Number of atoms          :  513 (2878 expanded)
%              Number of equality atoms :   35 ( 327 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17799,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f6333,f11216,f13264,f15192,f15301,f15306,f15315,f15321,f15353,f15355,f15373,f15434,f15454,f15455,f15459,f15517,f15656,f15800,f16556,f16564,f16574,f16580,f16587,f16589,f16611,f16630,f16633,f16713,f17796])).

fof(f17796,plain,
    ( spl19_36
    | spl19_87
    | ~ spl19_291 ),
    inference(avatar_contradiction_clause,[],[f17795])).

fof(f17795,plain,
    ( $false
    | spl19_36
    | spl19_87
    | ~ spl19_291 ),
    inference(subsumption_resolution,[],[f17794,f1410])).

fof(f1410,plain,
    ( ~ r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK1)
    | spl19_87 ),
    inference(avatar_component_clause,[],[f1408])).

fof(f1408,plain,
    ( spl19_87
  <=> r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_87])])).

fof(f17794,plain,
    ( r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK1)
    | spl19_36
    | ~ spl19_291 ),
    inference(subsumption_resolution,[],[f17774,f625])).

fof(f625,plain,
    ( ~ r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK2)
    | spl19_36 ),
    inference(avatar_component_clause,[],[f623])).

fof(f623,plain,
    ( spl19_36
  <=> r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_36])])).

fof(f17774,plain,
    ( r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK2)
    | r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK1)
    | ~ spl19_291 ),
    inference(resolution,[],[f6752,f283])).

fof(f283,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f255])).

fof(f255,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f161])).

fof(f161,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK15(X0,X1,X2),X1)
              & ~ r2_hidden(sK15(X0,X1,X2),X0) )
            | ~ r2_hidden(sK15(X0,X1,X2),X2) )
          & ( r2_hidden(sK15(X0,X1,X2),X1)
            | r2_hidden(sK15(X0,X1,X2),X0)
            | r2_hidden(sK15(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f159,f160])).

fof(f160,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK15(X0,X1,X2),X1)
            & ~ r2_hidden(sK15(X0,X1,X2),X0) )
          | ~ r2_hidden(sK15(X0,X1,X2),X2) )
        & ( r2_hidden(sK15(X0,X1,X2),X1)
          | r2_hidden(sK15(X0,X1,X2),X0)
          | r2_hidden(sK15(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f159,plain,(
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
    inference(rectify,[],[f158])).

fof(f158,plain,(
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
    inference(flattening,[],[f157])).

fof(f157,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f6752,plain,
    ( r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k2_xboole_0(sK1,sK2))
    | ~ spl19_291 ),
    inference(avatar_component_clause,[],[f6751])).

fof(f6751,plain,
    ( spl19_291
  <=> r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_291])])).

fof(f16713,plain,
    ( ~ spl19_87
    | spl19_34
    | ~ spl19_37 ),
    inference(avatar_split_clause,[],[f16712,f627,f596,f1408])).

fof(f596,plain,
    ( spl19_34
  <=> r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_34])])).

fof(f627,plain,
    ( spl19_37
  <=> r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_37])])).

fof(f16712,plain,
    ( ~ r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK1)
    | spl19_34
    | ~ spl19_37 ),
    inference(subsumption_resolution,[],[f16698,f628])).

fof(f628,plain,
    ( r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK0)
    | ~ spl19_37 ),
    inference(avatar_component_clause,[],[f627])).

fof(f16698,plain,
    ( ~ r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK1)
    | ~ r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK0)
    | spl19_34 ),
    inference(resolution,[],[f597,f278])).

fof(f278,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f251])).

fof(f251,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f156])).

fof(f156,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK14(X0,X1,X2),X1)
            | ~ r2_hidden(sK14(X0,X1,X2),X0)
            | ~ r2_hidden(sK14(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK14(X0,X1,X2),X1)
              & r2_hidden(sK14(X0,X1,X2),X0) )
            | r2_hidden(sK14(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f154,f155])).

fof(f155,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK14(X0,X1,X2),X1)
          | ~ r2_hidden(sK14(X0,X1,X2),X0)
          | ~ r2_hidden(sK14(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK14(X0,X1,X2),X1)
            & r2_hidden(sK14(X0,X1,X2),X0) )
          | r2_hidden(sK14(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f154,plain,(
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
    inference(rectify,[],[f153])).

fof(f153,plain,(
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
    inference(flattening,[],[f152])).

fof(f152,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f597,plain,
    ( ~ r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(sK0,sK1))
    | spl19_34 ),
    inference(avatar_component_clause,[],[f596])).

fof(f16633,plain,
    ( spl19_1
    | spl19_2
    | spl19_3 ),
    inference(avatar_split_clause,[],[f16632,f360,f356,f352])).

fof(f352,plain,
    ( spl19_1
  <=> r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_1])])).

fof(f356,plain,
    ( spl19_2
  <=> r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_2])])).

fof(f360,plain,
    ( spl19_3
  <=> r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_3])])).

fof(f16632,plain,
    ( r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0)))
    | spl19_2
    | spl19_3 ),
    inference(subsumption_resolution,[],[f16631,f361])).

fof(f361,plain,
    ( ~ r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(sK2,sK0))
    | spl19_3 ),
    inference(avatar_component_clause,[],[f360])).

fof(f16631,plain,
    ( r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(sK2,sK0))
    | r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0)))
    | spl19_2 ),
    inference(subsumption_resolution,[],[f16616,f287])).

fof(f287,plain,(
    ~ sQ18_eqProxy(k2_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0)),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))) ),
    inference(equality_proxy_replacement,[],[f167,f284])).

fof(f284,plain,(
    ! [X1,X0] :
      ( sQ18_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ18_eqProxy])])).

fof(f167,plain,(
    k2_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0)) != k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0)) ),
    inference(cnf_transformation,[],[f115])).

fof(f115,plain,(
    k2_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0)) != k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f76,f114])).

fof(f114,plain,
    ( ? [X0,X1,X2] : k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) != k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0))
   => k2_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0)) != k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0)) ),
    introduced(choice_axiom,[])).

fof(f76,plain,(
    ? [X0,X1,X2] : k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) != k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0)) ),
    inference(ennf_transformation,[],[f58])).

fof(f58,negated_conjecture,(
    ~ ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) = k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0)) ),
    inference(negated_conjecture,[],[f57])).

fof(f57,conjecture,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) = k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_xboole_1)).

fof(f16616,plain,
    ( sQ18_eqProxy(k2_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0)),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0)))
    | r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(sK2,sK0))
    | r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0)))
    | spl19_2 ),
    inference(resolution,[],[f357,f334])).

fof(f334,plain,(
    ! [X2,X0,X1] :
      ( sQ18_eqProxy(k2_xboole_0(X0,X1),X2)
      | r2_hidden(sK15(X0,X1,X2),X1)
      | r2_hidden(sK15(X0,X1,X2),X0)
      | r2_hidden(sK15(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f258,f284])).

fof(f258,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK15(X0,X1,X2),X1)
      | r2_hidden(sK15(X0,X1,X2),X0)
      | r2_hidden(sK15(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f161])).

fof(f357,plain,
    ( ~ r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)))
    | spl19_2 ),
    inference(avatar_component_clause,[],[f356])).

fof(f16630,plain,
    ( ~ spl19_34
    | spl19_2 ),
    inference(avatar_split_clause,[],[f16614,f356,f596])).

fof(f16614,plain,
    ( ~ r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(sK0,sK1))
    | spl19_2 ),
    inference(resolution,[],[f357,f282])).

fof(f282,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f256])).

fof(f256,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f161])).

fof(f16611,plain,
    ( ~ spl19_36
    | ~ spl19_37
    | spl19_3 ),
    inference(avatar_split_clause,[],[f16596,f360,f627,f623])).

fof(f16596,plain,
    ( ~ r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK0)
    | ~ r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK2)
    | spl19_3 ),
    inference(resolution,[],[f361,f278])).

fof(f16589,plain,
    ( spl19_36
    | ~ spl19_1
    | spl19_37 ),
    inference(avatar_split_clause,[],[f1463,f627,f352,f623])).

fof(f1463,plain,
    ( r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK2)
    | ~ spl19_1
    | spl19_37 ),
    inference(subsumption_resolution,[],[f1441,f629])).

fof(f629,plain,
    ( ~ r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK0)
    | spl19_37 ),
    inference(avatar_component_clause,[],[f627])).

fof(f1441,plain,
    ( r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK0)
    | r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK2)
    | ~ spl19_1 ),
    inference(resolution,[],[f684,f283])).

fof(f684,plain,
    ( r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k2_xboole_0(sK2,sK0))
    | ~ spl19_1 ),
    inference(resolution,[],[f354,f279])).

fof(f279,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f250])).

fof(f250,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f156])).

fof(f354,plain,
    ( r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0)))
    | ~ spl19_1 ),
    inference(avatar_component_clause,[],[f352])).

fof(f16587,plain,
    ( spl19_291
    | ~ spl19_1 ),
    inference(avatar_split_clause,[],[f2028,f352,f6751])).

fof(f2028,plain,
    ( r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k2_xboole_0(sK1,sK2))
    | ~ spl19_1 ),
    inference(resolution,[],[f683,f279])).

fof(f683,plain,
    ( r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)))
    | ~ spl19_1 ),
    inference(resolution,[],[f354,f280])).

fof(f280,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f249])).

fof(f249,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f156])).

fof(f16580,plain,
    ( ~ spl19_87
    | spl19_35
    | ~ spl19_36 ),
    inference(avatar_split_clause,[],[f11356,f623,f600,f1408])).

fof(f600,plain,
    ( spl19_35
  <=> r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_35])])).

fof(f11356,plain,
    ( ~ r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK1)
    | spl19_35
    | ~ spl19_36 ),
    inference(subsumption_resolution,[],[f11342,f624])).

fof(f624,plain,
    ( r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK2)
    | ~ spl19_36 ),
    inference(avatar_component_clause,[],[f623])).

fof(f11342,plain,
    ( ~ r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK2)
    | ~ r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK1)
    | spl19_35 ),
    inference(resolution,[],[f601,f278])).

fof(f601,plain,
    ( ~ r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(sK1,sK2))
    | spl19_35 ),
    inference(avatar_component_clause,[],[f600])).

fof(f16574,plain,
    ( spl19_37
    | spl19_87
    | ~ spl19_290 ),
    inference(avatar_split_clause,[],[f16508,f6747,f1408,f627])).

fof(f6747,plain,
    ( spl19_290
  <=> r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_290])])).

fof(f16508,plain,
    ( r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK1)
    | r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK0)
    | ~ spl19_290 ),
    inference(resolution,[],[f6748,f283])).

fof(f6748,plain,
    ( r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k2_xboole_0(sK0,sK1))
    | ~ spl19_290 ),
    inference(avatar_component_clause,[],[f6747])).

fof(f16564,plain,
    ( ~ spl19_3
    | spl19_36 ),
    inference(avatar_contradiction_clause,[],[f16563])).

fof(f16563,plain,
    ( $false
    | ~ spl19_3
    | spl19_36 ),
    inference(subsumption_resolution,[],[f6308,f625])).

fof(f6308,plain,
    ( r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK2)
    | ~ spl19_3 ),
    inference(resolution,[],[f362,f280])).

fof(f362,plain,
    ( r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(sK2,sK0))
    | ~ spl19_3 ),
    inference(avatar_component_clause,[],[f360])).

fof(f16556,plain,
    ( ~ spl19_87
    | spl19_291 ),
    inference(avatar_split_clause,[],[f16530,f6751,f1408])).

fof(f16530,plain,
    ( ~ r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK1)
    | spl19_291 ),
    inference(resolution,[],[f6753,f282])).

fof(f6753,plain,
    ( ~ r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k2_xboole_0(sK1,sK2))
    | spl19_291 ),
    inference(avatar_component_clause,[],[f6751])).

fof(f15800,plain,
    ( spl19_290
    | ~ spl19_2
    | ~ spl19_56 ),
    inference(avatar_split_clause,[],[f15783,f913,f356,f6747])).

fof(f913,plain,
    ( spl19_56
  <=> r1_tarski(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_56])])).

fof(f15783,plain,
    ( r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k2_xboole_0(sK0,sK1))
    | ~ spl19_2
    | ~ spl19_56 ),
    inference(resolution,[],[f15336,f914])).

fof(f914,plain,
    ( r1_tarski(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k2_xboole_0(sK0,sK1))
    | ~ spl19_56 ),
    inference(avatar_component_clause,[],[f913])).

fof(f15336,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),X2)
        | r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),X2) )
    | ~ spl19_2 ),
    inference(resolution,[],[f358,f214])).

fof(f214,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f137])).

fof(f137,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK8(X0,X1),X1)
          & r2_hidden(sK8(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f135,f136])).

fof(f136,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK8(X0,X1),X1)
        & r2_hidden(sK8(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f135,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f134])).

fof(f134,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f358,plain,
    ( r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)))
    | ~ spl19_2 ),
    inference(avatar_component_clause,[],[f356])).

fof(f15656,plain,
    ( ~ spl19_290
    | ~ spl19_291
    | spl19_288 ),
    inference(avatar_split_clause,[],[f15642,f6355,f6751,f6747])).

fof(f6355,plain,
    ( spl19_288
  <=> r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_288])])).

fof(f15642,plain,
    ( ~ r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k2_xboole_0(sK1,sK2))
    | ~ r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k2_xboole_0(sK0,sK1))
    | spl19_288 ),
    inference(resolution,[],[f6357,f278])).

fof(f6357,plain,
    ( ~ r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)))
    | spl19_288 ),
    inference(avatar_component_clause,[],[f6355])).

fof(f15517,plain,
    ( spl19_87
    | ~ spl19_34 ),
    inference(avatar_split_clause,[],[f15496,f596,f1408])).

fof(f15496,plain,
    ( r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK1)
    | ~ spl19_34 ),
    inference(resolution,[],[f598,f279])).

fof(f598,plain,
    ( r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(sK0,sK1))
    | ~ spl19_34 ),
    inference(avatar_component_clause,[],[f596])).

fof(f15459,plain,
    ( spl19_37
    | ~ spl19_34 ),
    inference(avatar_split_clause,[],[f15264,f596,f627])).

fof(f15264,plain,
    ( r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK0)
    | ~ spl19_34 ),
    inference(resolution,[],[f598,f280])).

fof(f15455,plain,
    ( ~ spl19_37
    | spl19_289 ),
    inference(avatar_split_clause,[],[f15438,f6359,f627])).

fof(f6359,plain,
    ( spl19_289
  <=> r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k2_xboole_0(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_289])])).

fof(f15438,plain,
    ( ~ r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK0)
    | spl19_289 ),
    inference(resolution,[],[f6361,f281])).

fof(f281,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f257])).

fof(f257,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f161])).

fof(f6361,plain,
    ( ~ r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k2_xboole_0(sK2,sK0))
    | spl19_289 ),
    inference(avatar_component_clause,[],[f6359])).

fof(f15454,plain,
    ( ~ spl19_36
    | spl19_289 ),
    inference(avatar_split_clause,[],[f15437,f6359,f623])).

fof(f15437,plain,
    ( ~ r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK2)
    | spl19_289 ),
    inference(resolution,[],[f6361,f282])).

fof(f15434,plain,
    ( spl19_87
    | ~ spl19_35 ),
    inference(avatar_split_clause,[],[f15412,f600,f1408])).

fof(f15412,plain,
    ( r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK1)
    | ~ spl19_35 ),
    inference(resolution,[],[f602,f280])).

fof(f602,plain,
    ( r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(sK1,sK2))
    | ~ spl19_35 ),
    inference(avatar_component_clause,[],[f600])).

fof(f15373,plain,
    ( ~ spl19_288
    | ~ spl19_289
    | spl19_1 ),
    inference(avatar_split_clause,[],[f15358,f352,f6359,f6355])).

fof(f15358,plain,
    ( ~ r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k2_xboole_0(sK2,sK0))
    | ~ r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)))
    | spl19_1 ),
    inference(resolution,[],[f353,f278])).

fof(f353,plain,
    ( ~ r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0)))
    | spl19_1 ),
    inference(avatar_component_clause,[],[f352])).

fof(f15355,plain,
    ( spl19_34
    | spl19_35
    | ~ spl19_2 ),
    inference(avatar_split_clause,[],[f15330,f356,f600,f596])).

fof(f15330,plain,
    ( r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(sK1,sK2))
    | r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(sK0,sK1))
    | ~ spl19_2 ),
    inference(resolution,[],[f358,f283])).

fof(f15353,plain,
    ( ~ spl19_1
    | ~ spl19_2 ),
    inference(avatar_split_clause,[],[f15352,f356,f352])).

fof(f15352,plain,
    ( ~ r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0)))
    | ~ spl19_2 ),
    inference(subsumption_resolution,[],[f15327,f287])).

fof(f15327,plain,
    ( sQ18_eqProxy(k2_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0)),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0)))
    | ~ r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0)))
    | ~ spl19_2 ),
    inference(resolution,[],[f358,f333])).

fof(f333,plain,(
    ! [X2,X0,X1] :
      ( sQ18_eqProxy(k2_xboole_0(X0,X1),X2)
      | ~ r2_hidden(sK15(X0,X1,X2),X0)
      | ~ r2_hidden(sK15(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f259,f284])).

fof(f259,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK15(X0,X1,X2),X0)
      | ~ r2_hidden(sK15(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f161])).

fof(f15321,plain,
    ( spl19_36
    | ~ spl19_35 ),
    inference(avatar_split_clause,[],[f6627,f600,f623])).

fof(f6627,plain,
    ( r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK2)
    | ~ spl19_35 ),
    inference(resolution,[],[f602,f279])).

fof(f15315,plain,
    ( ~ spl19_36
    | spl19_291 ),
    inference(avatar_contradiction_clause,[],[f15314])).

fof(f15314,plain,
    ( $false
    | ~ spl19_36
    | spl19_291 ),
    inference(subsumption_resolution,[],[f6753,f1492])).

fof(f1492,plain,
    ( ! [X13] : r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k2_xboole_0(X13,sK2))
    | ~ spl19_36 ),
    inference(resolution,[],[f624,f281])).

fof(f15306,plain,
    ( ~ spl19_1
    | spl19_290 ),
    inference(avatar_contradiction_clause,[],[f15305])).

fof(f15305,plain,
    ( $false
    | ~ spl19_1
    | spl19_290 ),
    inference(subsumption_resolution,[],[f2027,f6749])).

fof(f6749,plain,
    ( ~ r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k2_xboole_0(sK0,sK1))
    | spl19_290 ),
    inference(avatar_component_clause,[],[f6747])).

fof(f2027,plain,
    ( r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k2_xboole_0(sK0,sK1))
    | ~ spl19_1 ),
    inference(resolution,[],[f683,f280])).

fof(f15301,plain,
    ( ~ spl19_35
    | spl19_2 ),
    inference(avatar_split_clause,[],[f661,f356,f600])).

fof(f661,plain,
    ( ~ r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(sK1,sK2))
    | spl19_2 ),
    inference(resolution,[],[f357,f281])).

fof(f15192,plain,
    ( ~ spl19_37
    | spl19_290 ),
    inference(avatar_split_clause,[],[f15151,f6747,f627])).

fof(f15151,plain,
    ( ~ r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK0)
    | spl19_290 ),
    inference(resolution,[],[f6749,f282])).

fof(f13264,plain,(
    spl19_56 ),
    inference(avatar_contradiction_clause,[],[f13263])).

fof(f13263,plain,
    ( $false
    | spl19_56 ),
    inference(subsumption_resolution,[],[f13262,f184])).

fof(f184,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f13262,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),sK0)
    | spl19_56 ),
    inference(subsumption_resolution,[],[f13253,f184])).

fof(f13253,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK2),sK1)
    | ~ r1_tarski(k3_xboole_0(sK0,sK1),sK0)
    | spl19_56 ),
    inference(resolution,[],[f915,f269])).

fof(f269,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f113])).

fof(f113,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f112])).

fof(f112,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f43])).

fof(f43,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_xboole_1)).

fof(f915,plain,
    ( ~ r1_tarski(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k2_xboole_0(sK0,sK1))
    | spl19_56 ),
    inference(avatar_component_clause,[],[f913])).

fof(f11216,plain,
    ( spl19_37
    | ~ spl19_3 ),
    inference(avatar_split_clause,[],[f11194,f360,f627])).

fof(f11194,plain,
    ( r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),sK0)
    | ~ spl19_3 ),
    inference(resolution,[],[f362,f279])).

fof(f6333,plain,
    ( ~ spl19_1
    | ~ spl19_3 ),
    inference(avatar_split_clause,[],[f6332,f360,f352])).

fof(f6332,plain,
    ( ~ r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0)))
    | ~ spl19_3 ),
    inference(subsumption_resolution,[],[f6306,f287])).

fof(f6306,plain,
    ( sQ18_eqProxy(k2_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0)),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0)))
    | ~ r2_hidden(sK15(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0))),k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0)))
    | ~ spl19_3 ),
    inference(resolution,[],[f362,f332])).

fof(f332,plain,(
    ! [X2,X0,X1] :
      ( sQ18_eqProxy(k2_xboole_0(X0,X1),X2)
      | ~ r2_hidden(sK15(X0,X1,X2),X1)
      | ~ r2_hidden(sK15(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f260,f284])).

fof(f260,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK15(X0,X1,X2),X1)
      | ~ r2_hidden(sK15(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f161])).
%------------------------------------------------------------------------------
