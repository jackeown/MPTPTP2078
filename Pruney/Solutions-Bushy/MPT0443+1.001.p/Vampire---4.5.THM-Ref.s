%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0443+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:59 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 179 expanded)
%              Number of leaves         :   17 (  72 expanded)
%              Depth                    :   11
%              Number of atoms          :  258 ( 942 expanded)
%              Number of equality atoms :   33 ( 130 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f173,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f60,f79,f96,f128,f129,f145,f170,f172])).

fof(f172,plain,
    ( ~ spl7_8
    | spl7_1 ),
    inference(avatar_split_clause,[],[f63,f49,f125])).

fof(f125,plain,
    ( spl7_8
  <=> r2_hidden(sK2(k2_xboole_0(sK0,sK1),k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f49,plain,
    ( spl7_1
  <=> r2_hidden(sK2(k2_xboole_0(sK0,sK1),k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))),k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f63,plain,
    ( ~ r2_hidden(sK2(k2_xboole_0(sK0,sK1),k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))),k2_relat_1(sK1))
    | spl7_1 ),
    inference(resolution,[],[f50,f35])).

fof(f35,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f17,f18])).

fof(f18,plain,(
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

fof(f17,plain,(
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
    inference(rectify,[],[f16])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f15])).

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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f50,plain,
    ( ~ r2_hidden(sK2(k2_xboole_0(sK0,sK1),k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))),k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f170,plain,
    ( spl7_8
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f169,f76,f125])).

fof(f76,plain,
    ( spl7_5
  <=> r2_hidden(k4_tarski(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))),sK2(k2_xboole_0(sK0,sK1),k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f169,plain,
    ( r2_hidden(sK2(k2_xboole_0(sK0,sK1),k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))),k2_relat_1(sK1))
    | ~ spl7_5 ),
    inference(resolution,[],[f78,f33])).

fof(f33,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK4(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f10,f13,f12,f11])).

fof(f11,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK2(X0,X1)),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK2(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f78,plain,
    ( r2_hidden(k4_tarski(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))),sK2(k2_xboole_0(sK0,sK1),k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))),sK1)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f76])).

fof(f145,plain,
    ( ~ spl7_8
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f142,f58,f125])).

fof(f58,plain,
    ( spl7_3
  <=> ! [X0] : ~ r2_hidden(k4_tarski(X0,sK2(k2_xboole_0(sK0,sK1),k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))),k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f142,plain,
    ( ~ r2_hidden(sK2(k2_xboole_0(sK0,sK1),k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))),k2_relat_1(sK1))
    | ~ spl7_3 ),
    inference(resolution,[],[f112,f34])).

fof(f34,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK4(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f112,plain,
    ( ! [X1] : ~ r2_hidden(k4_tarski(X1,sK2(k2_xboole_0(sK0,sK1),k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))),sK1)
    | ~ spl7_3 ),
    inference(resolution,[],[f59,f35])).

fof(f59,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK2(k2_xboole_0(sK0,sK1),k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))),k2_xboole_0(sK0,sK1))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f129,plain,
    ( ~ spl7_7
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f116,f58,f121])).

fof(f121,plain,
    ( spl7_7
  <=> r2_hidden(sK2(k2_xboole_0(sK0,sK1),k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f116,plain,
    ( ~ r2_hidden(sK2(k2_xboole_0(sK0,sK1),k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))),k2_relat_1(sK0))
    | ~ spl7_3 ),
    inference(resolution,[],[f111,f34])).

fof(f111,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK2(k2_xboole_0(sK0,sK1),k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))),sK0)
    | ~ spl7_3 ),
    inference(resolution,[],[f59,f36])).

fof(f36,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f128,plain,
    ( spl7_7
    | spl7_8
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f102,f49,f125,f121])).

fof(f102,plain,
    ( r2_hidden(sK2(k2_xboole_0(sK0,sK1),k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))),k2_relat_1(sK1))
    | r2_hidden(sK2(k2_xboole_0(sK0,sK1),k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))),k2_relat_1(sK0))
    | ~ spl7_1 ),
    inference(resolution,[],[f51,f37])).

fof(f37,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f51,plain,
    ( r2_hidden(sK2(k2_xboole_0(sK0,sK1),k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))),k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f96,plain,
    ( spl7_1
    | ~ spl7_4 ),
    inference(avatar_contradiction_clause,[],[f92])).

fof(f92,plain,
    ( $false
    | spl7_1
    | ~ spl7_4 ),
    inference(resolution,[],[f74,f80])).

fof(f80,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK2(k2_xboole_0(sK0,sK1),k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))),sK0)
    | spl7_1 ),
    inference(resolution,[],[f62,f33])).

fof(f62,plain,
    ( ~ r2_hidden(sK2(k2_xboole_0(sK0,sK1),k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))),k2_relat_1(sK0))
    | spl7_1 ),
    inference(resolution,[],[f50,f36])).

fof(f74,plain,
    ( r2_hidden(k4_tarski(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))),sK2(k2_xboole_0(sK0,sK1),k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))),sK0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl7_4
  <=> r2_hidden(k4_tarski(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))),sK2(k2_xboole_0(sK0,sK1),k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f79,plain,
    ( spl7_4
    | spl7_5
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f66,f53,f76,f72])).

fof(f53,plain,
    ( spl7_2
  <=> r2_hidden(k4_tarski(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))),sK2(k2_xboole_0(sK0,sK1),k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))),k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f66,plain,
    ( r2_hidden(k4_tarski(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))),sK2(k2_xboole_0(sK0,sK1),k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))),sK1)
    | r2_hidden(k4_tarski(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))),sK2(k2_xboole_0(sK0,sK1),k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))),sK0)
    | ~ spl7_2 ),
    inference(resolution,[],[f55,f37])).

fof(f55,plain,
    ( r2_hidden(k4_tarski(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))),sK2(k2_xboole_0(sK0,sK1),k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))),k2_xboole_0(sK0,sK1))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f60,plain,
    ( ~ spl7_1
    | spl7_3 ),
    inference(avatar_split_clause,[],[f47,f58,f49])).

fof(f47,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(X0,sK2(k2_xboole_0(sK0,sK1),k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))),k2_xboole_0(sK0,sK1))
      | ~ r2_hidden(sK2(k2_xboole_0(sK0,sK1),k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))),k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) ) ),
    inference(resolution,[],[f39,f40])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( sQ6_eqProxy(k2_relat_1(X0),X1)
      | ~ r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0)
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(equality_proxy_replacement,[],[f26,f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( sQ6_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ6_eqProxy])])).

fof(f26,plain,(
    ! [X0,X3,X1] :
      ( k2_relat_1(X0) = X1
      | ~ r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0)
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f39,plain,(
    ~ sQ6_eqProxy(k2_relat_1(k2_xboole_0(sK0,sK1)),k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) ),
    inference(equality_proxy_replacement,[],[f22,f38])).

fof(f22,plain,(
    k2_relat_1(k2_xboole_0(sK0,sK1)) != k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,
    ( k2_relat_1(k2_xboole_0(sK0,sK1)) != k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f7,f6])).

fof(f6,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_relat_1(k2_xboole_0(X0,X1)) != k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k2_relat_1(k2_xboole_0(sK0,X1)) != k2_xboole_0(k2_relat_1(sK0),k2_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,
    ( ? [X1] :
        ( k2_relat_1(k2_xboole_0(sK0,X1)) != k2_xboole_0(k2_relat_1(sK0),k2_relat_1(X1))
        & v1_relat_1(X1) )
   => ( k2_relat_1(k2_xboole_0(sK0,sK1)) != k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_relat_1(k2_xboole_0(X0,X1)) != k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_relat_1)).

fof(f56,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f46,f53,f49])).

fof(f46,plain,
    ( r2_hidden(k4_tarski(sK3(k2_xboole_0(sK0,sK1),k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))),sK2(k2_xboole_0(sK0,sK1),k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))),k2_xboole_0(sK0,sK1))
    | r2_hidden(sK2(k2_xboole_0(sK0,sK1),k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))),k2_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) ),
    inference(resolution,[],[f39,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( sQ6_eqProxy(k2_relat_1(X0),X1)
      | r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0)
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(equality_proxy_replacement,[],[f25,f38])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0)
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f14])).

%------------------------------------------------------------------------------
