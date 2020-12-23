%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0546+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:10 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 189 expanded)
%              Number of leaves         :   24 (  82 expanded)
%              Depth                    :   10
%              Number of atoms          :  407 ( 901 expanded)
%              Number of equality atoms :   41 ( 106 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f432,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f111,f115,f125,f129,f186,f191,f202,f327,f338,f343,f430,f431])).

fof(f431,plain,
    ( ~ spl11_1
    | ~ spl11_12
    | spl11_8
    | ~ spl11_7 ),
    inference(avatar_split_clause,[],[f344,f113,f127,f179,f86])).

fof(f86,plain,
    ( spl11_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f179,plain,
    ( spl11_12
  <=> v1_relat_1(k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f127,plain,
    ( spl11_8
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(k4_tarski(X0,sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f113,plain,
    ( spl11_7
  <=> ! [X0] : ~ r2_hidden(k4_tarski(X0,sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f344,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),sK1)
        | ~ r2_hidden(X0,sK0)
        | ~ v1_relat_1(k7_relat_1(sK1,sK0))
        | ~ v1_relat_1(sK1) )
    | ~ spl11_7 ),
    inference(resolution,[],[f114,f49])).

fof(f49,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X2)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0)
                  | ~ r2_hidden(sK2(X0,X1,X2),X1)
                  | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0)
                    & r2_hidden(sK2(X0,X1,X2),X1) )
                  | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f15,f16])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0)
            & r2_hidden(sK2(X0,X1,X2),X1) )
          | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_relat_1)).

fof(f114,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),k7_relat_1(sK1,sK0))
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f113])).

fof(f430,plain,
    ( ~ spl11_25
    | ~ spl11_8
    | ~ spl11_24 ),
    inference(avatar_split_clause,[],[f422,f335,f127,f340])).

fof(f340,plain,
    ( spl11_25
  <=> r2_hidden(sK6(sK1,sK0,sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_25])])).

fof(f335,plain,
    ( spl11_24
  <=> r2_hidden(k4_tarski(sK6(sK1,sK0,sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_24])])).

fof(f422,plain,
    ( ~ r2_hidden(sK6(sK1,sK0,sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),sK0)
    | ~ spl11_8
    | ~ spl11_24 ),
    inference(resolution,[],[f337,f128])).

fof(f128,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f127])).

fof(f337,plain,
    ( r2_hidden(k4_tarski(sK6(sK1,sK0,sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),sK1)
    | ~ spl11_24 ),
    inference(avatar_component_clause,[],[f335])).

fof(f343,plain,
    ( ~ spl11_1
    | spl11_25
    | ~ spl11_5 ),
    inference(avatar_split_clause,[],[f331,f104,f340,f86])).

fof(f104,plain,
    ( spl11_5
  <=> r2_hidden(sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),k9_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f331,plain,
    ( r2_hidden(sK6(sK1,sK0,sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl11_5 ),
    inference(resolution,[],[f106,f53])).

fof(f53,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(X4,sK4(X0,X1,X2)),X0) )
                | ~ r2_hidden(sK4(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK5(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK5(X0,X1,X2),sK4(X0,X1,X2)),X0) )
                | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ( r2_hidden(sK6(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(sK6(X0,X1,X6),X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f19,f22,f21,f20])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r2_hidden(k4_tarski(X4,X3),X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X5,X3),X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(X4,sK4(X0,X1,X2)),X0) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(X5,sK4(X0,X1,X2)),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X5,sK4(X0,X1,X2)),X0) )
     => ( r2_hidden(sK5(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK5(X0,X1,X2),sK4(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X8,X6),X0) )
     => ( r2_hidden(sK6(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(sK6(X0,X1,X6),X6),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( r2_hidden(X5,X1)
                      & r2_hidden(k4_tarski(X5,X3),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ? [X8] :
                      ( r2_hidden(X8,X1)
                      & r2_hidden(k4_tarski(X8,X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X4,X3),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) ) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_relat_1)).

fof(f106,plain,
    ( r2_hidden(sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),k9_relat_1(sK1,sK0))
    | ~ spl11_5 ),
    inference(avatar_component_clause,[],[f104])).

fof(f338,plain,
    ( ~ spl11_1
    | spl11_24
    | ~ spl11_5 ),
    inference(avatar_split_clause,[],[f330,f104,f335,f86])).

fof(f330,plain,
    ( r2_hidden(k4_tarski(sK6(sK1,sK0,sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl11_5 ),
    inference(resolution,[],[f106,f54])).

fof(f54,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X1,X6),X6),X0)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X1,X6),X6),X0)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f327,plain,
    ( ~ spl11_13
    | ~ spl11_8
    | ~ spl11_14 ),
    inference(avatar_split_clause,[],[f319,f188,f127,f183])).

fof(f183,plain,
    ( spl11_13
  <=> r2_hidden(sK8(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).

fof(f188,plain,
    ( spl11_14
  <=> r2_hidden(k4_tarski(sK8(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).

fof(f319,plain,
    ( ~ r2_hidden(sK8(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),sK0)
    | ~ spl11_8
    | ~ spl11_14 ),
    inference(resolution,[],[f190,f128])).

fof(f190,plain,
    ( r2_hidden(k4_tarski(sK8(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),sK1)
    | ~ spl11_14 ),
    inference(avatar_component_clause,[],[f188])).

fof(f202,plain,(
    spl11_12 ),
    inference(avatar_contradiction_clause,[],[f200])).

fof(f200,plain,
    ( $false
    | spl11_12 ),
    inference(resolution,[],[f181,f68])).

fof(f68,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(resolution,[],[f30,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f30,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( k2_relat_1(k7_relat_1(sK1,sK0)) != k9_relat_1(sK1,sK0)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f11])).

fof(f11,plain,
    ( ? [X0,X1] :
        ( k2_relat_1(k7_relat_1(X1,X0)) != k9_relat_1(X1,X0)
        & v1_relat_1(X1) )
   => ( k2_relat_1(k7_relat_1(sK1,sK0)) != k9_relat_1(sK1,sK0)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) != k9_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f181,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | spl11_12 ),
    inference(avatar_component_clause,[],[f179])).

fof(f191,plain,
    ( ~ spl11_1
    | ~ spl11_12
    | spl11_14
    | ~ spl11_6 ),
    inference(avatar_split_clause,[],[f172,f108,f188,f179,f86])).

fof(f108,plain,
    ( spl11_6
  <=> r2_hidden(k4_tarski(sK8(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f172,plain,
    ( r2_hidden(k4_tarski(sK8(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),sK1)
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl11_6 ),
    inference(resolution,[],[f110,f50])).

fof(f50,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f110,plain,
    ( r2_hidden(k4_tarski(sK8(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),k7_relat_1(sK1,sK0))
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f108])).

fof(f186,plain,
    ( ~ spl11_1
    | ~ spl11_12
    | spl11_13
    | ~ spl11_6 ),
    inference(avatar_split_clause,[],[f171,f108,f183,f179,f86])).

fof(f171,plain,
    ( r2_hidden(sK8(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),sK0)
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl11_6 ),
    inference(resolution,[],[f110,f51])).

fof(f51,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f129,plain,
    ( ~ spl11_1
    | spl11_8
    | spl11_5 ),
    inference(avatar_split_clause,[],[f122,f104,f127,f86])).

fof(f122,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(k4_tarski(X0,sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),sK1)
        | ~ v1_relat_1(sK1) )
    | spl11_5 ),
    inference(resolution,[],[f105,f52])).

fof(f52,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f105,plain,
    ( ~ r2_hidden(sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),k9_relat_1(sK1,sK0))
    | spl11_5 ),
    inference(avatar_component_clause,[],[f104])).

fof(f125,plain,(
    spl11_1 ),
    inference(avatar_contradiction_clause,[],[f124])).

fof(f124,plain,
    ( $false
    | spl11_1 ),
    inference(resolution,[],[f88,f30])).

fof(f88,plain,
    ( ~ v1_relat_1(sK1)
    | spl11_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f115,plain,
    ( ~ spl11_5
    | spl11_7 ),
    inference(avatar_split_clause,[],[f102,f113,f104])).

fof(f102,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(X0,sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),k7_relat_1(sK1,sK0))
      | ~ r2_hidden(sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),k9_relat_1(sK1,sK0)) ) ),
    inference(resolution,[],[f58,f65])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( sQ10_eqProxy(k2_relat_1(X0),X1)
      | ~ r2_hidden(k4_tarski(X3,sK7(X0,X1)),X0)
      | ~ r2_hidden(sK7(X0,X1),X1) ) ),
    inference(equality_proxy_replacement,[],[f48,f57])).

fof(f57,plain,(
    ! [X1,X0] :
      ( sQ10_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ10_eqProxy])])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( k2_relat_1(X0) = X1
      | ~ r2_hidden(k4_tarski(X3,sK7(X0,X1)),X0)
      | ~ r2_hidden(sK7(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK7(X0,X1)),X0)
            | ~ r2_hidden(sK7(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0)
            | r2_hidden(sK7(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK9(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f25,f28,f27,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK7(X0,X1)),X0)
          | ~ r2_hidden(sK7(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK7(X0,X1)),X0)
          | r2_hidden(sK7(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK7(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK9(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f58,plain,(
    ~ sQ10_eqProxy(k2_relat_1(k7_relat_1(sK1,sK0)),k9_relat_1(sK1,sK0)) ),
    inference(equality_proxy_replacement,[],[f31,f57])).

fof(f31,plain,(
    k2_relat_1(k7_relat_1(sK1,sK0)) != k9_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f111,plain,
    ( spl11_5
    | spl11_6 ),
    inference(avatar_split_clause,[],[f101,f108,f104])).

fof(f101,plain,
    ( r2_hidden(k4_tarski(sK8(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))),k7_relat_1(sK1,sK0))
    | r2_hidden(sK7(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)),k9_relat_1(sK1,sK0)) ),
    inference(resolution,[],[f58,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( sQ10_eqProxy(k2_relat_1(X0),X1)
      | r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0)
      | r2_hidden(sK7(X0,X1),X1) ) ),
    inference(equality_proxy_replacement,[],[f47,f57])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0)
      | r2_hidden(sK7(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f29])).

%------------------------------------------------------------------------------
