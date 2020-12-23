%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:18 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 140 expanded)
%              Number of leaves         :   17 (  58 expanded)
%              Depth                    :   12
%              Number of atoms          :  314 ( 822 expanded)
%              Number of equality atoms :   19 (  44 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f93,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f56,f60,f68,f73,f88,f92])).

fof(f92,plain,
    ( ~ spl10_1
    | ~ spl10_6
    | spl10_7 ),
    inference(avatar_split_clause,[],[f90,f86,f66,f46])).

fof(f46,plain,
    ( spl10_1
  <=> r2_hidden(sK0,k9_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f66,plain,
    ( spl10_6
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f86,plain,
    ( spl10_7
  <=> r2_hidden(sK6(sK2,sK1,sK0),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f90,plain,
    ( ~ r2_hidden(sK0,k9_relat_1(sK2,sK1))
    | ~ spl10_6
    | spl10_7 ),
    inference(resolution,[],[f89,f80])).

fof(f80,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(sK6(sK2,X1,X0),X0),sK2)
        | ~ r2_hidden(X0,k9_relat_1(sK2,X1)) )
    | ~ spl10_6 ),
    inference(resolution,[],[f42,f67])).

fof(f67,plain,
    ( v1_relat_1(sK2)
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f66])).

fof(f42,plain,(
    ! [X6,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | r2_hidden(k4_tarski(sK6(X0,X1,X6),X6),X0) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X1,X6),X6),X0)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f14,f17,f16,f15])).

fof(f15,plain,(
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

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X5,sK4(X0,X1,X2)),X0) )
     => ( r2_hidden(sK5(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK5(X0,X1,X2),sK4(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X8,X6),X0) )
     => ( r2_hidden(sK6(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(sK6(X0,X1,X6),X6),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
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
    inference(rectify,[],[f13])).

fof(f13,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).

fof(f89,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK6(sK2,sK1,sK0),X0),sK2)
    | spl10_7 ),
    inference(resolution,[],[f87,f43])).

fof(f43,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK7(X0,X1),X3),X0)
            | ~ r2_hidden(sK7(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0)
            | r2_hidden(sK7(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f20,f23,f22,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK7(X0,X1),X3),X0)
          | ~ r2_hidden(sK7(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK7(X0,X1),X4),X0)
          | r2_hidden(sK7(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK7(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f87,plain,
    ( ~ r2_hidden(sK6(sK2,sK1,sK0),k1_relat_1(sK2))
    | spl10_7 ),
    inference(avatar_component_clause,[],[f86])).

fof(f88,plain,
    ( ~ spl10_6
    | ~ spl10_1
    | ~ spl10_7
    | ~ spl10_2
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f83,f66,f49,f86,f46,f66])).

fof(f49,plain,
    ( spl10_2
  <=> ! [X3] :
        ( ~ r2_hidden(X3,sK1)
        | ~ r2_hidden(X3,k1_relat_1(sK2))
        | ~ r2_hidden(k4_tarski(X3,sK0),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f83,plain,
    ( ~ r2_hidden(sK6(sK2,sK1,sK0),k1_relat_1(sK2))
    | ~ r2_hidden(sK0,k9_relat_1(sK2,sK1))
    | ~ v1_relat_1(sK2)
    | ~ spl10_2
    | ~ spl10_6 ),
    inference(duplicate_literal_removal,[],[f82])).

fof(f82,plain,
    ( ~ r2_hidden(sK6(sK2,sK1,sK0),k1_relat_1(sK2))
    | ~ r2_hidden(sK0,k9_relat_1(sK2,sK1))
    | ~ r2_hidden(sK0,k9_relat_1(sK2,sK1))
    | ~ v1_relat_1(sK2)
    | ~ spl10_2
    | ~ spl10_6 ),
    inference(resolution,[],[f81,f41])).

fof(f41,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f81,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK6(sK2,X0,sK0),sK1)
        | ~ r2_hidden(sK6(sK2,X0,sK0),k1_relat_1(sK2))
        | ~ r2_hidden(sK0,k9_relat_1(sK2,X0)) )
    | ~ spl10_2
    | ~ spl10_6 ),
    inference(resolution,[],[f80,f50])).

fof(f50,plain,
    ( ! [X3] :
        ( ~ r2_hidden(k4_tarski(X3,sK0),sK2)
        | ~ r2_hidden(X3,k1_relat_1(sK2))
        | ~ r2_hidden(X3,sK1) )
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f73,plain,
    ( ~ spl10_3
    | spl10_1
    | ~ spl10_4
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f71,f66,f58,f46,f54])).

fof(f54,plain,
    ( spl10_3
  <=> r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f58,plain,
    ( spl10_4
  <=> r2_hidden(k4_tarski(sK3,sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f71,plain,
    ( ~ r2_hidden(sK3,sK1)
    | spl10_1
    | ~ spl10_4
    | ~ spl10_6 ),
    inference(resolution,[],[f70,f59])).

fof(f59,plain,
    ( r2_hidden(k4_tarski(sK3,sK0),sK2)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f58])).

fof(f70,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK0),sK2)
        | ~ r2_hidden(X0,sK1) )
    | spl10_1
    | ~ spl10_6 ),
    inference(resolution,[],[f69,f47])).

fof(f47,plain,
    ( ~ r2_hidden(sK0,k9_relat_1(sK2,sK1))
    | spl10_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f69,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(X2,k9_relat_1(sK2,X1))
        | ~ r2_hidden(k4_tarski(X0,X2),sK2)
        | ~ r2_hidden(X0,X1) )
    | ~ spl10_6 ),
    inference(resolution,[],[f40,f67])).

fof(f40,plain,(
    ! [X6,X0,X7,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | r2_hidden(X6,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f68,plain,(
    spl10_6 ),
    inference(avatar_split_clause,[],[f25,f66])).

fof(f25,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ( ! [X3] :
          ( ~ r2_hidden(X3,sK1)
          | ~ r2_hidden(k4_tarski(X3,sK0),sK2)
          | ~ r2_hidden(X3,k1_relat_1(sK2)) )
      | ~ r2_hidden(sK0,k9_relat_1(sK2,sK1)) )
    & ( ( r2_hidden(sK3,sK1)
        & r2_hidden(k4_tarski(sK3,sK0),sK2)
        & r2_hidden(sK3,k1_relat_1(sK2)) )
      | r2_hidden(sK0,k9_relat_1(sK2,sK1)) )
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f11,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2] :
        ( ( ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | r2_hidden(X0,k9_relat_1(X2,X1)) )
        & v1_relat_1(X2) )
   => ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK1)
            | ~ r2_hidden(k4_tarski(X3,sK0),sK2)
            | ~ r2_hidden(X3,k1_relat_1(sK2)) )
        | ~ r2_hidden(sK0,k9_relat_1(sK2,sK1)) )
      & ( ? [X4] :
            ( r2_hidden(X4,sK1)
            & r2_hidden(k4_tarski(X4,sK0),sK2)
            & r2_hidden(X4,k1_relat_1(sK2)) )
        | r2_hidden(sK0,k9_relat_1(sK2,sK1)) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,
    ( ? [X4] :
        ( r2_hidden(X4,sK1)
        & r2_hidden(k4_tarski(X4,sK0),sK2)
        & r2_hidden(X4,k1_relat_1(sK2)) )
   => ( r2_hidden(sK3,sK1)
      & r2_hidden(k4_tarski(sK3,sK0),sK2)
      & r2_hidden(sK3,k1_relat_1(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X0),X2)
            | ~ r2_hidden(X3,k1_relat_1(X2)) )
        | ~ r2_hidden(X0,k9_relat_1(X2,X1)) )
      & ( ? [X4] :
            ( r2_hidden(X4,X1)
            & r2_hidden(k4_tarski(X4,X0),X2)
            & r2_hidden(X4,k1_relat_1(X2)) )
        | r2_hidden(X0,k9_relat_1(X2,X1)) )
      & v1_relat_1(X2) ) ),
    inference(rectify,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X0),X2)
            | ~ r2_hidden(X3,k1_relat_1(X2)) )
        | ~ r2_hidden(X0,k9_relat_1(X2,X1)) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) )
        | r2_hidden(X0,k9_relat_1(X2,X1)) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X0),X2)
            | ~ r2_hidden(X3,k1_relat_1(X2)) )
        | ~ r2_hidden(X0,k9_relat_1(X2,X1)) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) )
        | r2_hidden(X0,k9_relat_1(X2,X1)) )
      & v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <~> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(X0,k9_relat_1(X2,X1))
        <=> ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(f60,plain,
    ( spl10_1
    | spl10_4 ),
    inference(avatar_split_clause,[],[f27,f58,f46])).

fof(f27,plain,
    ( r2_hidden(k4_tarski(sK3,sK0),sK2)
    | r2_hidden(sK0,k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f56,plain,
    ( spl10_1
    | spl10_3 ),
    inference(avatar_split_clause,[],[f28,f54,f46])).

fof(f28,plain,
    ( r2_hidden(sK3,sK1)
    | r2_hidden(sK0,k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f51,plain,
    ( ~ spl10_1
    | spl10_2 ),
    inference(avatar_split_clause,[],[f29,f49,f46])).

fof(f29,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK1)
      | ~ r2_hidden(k4_tarski(X3,sK0),sK2)
      | ~ r2_hidden(X3,k1_relat_1(sK2))
      | ~ r2_hidden(sK0,k9_relat_1(sK2,sK1)) ) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:43:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (27526)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.47  % (27522)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.47  % (27531)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.48  % (27522)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % (27520)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.48  % (27523)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.48  % (27529)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f93,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f51,f56,f60,f68,f73,f88,f92])).
% 0.22/0.48  fof(f92,plain,(
% 0.22/0.48    ~spl10_1 | ~spl10_6 | spl10_7),
% 0.22/0.48    inference(avatar_split_clause,[],[f90,f86,f66,f46])).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    spl10_1 <=> r2_hidden(sK0,k9_relat_1(sK2,sK1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.22/0.48  fof(f66,plain,(
% 0.22/0.48    spl10_6 <=> v1_relat_1(sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 0.22/0.48  fof(f86,plain,(
% 0.22/0.48    spl10_7 <=> r2_hidden(sK6(sK2,sK1,sK0),k1_relat_1(sK2))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 0.22/0.48  fof(f90,plain,(
% 0.22/0.48    ~r2_hidden(sK0,k9_relat_1(sK2,sK1)) | (~spl10_6 | spl10_7)),
% 0.22/0.48    inference(resolution,[],[f89,f80])).
% 0.22/0.48  fof(f80,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK6(sK2,X1,X0),X0),sK2) | ~r2_hidden(X0,k9_relat_1(sK2,X1))) ) | ~spl10_6),
% 0.22/0.48    inference(resolution,[],[f42,f67])).
% 0.22/0.48  fof(f67,plain,(
% 0.22/0.48    v1_relat_1(sK2) | ~spl10_6),
% 0.22/0.48    inference(avatar_component_clause,[],[f66])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    ( ! [X6,X0,X1] : (~v1_relat_1(X0) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | r2_hidden(k4_tarski(sK6(X0,X1,X6),X6),X0)) )),
% 0.22/0.48    inference(equality_resolution,[],[f30])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    ( ! [X6,X2,X0,X1] : (r2_hidden(k4_tarski(sK6(X0,X1,X6),X6),X0) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,sK4(X0,X1,X2)),X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK5(X0,X1,X2),sK4(X0,X1,X2)),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0))) & ((r2_hidden(sK6(X0,X1,X6),X1) & r2_hidden(k4_tarski(sK6(X0,X1,X6),X6),X0)) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f14,f17,f16,f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X3),X0)) | r2_hidden(X3,X2))) => ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,sK4(X0,X1,X2)),X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,sK4(X0,X1,X2)),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X2,X1,X0] : (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,sK4(X0,X1,X2)),X0)) => (r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK5(X0,X1,X2),sK4(X0,X1,X2)),X0)))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X6,X1,X0] : (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X8,X6),X0)) => (r2_hidden(sK6(X0,X1,X6),X1) & r2_hidden(k4_tarski(sK6(X0,X1,X6),X6),X0)))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X3),X0)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0))) & (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X8,X6),X0)) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(rectify,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(nnf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,plain,(
% 0.22/0.49    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).
% 0.22/0.49  fof(f89,plain,(
% 0.22/0.49    ( ! [X0] : (~r2_hidden(k4_tarski(sK6(sK2,sK1,sK0),X0),sK2)) ) | spl10_7),
% 0.22/0.49    inference(resolution,[],[f87,f43])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    ( ! [X6,X0,X5] : (r2_hidden(X5,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X6),X0)) )),
% 0.22/0.49    inference(equality_resolution,[],[f37])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK7(X0,X1),X3),X0) | ~r2_hidden(sK7(X0,X1),X1)) & (r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0) | r2_hidden(sK7(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f20,f23,f22,f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK7(X0,X1),X3),X0) | ~r2_hidden(sK7(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK7(X0,X1),X4),X0) | r2_hidden(sK7(X0,X1),X1))))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK7(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK7(X0,X1),sK8(X0,X1)),X0))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK9(X0,X5)),X0))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.22/0.49    inference(rectify,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 0.22/0.49    inference(nnf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 0.22/0.49  fof(f87,plain,(
% 0.22/0.49    ~r2_hidden(sK6(sK2,sK1,sK0),k1_relat_1(sK2)) | spl10_7),
% 0.22/0.49    inference(avatar_component_clause,[],[f86])).
% 0.22/0.49  fof(f88,plain,(
% 0.22/0.49    ~spl10_6 | ~spl10_1 | ~spl10_7 | ~spl10_2 | ~spl10_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f83,f66,f49,f86,f46,f66])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    spl10_2 <=> ! [X3] : (~r2_hidden(X3,sK1) | ~r2_hidden(X3,k1_relat_1(sK2)) | ~r2_hidden(k4_tarski(X3,sK0),sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.22/0.49  fof(f83,plain,(
% 0.22/0.49    ~r2_hidden(sK6(sK2,sK1,sK0),k1_relat_1(sK2)) | ~r2_hidden(sK0,k9_relat_1(sK2,sK1)) | ~v1_relat_1(sK2) | (~spl10_2 | ~spl10_6)),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f82])).
% 0.22/0.49  fof(f82,plain,(
% 0.22/0.49    ~r2_hidden(sK6(sK2,sK1,sK0),k1_relat_1(sK2)) | ~r2_hidden(sK0,k9_relat_1(sK2,sK1)) | ~r2_hidden(sK0,k9_relat_1(sK2,sK1)) | ~v1_relat_1(sK2) | (~spl10_2 | ~spl10_6)),
% 0.22/0.49    inference(resolution,[],[f81,f41])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    ( ! [X6,X0,X1] : (r2_hidden(sK6(X0,X1,X6),X1) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(equality_resolution,[],[f31])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ( ! [X6,X2,X0,X1] : (r2_hidden(sK6(X0,X1,X6),X1) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f81,plain,(
% 0.22/0.49    ( ! [X0] : (~r2_hidden(sK6(sK2,X0,sK0),sK1) | ~r2_hidden(sK6(sK2,X0,sK0),k1_relat_1(sK2)) | ~r2_hidden(sK0,k9_relat_1(sK2,X0))) ) | (~spl10_2 | ~spl10_6)),
% 0.22/0.49    inference(resolution,[],[f80,f50])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    ( ! [X3] : (~r2_hidden(k4_tarski(X3,sK0),sK2) | ~r2_hidden(X3,k1_relat_1(sK2)) | ~r2_hidden(X3,sK1)) ) | ~spl10_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f49])).
% 0.22/0.49  fof(f73,plain,(
% 0.22/0.49    ~spl10_3 | spl10_1 | ~spl10_4 | ~spl10_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f71,f66,f58,f46,f54])).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    spl10_3 <=> r2_hidden(sK3,sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.22/0.49  fof(f58,plain,(
% 0.22/0.49    spl10_4 <=> r2_hidden(k4_tarski(sK3,sK0),sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 0.22/0.49  fof(f71,plain,(
% 0.22/0.49    ~r2_hidden(sK3,sK1) | (spl10_1 | ~spl10_4 | ~spl10_6)),
% 0.22/0.49    inference(resolution,[],[f70,f59])).
% 0.22/0.49  fof(f59,plain,(
% 0.22/0.49    r2_hidden(k4_tarski(sK3,sK0),sK2) | ~spl10_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f58])).
% 0.22/0.49  fof(f70,plain,(
% 0.22/0.49    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK0),sK2) | ~r2_hidden(X0,sK1)) ) | (spl10_1 | ~spl10_6)),
% 0.22/0.49    inference(resolution,[],[f69,f47])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    ~r2_hidden(sK0,k9_relat_1(sK2,sK1)) | spl10_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f46])).
% 0.22/0.49  fof(f69,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (r2_hidden(X2,k9_relat_1(sK2,X1)) | ~r2_hidden(k4_tarski(X0,X2),sK2) | ~r2_hidden(X0,X1)) ) | ~spl10_6),
% 0.22/0.49    inference(resolution,[],[f40,f67])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    ( ! [X6,X0,X7,X1] : (~v1_relat_1(X0) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0) | r2_hidden(X6,k9_relat_1(X0,X1))) )),
% 0.22/0.49    inference(equality_resolution,[],[f32])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ( ! [X6,X2,X0,X7,X1] : (r2_hidden(X6,X2) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0) | k9_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f68,plain,(
% 0.22/0.49    spl10_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f25,f66])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    v1_relat_1(sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    (! [X3] : (~r2_hidden(X3,sK1) | ~r2_hidden(k4_tarski(X3,sK0),sK2) | ~r2_hidden(X3,k1_relat_1(sK2))) | ~r2_hidden(sK0,k9_relat_1(sK2,sK1))) & ((r2_hidden(sK3,sK1) & r2_hidden(k4_tarski(sK3,sK0),sK2) & r2_hidden(sK3,k1_relat_1(sK2))) | r2_hidden(sK0,k9_relat_1(sK2,sK1))) & v1_relat_1(sK2)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f11,f10])).
% 0.22/0.49  fof(f10,plain,(
% 0.22/0.49    ? [X0,X1,X2] : ((! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | r2_hidden(X0,k9_relat_1(X2,X1))) & v1_relat_1(X2)) => ((! [X3] : (~r2_hidden(X3,sK1) | ~r2_hidden(k4_tarski(X3,sK0),sK2) | ~r2_hidden(X3,k1_relat_1(sK2))) | ~r2_hidden(sK0,k9_relat_1(sK2,sK1))) & (? [X4] : (r2_hidden(X4,sK1) & r2_hidden(k4_tarski(X4,sK0),sK2) & r2_hidden(X4,k1_relat_1(sK2))) | r2_hidden(sK0,k9_relat_1(sK2,sK1))) & v1_relat_1(sK2))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ? [X4] : (r2_hidden(X4,sK1) & r2_hidden(k4_tarski(X4,sK0),sK2) & r2_hidden(X4,k1_relat_1(sK2))) => (r2_hidden(sK3,sK1) & r2_hidden(k4_tarski(sK3,sK0),sK2) & r2_hidden(sK3,k1_relat_1(sK2)))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f9,plain,(
% 0.22/0.49    ? [X0,X1,X2] : ((! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | r2_hidden(X0,k9_relat_1(X2,X1))) & v1_relat_1(X2))),
% 0.22/0.49    inference(rectify,[],[f8])).
% 0.22/0.49  fof(f8,plain,(
% 0.22/0.49    ? [X0,X1,X2] : ((! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | r2_hidden(X0,k9_relat_1(X2,X1))) & v1_relat_1(X2))),
% 0.22/0.49    inference(flattening,[],[f7])).
% 0.22/0.49  fof(f7,plain,(
% 0.22/0.49    ? [X0,X1,X2] : (((! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | r2_hidden(X0,k9_relat_1(X2,X1)))) & v1_relat_1(X2))),
% 0.22/0.49    inference(nnf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,plain,(
% 0.22/0.49    ? [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <~> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) & v1_relat_1(X2))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.22/0.49    inference(negated_conjecture,[],[f3])).
% 0.22/0.49  fof(f3,conjecture,(
% 0.22/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 0.22/0.49  fof(f60,plain,(
% 0.22/0.49    spl10_1 | spl10_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f27,f58,f46])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    r2_hidden(k4_tarski(sK3,sK0),sK2) | r2_hidden(sK0,k9_relat_1(sK2,sK1))),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    spl10_1 | spl10_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f28,f54,f46])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    r2_hidden(sK3,sK1) | r2_hidden(sK0,k9_relat_1(sK2,sK1))),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    ~spl10_1 | spl10_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f29,f49,f46])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ( ! [X3] : (~r2_hidden(X3,sK1) | ~r2_hidden(k4_tarski(X3,sK0),sK2) | ~r2_hidden(X3,k1_relat_1(sK2)) | ~r2_hidden(sK0,k9_relat_1(sK2,sK1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (27522)------------------------------
% 0.22/0.49  % (27522)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (27522)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (27522)Memory used [KB]: 10618
% 0.22/0.49  % (27522)Time elapsed: 0.067 s
% 0.22/0.49  % (27522)------------------------------
% 0.22/0.49  % (27522)------------------------------
% 0.22/0.49  % (27515)Success in time 0.128 s
%------------------------------------------------------------------------------
