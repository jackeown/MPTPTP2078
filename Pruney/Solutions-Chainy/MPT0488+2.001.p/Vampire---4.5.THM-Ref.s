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
% DateTime   : Thu Dec  3 12:48:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 177 expanded)
%              Number of leaves         :   16 (  66 expanded)
%              Depth                    :   10
%              Number of atoms          :  322 ( 930 expanded)
%              Number of equality atoms :   22 (  73 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f231,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f64,f65,f99,f140,f145,f158,f188,f207,f229])).

fof(f229,plain,
    ( ~ spl9_3
    | ~ spl9_14 ),
    inference(avatar_contradiction_clause,[],[f225])).

fof(f225,plain,
    ( $false
    | ~ spl9_3
    | ~ spl9_14 ),
    inference(resolution,[],[f206,f71])).

fof(f71,plain,
    ( r2_hidden(k4_tarski(sK0,sK7(sK2,sK0)),sK2)
    | ~ spl9_3 ),
    inference(resolution,[],[f61,f43])).

fof(f43,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK5(X0,X1),X3),X0)
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0)
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f19,f22,f21,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK5(X0,X1),X3),X0)
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0)
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f61,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl9_3
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f206,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK0,X0),sK2)
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f205])).

fof(f205,plain,
    ( spl9_14
  <=> ! [X0] : ~ r2_hidden(k4_tarski(sK0,X0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f207,plain,
    ( ~ spl9_4
    | ~ spl9_10
    | ~ spl9_2
    | spl9_14
    | spl9_1 ),
    inference(avatar_split_clause,[],[f200,f52,f205,f56,f137,f83])).

fof(f83,plain,
    ( spl9_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f137,plain,
    ( spl9_10
  <=> v1_relat_1(k7_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f56,plain,
    ( spl9_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f52,plain,
    ( spl9_1
  <=> r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f200,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK0,X0),sK2)
        | ~ r2_hidden(sK0,sK1)
        | ~ v1_relat_1(k7_relat_1(sK2,sK1))
        | ~ v1_relat_1(sK2) )
    | spl9_1 ),
    inference(resolution,[],[f73,f39])).

fof(f39,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
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
              | ( ( ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)
                  | ~ r2_hidden(sK3(X0,X1,X2),X1)
                  | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)
                    & r2_hidden(sK3(X0,X1,X2),X1) )
                  | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f15,f16])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)
            & r2_hidden(sK3(X0,X1,X2),X1) )
          | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) ) ) ) ),
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
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
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

fof(f73,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK0,X0),k7_relat_1(sK2,sK1))
    | spl9_1 ),
    inference(resolution,[],[f54,f42])).

fof(f42,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f54,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))
    | spl9_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f188,plain,
    ( spl9_3
    | ~ spl9_11 ),
    inference(avatar_contradiction_clause,[],[f184])).

fof(f184,plain,
    ( $false
    | spl9_3
    | ~ spl9_11 ),
    inference(resolution,[],[f144,f107])).

fof(f107,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK0,X0),sK2)
    | spl9_3 ),
    inference(resolution,[],[f62,f42])).

fof(f62,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | spl9_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f144,plain,
    ( r2_hidden(k4_tarski(sK0,sK7(k7_relat_1(sK2,sK1),sK0)),sK2)
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl9_11
  <=> r2_hidden(k4_tarski(sK0,sK7(k7_relat_1(sK2,sK1),sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f158,plain,(
    spl9_10 ),
    inference(avatar_contradiction_clause,[],[f156])).

fof(f156,plain,
    ( $false
    | spl9_10 ),
    inference(resolution,[],[f139,f66])).

fof(f66,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK2,X0)) ),
    inference(resolution,[],[f24,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f24,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ( ~ r2_hidden(sK0,k1_relat_1(sK2))
      | ~ r2_hidden(sK0,sK1)
      | ~ r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) )
    & ( ( r2_hidden(sK0,k1_relat_1(sK2))
        & r2_hidden(sK0,sK1) )
      | r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) )
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1)
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) )
        & v1_relat_1(X2) )
   => ( ( ~ r2_hidden(sK0,k1_relat_1(sK2))
        | ~ r2_hidden(sK0,sK1)
        | ~ r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) )
      & ( ( r2_hidden(sK0,k1_relat_1(sK2))
          & r2_hidden(sK0,sK1) )
        | r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X0,k1_relat_1(X2))
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) )
      & ( ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) )
        | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X0,k1_relat_1(X2))
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) )
      & ( ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) )
        | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) )
      & v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <~> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
        <=> ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

fof(f139,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | spl9_10 ),
    inference(avatar_component_clause,[],[f137])).

fof(f145,plain,
    ( ~ spl9_4
    | ~ spl9_10
    | spl9_11
    | ~ spl9_1 ),
    inference(avatar_split_clause,[],[f132,f52,f142,f137,f83])).

fof(f132,plain,
    ( r2_hidden(k4_tarski(sK0,sK7(k7_relat_1(sK2,sK1),sK0)),sK2)
    | ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | ~ v1_relat_1(sK2)
    | ~ spl9_1 ),
    inference(resolution,[],[f109,f40])).

fof(f40,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f109,plain,
    ( r2_hidden(k4_tarski(sK0,sK7(k7_relat_1(sK2,sK1),sK0)),k7_relat_1(sK2,sK1))
    | ~ spl9_1 ),
    inference(resolution,[],[f53,f43])).

fof(f53,plain,
    ( r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f140,plain,
    ( ~ spl9_4
    | ~ spl9_10
    | spl9_2
    | ~ spl9_1 ),
    inference(avatar_split_clause,[],[f131,f52,f56,f137,f83])).

fof(f131,plain,
    ( r2_hidden(sK0,sK1)
    | ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | ~ v1_relat_1(sK2)
    | ~ spl9_1 ),
    inference(resolution,[],[f109,f41])).

fof(f41,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f99,plain,(
    spl9_4 ),
    inference(avatar_contradiction_clause,[],[f98])).

fof(f98,plain,
    ( $false
    | spl9_4 ),
    inference(resolution,[],[f85,f24])).

fof(f85,plain,
    ( ~ v1_relat_1(sK2)
    | spl9_4 ),
    inference(avatar_component_clause,[],[f83])).

fof(f65,plain,
    ( spl9_1
    | spl9_2 ),
    inference(avatar_split_clause,[],[f25,f56,f52])).

fof(f25,plain,
    ( r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f12])).

fof(f64,plain,
    ( spl9_1
    | spl9_3 ),
    inference(avatar_split_clause,[],[f26,f60,f52])).

fof(f26,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f12])).

fof(f63,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f27,f60,f56,f52])).

fof(f27,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:06:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (23981)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.46  % (23973)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.46  % (23966)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.46  % (23973)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f231,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f63,f64,f65,f99,f140,f145,f158,f188,f207,f229])).
% 0.21/0.46  fof(f229,plain,(
% 0.21/0.46    ~spl9_3 | ~spl9_14),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f225])).
% 0.21/0.46  fof(f225,plain,(
% 0.21/0.46    $false | (~spl9_3 | ~spl9_14)),
% 0.21/0.46    inference(resolution,[],[f206,f71])).
% 0.21/0.46  fof(f71,plain,(
% 0.21/0.46    r2_hidden(k4_tarski(sK0,sK7(sK2,sK0)),sK2) | ~spl9_3),
% 0.21/0.46    inference(resolution,[],[f61,f43])).
% 0.21/0.46  fof(f43,plain,(
% 0.21/0.46    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 0.21/0.46    inference(equality_resolution,[],[f35])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 0.21/0.47    inference(cnf_transformation,[],[f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK5(X0,X1),X3),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f19,f22,f21,f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK5(X0,X1),X3),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0) | r2_hidden(sK5(X0,X1),X1))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.21/0.47    inference(rectify,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 0.21/0.47    inference(nnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    r2_hidden(sK0,k1_relat_1(sK2)) | ~spl9_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f60])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    spl9_3 <=> r2_hidden(sK0,k1_relat_1(sK2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.21/0.47  fof(f206,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(k4_tarski(sK0,X0),sK2)) ) | ~spl9_14),
% 0.21/0.47    inference(avatar_component_clause,[],[f205])).
% 0.21/0.47  fof(f205,plain,(
% 0.21/0.47    spl9_14 <=> ! [X0] : ~r2_hidden(k4_tarski(sK0,X0),sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).
% 0.21/0.47  fof(f207,plain,(
% 0.21/0.47    ~spl9_4 | ~spl9_10 | ~spl9_2 | spl9_14 | spl9_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f200,f52,f205,f56,f137,f83])).
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    spl9_4 <=> v1_relat_1(sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.21/0.47  fof(f137,plain,(
% 0.21/0.47    spl9_10 <=> v1_relat_1(k7_relat_1(sK2,sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    spl9_2 <=> r2_hidden(sK0,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    spl9_1 <=> r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.21/0.47  fof(f200,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(k4_tarski(sK0,X0),sK2) | ~r2_hidden(sK0,sK1) | ~v1_relat_1(k7_relat_1(sK2,sK1)) | ~v1_relat_1(sK2)) ) | spl9_1),
% 0.21/0.47    inference(resolution,[],[f73,f39])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ( ! [X6,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1)) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(equality_resolution,[],[f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1) | k7_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0) | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0) & r2_hidden(sK3(X0,X1,X2),X1)) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1)) & ((r2_hidden(k4_tarski(X5,X6),X0) & r2_hidden(X5,X1)) | ~r2_hidden(k4_tarski(X5,X6),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f15,f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X2,X1,X0] : (? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0) | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0) & r2_hidden(sK3(X0,X1,X2),X1)) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1)) & ((r2_hidden(k4_tarski(X5,X6),X0) & r2_hidden(X5,X1)) | ~r2_hidden(k4_tarski(X5,X6),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(rectify,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(flattening,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ? [X3,X4] : (((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | (~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1))) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,plain,(
% 0.21/0.47    ! [X0] : (! [X1,X2] : ((k7_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (v1_relat_1(X2) => (k7_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1))))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_relat_1)).
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(k4_tarski(sK0,X0),k7_relat_1(sK2,sK1))) ) | spl9_1),
% 0.21/0.47    inference(resolution,[],[f54,f42])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ( ! [X6,X0,X5] : (r2_hidden(X5,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X6),X0)) )),
% 0.21/0.47    inference(equality_resolution,[],[f36])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 0.21/0.47    inference(cnf_transformation,[],[f23])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    ~r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) | spl9_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f52])).
% 0.21/0.47  fof(f188,plain,(
% 0.21/0.47    spl9_3 | ~spl9_11),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f184])).
% 0.21/0.47  fof(f184,plain,(
% 0.21/0.47    $false | (spl9_3 | ~spl9_11)),
% 0.21/0.47    inference(resolution,[],[f144,f107])).
% 0.21/0.47  fof(f107,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(k4_tarski(sK0,X0),sK2)) ) | spl9_3),
% 0.21/0.47    inference(resolution,[],[f62,f42])).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    ~r2_hidden(sK0,k1_relat_1(sK2)) | spl9_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f60])).
% 0.21/0.47  fof(f144,plain,(
% 0.21/0.47    r2_hidden(k4_tarski(sK0,sK7(k7_relat_1(sK2,sK1),sK0)),sK2) | ~spl9_11),
% 0.21/0.47    inference(avatar_component_clause,[],[f142])).
% 0.21/0.47  fof(f142,plain,(
% 0.21/0.47    spl9_11 <=> r2_hidden(k4_tarski(sK0,sK7(k7_relat_1(sK2,sK1),sK0)),sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 0.21/0.47  fof(f158,plain,(
% 0.21/0.47    spl9_10),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f156])).
% 0.21/0.47  fof(f156,plain,(
% 0.21/0.47    $false | spl9_10),
% 0.21/0.47    inference(resolution,[],[f139,f66])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    ( ! [X0] : (v1_relat_1(k7_relat_1(sK2,X0))) )),
% 0.21/0.47    inference(resolution,[],[f24,f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    v1_relat_1(sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    (~r2_hidden(sK0,k1_relat_1(sK2)) | ~r2_hidden(sK0,sK1) | ~r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))) & ((r2_hidden(sK0,k1_relat_1(sK2)) & r2_hidden(sK0,sK1)) | r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))) & v1_relat_1(sK2)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ? [X0,X1,X2] : ((~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))) & v1_relat_1(X2)) => ((~r2_hidden(sK0,k1_relat_1(sK2)) | ~r2_hidden(sK0,sK1) | ~r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))) & ((r2_hidden(sK0,k1_relat_1(sK2)) & r2_hidden(sK0,sK1)) | r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))) & v1_relat_1(sK2))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ? [X0,X1,X2] : ((~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))) & v1_relat_1(X2))),
% 0.21/0.47    inference(flattening,[],[f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ? [X0,X1,X2] : ((((~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) & v1_relat_1(X2))),
% 0.21/0.47    inference(nnf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,plain,(
% 0.21/0.47    ? [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <~> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) & v1_relat_1(X2))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 0.21/0.47    inference(negated_conjecture,[],[f4])).
% 0.21/0.47  fof(f4,conjecture,(
% 0.21/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).
% 0.21/0.47  fof(f139,plain,(
% 0.21/0.47    ~v1_relat_1(k7_relat_1(sK2,sK1)) | spl9_10),
% 0.21/0.47    inference(avatar_component_clause,[],[f137])).
% 0.21/0.47  fof(f145,plain,(
% 0.21/0.47    ~spl9_4 | ~spl9_10 | spl9_11 | ~spl9_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f132,f52,f142,f137,f83])).
% 0.21/0.47  fof(f132,plain,(
% 0.21/0.47    r2_hidden(k4_tarski(sK0,sK7(k7_relat_1(sK2,sK1),sK0)),sK2) | ~v1_relat_1(k7_relat_1(sK2,sK1)) | ~v1_relat_1(sK2) | ~spl9_1),
% 0.21/0.47    inference(resolution,[],[f109,f40])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ( ! [X6,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1)) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(equality_resolution,[],[f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(k4_tarski(X5,X6),X2) | k7_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f109,plain,(
% 0.21/0.47    r2_hidden(k4_tarski(sK0,sK7(k7_relat_1(sK2,sK1),sK0)),k7_relat_1(sK2,sK1)) | ~spl9_1),
% 0.21/0.47    inference(resolution,[],[f53,f43])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1))) | ~spl9_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f52])).
% 0.21/0.47  fof(f140,plain,(
% 0.21/0.47    ~spl9_4 | ~spl9_10 | spl9_2 | ~spl9_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f131,f52,f56,f137,f83])).
% 0.21/0.47  fof(f131,plain,(
% 0.21/0.47    r2_hidden(sK0,sK1) | ~v1_relat_1(k7_relat_1(sK2,sK1)) | ~v1_relat_1(sK2) | ~spl9_1),
% 0.21/0.47    inference(resolution,[],[f109,f41])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1)) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(equality_resolution,[],[f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X2) | k7_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f99,plain,(
% 0.21/0.47    spl9_4),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f98])).
% 0.21/0.47  fof(f98,plain,(
% 0.21/0.47    $false | spl9_4),
% 0.21/0.47    inference(resolution,[],[f85,f24])).
% 0.21/0.47  fof(f85,plain,(
% 0.21/0.47    ~v1_relat_1(sK2) | spl9_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f83])).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    spl9_1 | spl9_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f25,f56,f52])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    r2_hidden(sK0,sK1) | r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    spl9_1 | spl9_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f26,f60,f52])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    r2_hidden(sK0,k1_relat_1(sK2)) | r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    ~spl9_1 | ~spl9_2 | ~spl9_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f27,f60,f56,f52])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ~r2_hidden(sK0,k1_relat_1(sK2)) | ~r2_hidden(sK0,sK1) | ~r2_hidden(sK0,k1_relat_1(k7_relat_1(sK2,sK1)))),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (23973)------------------------------
% 0.21/0.47  % (23973)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (23973)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (23973)Memory used [KB]: 6140
% 0.21/0.47  % (23973)Time elapsed: 0.060 s
% 0.21/0.47  % (23973)------------------------------
% 0.21/0.47  % (23973)------------------------------
% 0.21/0.47  % (23981)Refutation not found, incomplete strategy% (23981)------------------------------
% 0.21/0.47  % (23981)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (23981)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (23960)Success in time 0.112 s
%------------------------------------------------------------------------------
