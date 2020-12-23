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
% DateTime   : Thu Dec  3 12:49:20 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 146 expanded)
%              Number of leaves         :   19 (  60 expanded)
%              Depth                    :   10
%              Number of atoms          :  268 ( 569 expanded)
%              Number of equality atoms :   29 (  86 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f191,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f70,f89,f93,f105,f160,f174,f180])).

fof(f180,plain,
    ( spl8_9
    | ~ spl8_1
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f176,f102,f59,f123])).

fof(f123,plain,
    ( spl8_9
  <=> r2_hidden(sK4(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f59,plain,
    ( spl8_1
  <=> r2_hidden(sK4(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),k9_relat_1(sK0,k1_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f102,plain,
    ( spl8_7
  <=> ! [X5,X4] :
        ( ~ r2_hidden(X4,k9_relat_1(sK0,X5))
        | r2_hidden(X4,k2_relat_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f176,plain,
    ( r2_hidden(sK4(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),k2_relat_1(sK0))
    | ~ spl8_1
    | ~ spl8_7 ),
    inference(resolution,[],[f61,f103])).

fof(f103,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X4,k9_relat_1(sK0,X5))
        | r2_hidden(X4,k2_relat_1(sK0)) )
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f102])).

fof(f61,plain,
    ( r2_hidden(sK4(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),k9_relat_1(sK0,k1_relat_1(sK0)))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f174,plain,
    ( ~ spl8_9
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f173,f68,f123])).

fof(f68,plain,
    ( spl8_3
  <=> ! [X0] : ~ r2_hidden(k4_tarski(X0,sK4(sK0,k9_relat_1(sK0,k1_relat_1(sK0)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f173,plain,
    ( ~ r2_hidden(sK4(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),k2_relat_1(sK0))
    | ~ spl8_3 ),
    inference(resolution,[],[f69,f42])).

fof(f42,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK6(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK6(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f19,f22,f21,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK4(X0,X1)),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK4(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f69,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK4(sK0,k9_relat_1(sK0,k1_relat_1(sK0)))),sK0)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f68])).

fof(f160,plain,
    ( ~ spl8_2
    | ~ spl8_6 ),
    inference(avatar_contradiction_clause,[],[f157])).

fof(f157,plain,
    ( $false
    | ~ spl8_2
    | ~ spl8_6 ),
    inference(resolution,[],[f141,f115])).

fof(f115,plain,
    ( r2_hidden(sK5(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),k1_relat_1(sK0))
    | ~ spl8_2 ),
    inference(resolution,[],[f65,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK0)
      | r2_hidden(X0,k1_relat_1(sK0)) ) ),
    inference(resolution,[],[f24,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

fof(f24,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( k2_relat_1(sK0) != k9_relat_1(sK0,k1_relat_1(sK0))
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f10])).

fof(f10,plain,
    ( ? [X0] :
        ( k2_relat_1(X0) != k9_relat_1(X0,k1_relat_1(X0))
        & v1_relat_1(X0) )
   => ( k2_relat_1(sK0) != k9_relat_1(sK0,k1_relat_1(sK0))
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0] :
      ( k2_relat_1(X0) != k9_relat_1(X0,k1_relat_1(X0))
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f65,plain,
    ( r2_hidden(k4_tarski(sK5(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),sK4(sK0,k9_relat_1(sK0,k1_relat_1(sK0)))),sK0)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl8_2
  <=> r2_hidden(k4_tarski(sK5(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),sK4(sK0,k9_relat_1(sK0,k1_relat_1(sK0)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f141,plain,
    ( ~ r2_hidden(sK5(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),k1_relat_1(sK0))
    | ~ spl8_2
    | ~ spl8_6 ),
    inference(resolution,[],[f92,f65])).

fof(f92,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK4(sK0,k9_relat_1(sK0,k1_relat_1(sK0)))),sK0)
        | ~ r2_hidden(X0,k1_relat_1(sK0)) )
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl8_6
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK0))
        | ~ r2_hidden(k4_tarski(X0,sK4(sK0,k9_relat_1(sK0,k1_relat_1(sK0)))),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f105,plain,(
    spl8_7 ),
    inference(avatar_split_clause,[],[f97,f102])).

fof(f97,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,k9_relat_1(sK0,X7))
      | r2_hidden(X6,k2_relat_1(sK0)) ) ),
    inference(resolution,[],[f53,f41])).

fof(f41,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f53,plain,(
    ! [X4,X5] :
      ( r2_hidden(k4_tarski(sK3(sK0,X4,X5),X5),sK0)
      | ~ r2_hidden(X5,k9_relat_1(sK0,X4)) ) ),
    inference(resolution,[],[f24,f40])).

fof(f40,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1,X6),X6),X0)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1,X6),X6),X0)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(X4,sK1(X0,X1,X2)),X0) )
                | ~ r2_hidden(sK1(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK2(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK1(X0,X1,X2)),X0) )
                | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ( r2_hidden(sK3(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(sK3(X0,X1,X6),X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f13,f16,f15,f14])).

fof(f14,plain,(
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
              | ~ r2_hidden(k4_tarski(X4,sK1(X0,X1,X2)),X0) )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(X5,sK1(X0,X1,X2)),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X5,sK1(X0,X1,X2)),X0) )
     => ( r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK1(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X8,X6),X0) )
     => ( r2_hidden(sK3(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(sK3(X0,X1,X6),X6),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
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
    inference(rectify,[],[f12])).

fof(f12,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_relat_1)).

fof(f93,plain,
    ( ~ spl8_4
    | spl8_6
    | spl8_1 ),
    inference(avatar_split_clause,[],[f87,f59,f91,f75])).

fof(f75,plain,
    ( spl8_4
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f87,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK0))
        | ~ r2_hidden(k4_tarski(X0,sK4(sK0,k9_relat_1(sK0,k1_relat_1(sK0)))),sK0)
        | ~ v1_relat_1(sK0) )
    | spl8_1 ),
    inference(resolution,[],[f60,f38])).

fof(f38,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f60,plain,
    ( ~ r2_hidden(sK4(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),k9_relat_1(sK0,k1_relat_1(sK0)))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f89,plain,(
    spl8_4 ),
    inference(avatar_contradiction_clause,[],[f88])).

fof(f88,plain,
    ( $false
    | spl8_4 ),
    inference(resolution,[],[f77,f24])).

fof(f77,plain,
    ( ~ v1_relat_1(sK0)
    | spl8_4 ),
    inference(avatar_component_clause,[],[f75])).

fof(f70,plain,
    ( ~ spl8_1
    | spl8_3 ),
    inference(avatar_split_clause,[],[f57,f68,f59])).

fof(f57,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(X0,sK4(sK0,k9_relat_1(sK0,k1_relat_1(sK0)))),sK0)
      | ~ r2_hidden(sK4(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),k9_relat_1(sK0,k1_relat_1(sK0))) ) ),
    inference(resolution,[],[f44,f48])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( sQ7_eqProxy(k2_relat_1(X0),X1)
      | ~ r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0)
      | ~ r2_hidden(sK4(X0,X1),X1) ) ),
    inference(equality_proxy_replacement,[],[f35,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( sQ7_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ7_eqProxy])])).

fof(f35,plain,(
    ! [X0,X3,X1] :
      ( k2_relat_1(X0) = X1
      | ~ r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0)
      | ~ r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f44,plain,(
    ~ sQ7_eqProxy(k2_relat_1(sK0),k9_relat_1(sK0,k1_relat_1(sK0))) ),
    inference(equality_proxy_replacement,[],[f25,f43])).

fof(f25,plain,(
    k2_relat_1(sK0) != k9_relat_1(sK0,k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f66,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f56,f63,f59])).

fof(f56,plain,
    ( r2_hidden(k4_tarski(sK5(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),sK4(sK0,k9_relat_1(sK0,k1_relat_1(sK0)))),sK0)
    | r2_hidden(sK4(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),k9_relat_1(sK0,k1_relat_1(sK0))) ),
    inference(resolution,[],[f44,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( sQ7_eqProxy(k2_relat_1(X0),X1)
      | r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
      | r2_hidden(sK4(X0,X1),X1) ) ),
    inference(equality_proxy_replacement,[],[f34,f43])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
      | r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:00:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.43  % (28244)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.43  % (28244)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.43  fof(f191,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(avatar_sat_refutation,[],[f66,f70,f89,f93,f105,f160,f174,f180])).
% 0.22/0.43  fof(f180,plain,(
% 0.22/0.43    spl8_9 | ~spl8_1 | ~spl8_7),
% 0.22/0.43    inference(avatar_split_clause,[],[f176,f102,f59,f123])).
% 0.22/0.43  fof(f123,plain,(
% 0.22/0.43    spl8_9 <=> r2_hidden(sK4(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),k2_relat_1(sK0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.22/0.43  fof(f59,plain,(
% 0.22/0.43    spl8_1 <=> r2_hidden(sK4(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),k9_relat_1(sK0,k1_relat_1(sK0)))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.22/0.43  fof(f102,plain,(
% 0.22/0.43    spl8_7 <=> ! [X5,X4] : (~r2_hidden(X4,k9_relat_1(sK0,X5)) | r2_hidden(X4,k2_relat_1(sK0)))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.22/0.43  fof(f176,plain,(
% 0.22/0.43    r2_hidden(sK4(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),k2_relat_1(sK0)) | (~spl8_1 | ~spl8_7)),
% 0.22/0.43    inference(resolution,[],[f61,f103])).
% 0.22/0.43  fof(f103,plain,(
% 0.22/0.43    ( ! [X4,X5] : (~r2_hidden(X4,k9_relat_1(sK0,X5)) | r2_hidden(X4,k2_relat_1(sK0))) ) | ~spl8_7),
% 0.22/0.43    inference(avatar_component_clause,[],[f102])).
% 0.22/0.43  fof(f61,plain,(
% 0.22/0.43    r2_hidden(sK4(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),k9_relat_1(sK0,k1_relat_1(sK0))) | ~spl8_1),
% 0.22/0.43    inference(avatar_component_clause,[],[f59])).
% 0.22/0.43  fof(f174,plain,(
% 0.22/0.43    ~spl8_9 | ~spl8_3),
% 0.22/0.43    inference(avatar_split_clause,[],[f173,f68,f123])).
% 0.22/0.43  fof(f68,plain,(
% 0.22/0.43    spl8_3 <=> ! [X0] : ~r2_hidden(k4_tarski(X0,sK4(sK0,k9_relat_1(sK0,k1_relat_1(sK0)))),sK0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.22/0.43  fof(f173,plain,(
% 0.22/0.43    ~r2_hidden(sK4(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),k2_relat_1(sK0)) | ~spl8_3),
% 0.22/0.43    inference(resolution,[],[f69,f42])).
% 0.22/0.43  fof(f42,plain,(
% 0.22/0.43    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 0.22/0.43    inference(equality_resolution,[],[f32])).
% 0.22/0.43  fof(f32,plain,(
% 0.22/0.43    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 0.22/0.43    inference(cnf_transformation,[],[f23])).
% 0.22/0.43  fof(f23,plain,(
% 0.22/0.43    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f19,f22,f21,f20])).
% 0.22/0.43  fof(f20,plain,(
% 0.22/0.43    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK4(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1))))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f21,plain,(
% 0.22/0.44    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK4(X0,X1)),X0) => r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f22,plain,(
% 0.22/0.44    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK6(X0,X5),X5),X0))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f19,plain,(
% 0.22/0.44    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.22/0.44    inference(rectify,[],[f18])).
% 0.22/0.44  fof(f18,plain,(
% 0.22/0.44    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 0.22/0.44    inference(nnf_transformation,[],[f2])).
% 0.22/0.44  fof(f2,axiom,(
% 0.22/0.44    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 0.22/0.44  fof(f69,plain,(
% 0.22/0.44    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK4(sK0,k9_relat_1(sK0,k1_relat_1(sK0)))),sK0)) ) | ~spl8_3),
% 0.22/0.44    inference(avatar_component_clause,[],[f68])).
% 0.22/0.44  fof(f160,plain,(
% 0.22/0.44    ~spl8_2 | ~spl8_6),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f157])).
% 0.22/0.44  fof(f157,plain,(
% 0.22/0.44    $false | (~spl8_2 | ~spl8_6)),
% 0.22/0.44    inference(resolution,[],[f141,f115])).
% 0.22/0.44  fof(f115,plain,(
% 0.22/0.44    r2_hidden(sK5(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),k1_relat_1(sK0)) | ~spl8_2),
% 0.22/0.44    inference(resolution,[],[f65,f51])).
% 0.22/0.44  fof(f51,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK0) | r2_hidden(X0,k1_relat_1(sK0))) )),
% 0.22/0.44    inference(resolution,[],[f24,f36])).
% 0.22/0.44  fof(f36,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f9])).
% 0.22/0.44  fof(f9,plain,(
% 0.22/0.44    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.22/0.44    inference(flattening,[],[f8])).
% 0.22/0.44  fof(f8,plain,(
% 0.22/0.44    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 0.22/0.44    inference(ennf_transformation,[],[f3])).
% 0.22/0.44  fof(f3,axiom,(
% 0.22/0.44    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).
% 0.22/0.44  fof(f24,plain,(
% 0.22/0.44    v1_relat_1(sK0)),
% 0.22/0.44    inference(cnf_transformation,[],[f11])).
% 0.22/0.44  fof(f11,plain,(
% 0.22/0.44    k2_relat_1(sK0) != k9_relat_1(sK0,k1_relat_1(sK0)) & v1_relat_1(sK0)),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f10])).
% 0.22/0.44  fof(f10,plain,(
% 0.22/0.44    ? [X0] : (k2_relat_1(X0) != k9_relat_1(X0,k1_relat_1(X0)) & v1_relat_1(X0)) => (k2_relat_1(sK0) != k9_relat_1(sK0,k1_relat_1(sK0)) & v1_relat_1(sK0))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f6,plain,(
% 0.22/0.44    ? [X0] : (k2_relat_1(X0) != k9_relat_1(X0,k1_relat_1(X0)) & v1_relat_1(X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f5])).
% 0.22/0.44  fof(f5,negated_conjecture,(
% 0.22/0.44    ~! [X0] : (v1_relat_1(X0) => k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)))),
% 0.22/0.44    inference(negated_conjecture,[],[f4])).
% 0.22/0.44  fof(f4,conjecture,(
% 0.22/0.44    ! [X0] : (v1_relat_1(X0) => k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 0.22/0.44  fof(f65,plain,(
% 0.22/0.44    r2_hidden(k4_tarski(sK5(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),sK4(sK0,k9_relat_1(sK0,k1_relat_1(sK0)))),sK0) | ~spl8_2),
% 0.22/0.44    inference(avatar_component_clause,[],[f63])).
% 0.22/0.44  fof(f63,plain,(
% 0.22/0.44    spl8_2 <=> r2_hidden(k4_tarski(sK5(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),sK4(sK0,k9_relat_1(sK0,k1_relat_1(sK0)))),sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.22/0.44  fof(f141,plain,(
% 0.22/0.44    ~r2_hidden(sK5(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),k1_relat_1(sK0)) | (~spl8_2 | ~spl8_6)),
% 0.22/0.44    inference(resolution,[],[f92,f65])).
% 0.22/0.44  fof(f92,plain,(
% 0.22/0.44    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK4(sK0,k9_relat_1(sK0,k1_relat_1(sK0)))),sK0) | ~r2_hidden(X0,k1_relat_1(sK0))) ) | ~spl8_6),
% 0.22/0.44    inference(avatar_component_clause,[],[f91])).
% 0.22/0.44  fof(f91,plain,(
% 0.22/0.44    spl8_6 <=> ! [X0] : (~r2_hidden(X0,k1_relat_1(sK0)) | ~r2_hidden(k4_tarski(X0,sK4(sK0,k9_relat_1(sK0,k1_relat_1(sK0)))),sK0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.22/0.44  fof(f105,plain,(
% 0.22/0.44    spl8_7),
% 0.22/0.44    inference(avatar_split_clause,[],[f97,f102])).
% 0.22/0.44  fof(f97,plain,(
% 0.22/0.44    ( ! [X6,X7] : (~r2_hidden(X6,k9_relat_1(sK0,X7)) | r2_hidden(X6,k2_relat_1(sK0))) )),
% 0.22/0.44    inference(resolution,[],[f53,f41])).
% 0.22/0.44  fof(f41,plain,(
% 0.22/0.44    ( ! [X6,X0,X5] : (r2_hidden(X5,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X6,X5),X0)) )),
% 0.22/0.44    inference(equality_resolution,[],[f33])).
% 0.22/0.44  fof(f33,plain,(
% 0.22/0.44    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 0.22/0.44    inference(cnf_transformation,[],[f23])).
% 0.22/0.44  fof(f53,plain,(
% 0.22/0.44    ( ! [X4,X5] : (r2_hidden(k4_tarski(sK3(sK0,X4,X5),X5),sK0) | ~r2_hidden(X5,k9_relat_1(sK0,X4))) )),
% 0.22/0.44    inference(resolution,[],[f24,f40])).
% 0.22/0.44  fof(f40,plain,(
% 0.22/0.44    ( ! [X6,X0,X1] : (r2_hidden(k4_tarski(sK3(X0,X1,X6),X6),X0) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.44    inference(equality_resolution,[],[f26])).
% 0.22/0.44  fof(f26,plain,(
% 0.22/0.44    ( ! [X6,X2,X0,X1] : (r2_hidden(k4_tarski(sK3(X0,X1,X6),X6),X0) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f17])).
% 0.22/0.44  fof(f17,plain,(
% 0.22/0.44    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,sK1(X0,X1,X2)),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK1(X0,X1,X2)),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0))) & ((r2_hidden(sK3(X0,X1,X6),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X6),X6),X0)) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f13,f16,f15,f14])).
% 0.22/0.44  fof(f14,plain,(
% 0.22/0.44    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X3),X0)) | r2_hidden(X3,X2))) => ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,sK1(X0,X1,X2)),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,sK1(X0,X1,X2)),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f15,plain,(
% 0.22/0.44    ! [X2,X1,X0] : (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,sK1(X0,X1,X2)),X0)) => (r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK1(X0,X1,X2)),X0)))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f16,plain,(
% 0.22/0.44    ! [X6,X1,X0] : (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X8,X6),X0)) => (r2_hidden(sK3(X0,X1,X6),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X6),X6),X0)))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f13,plain,(
% 0.22/0.44    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X3),X0)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0))) & (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X8,X6),X0)) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.22/0.44    inference(rectify,[],[f12])).
% 0.22/0.44  fof(f12,plain,(
% 0.22/0.44    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.22/0.44    inference(nnf_transformation,[],[f7])).
% 0.22/0.44  fof(f7,plain,(
% 0.22/0.44    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))) | ~v1_relat_1(X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f1])).
% 0.22/0.44  fof(f1,axiom,(
% 0.22/0.44    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_relat_1)).
% 0.22/0.44  fof(f93,plain,(
% 0.22/0.44    ~spl8_4 | spl8_6 | spl8_1),
% 0.22/0.44    inference(avatar_split_clause,[],[f87,f59,f91,f75])).
% 0.22/0.44  fof(f75,plain,(
% 0.22/0.44    spl8_4 <=> v1_relat_1(sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.22/0.44  fof(f87,plain,(
% 0.22/0.44    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK0)) | ~r2_hidden(k4_tarski(X0,sK4(sK0,k9_relat_1(sK0,k1_relat_1(sK0)))),sK0) | ~v1_relat_1(sK0)) ) | spl8_1),
% 0.22/0.44    inference(resolution,[],[f60,f38])).
% 0.22/0.44  fof(f38,plain,(
% 0.22/0.44    ( ! [X6,X0,X7,X1] : (r2_hidden(X6,k9_relat_1(X0,X1)) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0) | ~v1_relat_1(X0)) )),
% 0.22/0.44    inference(equality_resolution,[],[f28])).
% 0.22/0.44  fof(f28,plain,(
% 0.22/0.44    ( ! [X6,X2,X0,X7,X1] : (r2_hidden(X6,X2) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0) | k9_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f17])).
% 0.22/0.44  fof(f60,plain,(
% 0.22/0.44    ~r2_hidden(sK4(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),k9_relat_1(sK0,k1_relat_1(sK0))) | spl8_1),
% 0.22/0.44    inference(avatar_component_clause,[],[f59])).
% 0.22/0.44  fof(f89,plain,(
% 0.22/0.44    spl8_4),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f88])).
% 0.22/0.44  fof(f88,plain,(
% 0.22/0.44    $false | spl8_4),
% 0.22/0.44    inference(resolution,[],[f77,f24])).
% 0.22/0.44  fof(f77,plain,(
% 0.22/0.44    ~v1_relat_1(sK0) | spl8_4),
% 0.22/0.44    inference(avatar_component_clause,[],[f75])).
% 0.22/0.44  fof(f70,plain,(
% 0.22/0.44    ~spl8_1 | spl8_3),
% 0.22/0.44    inference(avatar_split_clause,[],[f57,f68,f59])).
% 0.22/0.44  fof(f57,plain,(
% 0.22/0.44    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK4(sK0,k9_relat_1(sK0,k1_relat_1(sK0)))),sK0) | ~r2_hidden(sK4(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),k9_relat_1(sK0,k1_relat_1(sK0)))) )),
% 0.22/0.44    inference(resolution,[],[f44,f48])).
% 0.22/0.44  fof(f48,plain,(
% 0.22/0.44    ( ! [X0,X3,X1] : (sQ7_eqProxy(k2_relat_1(X0),X1) | ~r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0) | ~r2_hidden(sK4(X0,X1),X1)) )),
% 0.22/0.44    inference(equality_proxy_replacement,[],[f35,f43])).
% 0.22/0.44  fof(f43,plain,(
% 0.22/0.44    ! [X1,X0] : (sQ7_eqProxy(X0,X1) <=> X0 = X1)),
% 0.22/0.44    introduced(equality_proxy_definition,[new_symbols(naming,[sQ7_eqProxy])])).
% 0.22/0.44  fof(f35,plain,(
% 0.22/0.44    ( ! [X0,X3,X1] : (k2_relat_1(X0) = X1 | ~r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0) | ~r2_hidden(sK4(X0,X1),X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f23])).
% 0.22/0.44  fof(f44,plain,(
% 0.22/0.44    ~sQ7_eqProxy(k2_relat_1(sK0),k9_relat_1(sK0,k1_relat_1(sK0)))),
% 0.22/0.44    inference(equality_proxy_replacement,[],[f25,f43])).
% 0.22/0.44  fof(f25,plain,(
% 0.22/0.44    k2_relat_1(sK0) != k9_relat_1(sK0,k1_relat_1(sK0))),
% 0.22/0.44    inference(cnf_transformation,[],[f11])).
% 0.22/0.44  fof(f66,plain,(
% 0.22/0.44    spl8_1 | spl8_2),
% 0.22/0.44    inference(avatar_split_clause,[],[f56,f63,f59])).
% 0.22/0.44  fof(f56,plain,(
% 0.22/0.44    r2_hidden(k4_tarski(sK5(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),sK4(sK0,k9_relat_1(sK0,k1_relat_1(sK0)))),sK0) | r2_hidden(sK4(sK0,k9_relat_1(sK0,k1_relat_1(sK0))),k9_relat_1(sK0,k1_relat_1(sK0)))),
% 0.22/0.44    inference(resolution,[],[f44,f49])).
% 0.22/0.44  fof(f49,plain,(
% 0.22/0.44    ( ! [X0,X1] : (sQ7_eqProxy(k2_relat_1(X0),X1) | r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1)) )),
% 0.22/0.44    inference(equality_proxy_replacement,[],[f34,f43])).
% 0.22/0.44  fof(f34,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f23])).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (28244)------------------------------
% 0.22/0.44  % (28244)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (28244)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (28244)Memory used [KB]: 6140
% 0.22/0.44  % (28244)Time elapsed: 0.009 s
% 0.22/0.44  % (28244)------------------------------
% 0.22/0.44  % (28244)------------------------------
% 0.22/0.44  % (28231)Success in time 0.077 s
%------------------------------------------------------------------------------
