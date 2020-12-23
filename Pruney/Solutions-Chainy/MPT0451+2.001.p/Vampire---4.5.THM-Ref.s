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
% DateTime   : Thu Dec  3 12:47:22 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 222 expanded)
%              Number of leaves         :   25 (  99 expanded)
%              Depth                    :    9
%              Number of atoms          :  362 ( 911 expanded)
%              Number of equality atoms :   47 ( 159 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f359,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f77,f81,f82,f126,f203,f234,f325,f335,f336,f338,f355,f356])).

fof(f356,plain,
    ( spl10_9
    | spl10_1
    | ~ spl10_11 ),
    inference(avatar_split_clause,[],[f343,f113,f59,f104])).

fof(f104,plain,
    ( spl10_9
  <=> r2_hidden(sK3(sK0,k1_relat_1(k4_relat_1(sK0))),k1_relat_1(k4_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f59,plain,
    ( spl10_1
  <=> sQ9_eqProxy(k2_relat_1(sK0),k1_relat_1(k4_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f113,plain,
    ( spl10_11
  <=> ! [X0] : ~ r2_hidden(k4_tarski(X0,sK3(sK0,k1_relat_1(k4_relat_1(sK0)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f343,plain,
    ( sQ9_eqProxy(k2_relat_1(sK0),k1_relat_1(k4_relat_1(sK0)))
    | r2_hidden(sK3(sK0,k1_relat_1(k4_relat_1(sK0))),k1_relat_1(k4_relat_1(sK0)))
    | ~ spl10_11 ),
    inference(resolution,[],[f114,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( sQ9_eqProxy(k2_relat_1(X0),X1)
      | r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(equality_proxy_replacement,[],[f37,f49])).

fof(f49,plain,(
    ! [X1,X0] :
      ( sQ9_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ9_eqProxy])])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f17,f20,f19,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
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
    inference(rectify,[],[f16])).

fof(f16,plain,(
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

fof(f114,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK3(sK0,k1_relat_1(k4_relat_1(sK0)))),sK0)
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f113])).

fof(f355,plain,
    ( ~ spl10_9
    | ~ spl10_4
    | ~ spl10_11 ),
    inference(avatar_split_clause,[],[f353,f113,f75,f104])).

fof(f75,plain,
    ( spl10_4
  <=> ! [X1,X0] :
        ( r2_hidden(k4_tarski(X0,X1),sK0)
        | ~ r2_hidden(k4_tarski(X1,X0),k4_relat_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f353,plain,
    ( ~ r2_hidden(sK3(sK0,k1_relat_1(k4_relat_1(sK0))),k1_relat_1(k4_relat_1(sK0)))
    | ~ spl10_4
    | ~ spl10_11 ),
    inference(resolution,[],[f341,f48])).

fof(f48,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK6(X0,X1),X3),X0)
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0)
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f23,f26,f25,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK6(X0,X1),X3),X0)
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0)
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f341,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK3(sK0,k1_relat_1(k4_relat_1(sK0))),X0),k4_relat_1(sK0))
    | ~ spl10_4
    | ~ spl10_11 ),
    inference(resolution,[],[f114,f76])).

fof(f76,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,X1),sK0)
        | ~ r2_hidden(k4_tarski(X1,X0),k4_relat_1(sK0)) )
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f75])).

fof(f338,plain,
    ( spl10_14
    | spl10_2
    | ~ spl10_12 ),
    inference(avatar_split_clause,[],[f204,f119,f63,f128])).

fof(f128,plain,
    ( spl10_14
  <=> ! [X0] : ~ r2_hidden(k4_tarski(sK6(sK0,k2_relat_1(k4_relat_1(sK0))),X0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f63,plain,
    ( spl10_2
  <=> sQ9_eqProxy(k1_relat_1(sK0),k2_relat_1(k4_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f119,plain,
    ( spl10_12
  <=> r2_hidden(sK6(sK0,k2_relat_1(k4_relat_1(sK0))),k2_relat_1(k4_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f204,plain,
    ( ! [X0] :
        ( sQ9_eqProxy(k1_relat_1(sK0),k2_relat_1(k4_relat_1(sK0)))
        | ~ r2_hidden(k4_tarski(sK6(sK0,k2_relat_1(k4_relat_1(sK0))),X0),sK0) )
    | ~ spl10_12 ),
    inference(resolution,[],[f121,f55])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( sQ9_eqProxy(k1_relat_1(X0),X1)
      | ~ r2_hidden(k4_tarski(sK6(X0,X1),X3),X0)
      | ~ r2_hidden(sK6(X0,X1),X1) ) ),
    inference(equality_proxy_replacement,[],[f42,f49])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( k1_relat_1(X0) = X1
      | ~ r2_hidden(k4_tarski(sK6(X0,X1),X3),X0)
      | ~ r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f121,plain,
    ( r2_hidden(sK6(sK0,k2_relat_1(k4_relat_1(sK0))),k2_relat_1(k4_relat_1(sK0)))
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f119])).

fof(f336,plain,
    ( spl10_11
    | spl10_1
    | ~ spl10_9 ),
    inference(avatar_split_clause,[],[f245,f104,f59,f113])).

fof(f245,plain,
    ( ! [X0] :
        ( sQ9_eqProxy(k2_relat_1(sK0),k1_relat_1(k4_relat_1(sK0)))
        | ~ r2_hidden(k4_tarski(X0,sK3(sK0,k1_relat_1(k4_relat_1(sK0)))),sK0) )
    | ~ spl10_9 ),
    inference(resolution,[],[f106,f53])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( sQ9_eqProxy(k2_relat_1(X0),X1)
      | ~ r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(equality_proxy_replacement,[],[f38,f49])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( k2_relat_1(X0) = X1
      | ~ r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f106,plain,
    ( r2_hidden(sK3(sK0,k1_relat_1(k4_relat_1(sK0))),k1_relat_1(k4_relat_1(sK0)))
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f104])).

fof(f335,plain,
    ( spl10_12
    | ~ spl10_5
    | ~ spl10_13 ),
    inference(avatar_split_clause,[],[f330,f123,f79,f119])).

fof(f79,plain,
    ( spl10_5
  <=> ! [X3,X2] :
        ( r2_hidden(k4_tarski(X2,X3),k4_relat_1(sK0))
        | ~ r2_hidden(k4_tarski(X3,X2),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f123,plain,
    ( spl10_13
  <=> r2_hidden(k4_tarski(sK6(sK0,k2_relat_1(k4_relat_1(sK0))),sK7(sK0,k2_relat_1(k4_relat_1(sK0)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f330,plain,
    ( r2_hidden(sK6(sK0,k2_relat_1(k4_relat_1(sK0))),k2_relat_1(k4_relat_1(sK0)))
    | ~ spl10_5
    | ~ spl10_13 ),
    inference(resolution,[],[f125,f178])).

fof(f178,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(k4_tarski(X4,X5),sK0)
        | r2_hidden(X4,k2_relat_1(k4_relat_1(sK0))) )
    | ~ spl10_5 ),
    inference(resolution,[],[f80,f45])).

fof(f45,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f80,plain,
    ( ! [X2,X3] :
        ( r2_hidden(k4_tarski(X2,X3),k4_relat_1(sK0))
        | ~ r2_hidden(k4_tarski(X3,X2),sK0) )
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f79])).

fof(f125,plain,
    ( r2_hidden(k4_tarski(sK6(sK0,k2_relat_1(k4_relat_1(sK0))),sK7(sK0,k2_relat_1(k4_relat_1(sK0)))),sK0)
    | ~ spl10_13 ),
    inference(avatar_component_clause,[],[f123])).

fof(f325,plain,
    ( ~ spl10_12
    | ~ spl10_4
    | ~ spl10_14 ),
    inference(avatar_split_clause,[],[f320,f128,f75,f119])).

fof(f320,plain,
    ( ~ r2_hidden(sK6(sK0,k2_relat_1(k4_relat_1(sK0))),k2_relat_1(k4_relat_1(sK0)))
    | ~ spl10_4
    | ~ spl10_14 ),
    inference(resolution,[],[f207,f46])).

fof(f46,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f207,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK6(sK0,k2_relat_1(k4_relat_1(sK0)))),k4_relat_1(sK0))
    | ~ spl10_4
    | ~ spl10_14 ),
    inference(resolution,[],[f129,f76])).

fof(f129,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK6(sK0,k2_relat_1(k4_relat_1(sK0))),X0),sK0)
    | ~ spl10_14 ),
    inference(avatar_component_clause,[],[f128])).

fof(f234,plain,
    ( ~ spl10_22
    | ~ spl10_3
    | spl10_11
    | spl10_9 ),
    inference(avatar_split_clause,[],[f230,f104,f113,f71,f194])).

fof(f194,plain,
    ( spl10_22
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f71,plain,
    ( spl10_3
  <=> v1_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f230,plain,
    ( ! [X1] :
        ( ~ r2_hidden(k4_tarski(X1,sK3(sK0,k1_relat_1(k4_relat_1(sK0)))),sK0)
        | ~ v1_relat_1(k4_relat_1(sK0))
        | ~ v1_relat_1(sK0) )
    | spl10_9 ),
    inference(resolution,[],[f150,f43])).

fof(f43,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X4),X0)
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r2_hidden(k4_tarski(X5,X4),X0)
      | k4_relat_1(X0) != X1
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ( ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
                  | ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) )
                & ( r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
                  | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X5,X4),X0) )
                  & ( r2_hidden(k4_tarski(X5,X4),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f13,f14])).

fof(f14,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r2_hidden(k4_tarski(X3,X2),X0)
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
          | ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) )
        & ( r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
          | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X5,X4),X0) )
                  & ( r2_hidden(k4_tarski(X5,X4),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
            & ( ! [X2,X3] :
                  ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X3,X2),X0) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_relat_1)).

fof(f150,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK3(sK0,k1_relat_1(k4_relat_1(sK0))),X0),k4_relat_1(sK0))
    | spl10_9 ),
    inference(resolution,[],[f105,f47])).

fof(f47,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f105,plain,
    ( ~ r2_hidden(sK3(sK0,k1_relat_1(k4_relat_1(sK0))),k1_relat_1(k4_relat_1(sK0)))
    | spl10_9 ),
    inference(avatar_component_clause,[],[f104])).

fof(f203,plain,(
    spl10_22 ),
    inference(avatar_contradiction_clause,[],[f202])).

fof(f202,plain,
    ( $false
    | spl10_22 ),
    inference(resolution,[],[f196,f28])).

fof(f28,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ( k1_relat_1(sK0) != k2_relat_1(k4_relat_1(sK0))
      | k2_relat_1(sK0) != k1_relat_1(k4_relat_1(sK0)) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f10])).

fof(f10,plain,
    ( ? [X0] :
        ( ( k1_relat_1(X0) != k2_relat_1(k4_relat_1(X0))
          | k2_relat_1(X0) != k1_relat_1(k4_relat_1(X0)) )
        & v1_relat_1(X0) )
   => ( ( k1_relat_1(sK0) != k2_relat_1(k4_relat_1(sK0))
        | k2_relat_1(sK0) != k1_relat_1(k4_relat_1(sK0)) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ( k1_relat_1(X0) != k2_relat_1(k4_relat_1(X0))
        | k2_relat_1(X0) != k1_relat_1(k4_relat_1(X0)) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f196,plain,
    ( ~ v1_relat_1(sK0)
    | spl10_22 ),
    inference(avatar_component_clause,[],[f194])).

fof(f126,plain,
    ( spl10_12
    | spl10_13
    | spl10_2 ),
    inference(avatar_split_clause,[],[f116,f63,f123,f119])).

fof(f116,plain,
    ( r2_hidden(k4_tarski(sK6(sK0,k2_relat_1(k4_relat_1(sK0))),sK7(sK0,k2_relat_1(k4_relat_1(sK0)))),sK0)
    | r2_hidden(sK6(sK0,k2_relat_1(k4_relat_1(sK0))),k2_relat_1(k4_relat_1(sK0)))
    | spl10_2 ),
    inference(resolution,[],[f65,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( sQ9_eqProxy(k1_relat_1(X0),X1)
      | r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0)
      | r2_hidden(sK6(X0,X1),X1) ) ),
    inference(equality_proxy_replacement,[],[f41,f49])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0)
      | r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f65,plain,
    ( ~ sQ9_eqProxy(k1_relat_1(sK0),k2_relat_1(k4_relat_1(sK0)))
    | spl10_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f82,plain,(
    spl10_3 ),
    inference(avatar_split_clause,[],[f69,f71])).

fof(f69,plain,(
    v1_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f28,f30])).

fof(f30,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f81,plain,
    ( ~ spl10_3
    | spl10_5 ),
    inference(avatar_split_clause,[],[f68,f79,f71])).

fof(f68,plain,(
    ! [X2,X3] :
      ( r2_hidden(k4_tarski(X2,X3),k4_relat_1(sK0))
      | ~ r2_hidden(k4_tarski(X3,X2),sK0)
      | ~ v1_relat_1(k4_relat_1(sK0)) ) ),
    inference(resolution,[],[f28,f43])).

fof(f77,plain,
    ( ~ spl10_3
    | spl10_4 ),
    inference(avatar_split_clause,[],[f67,f75,f71])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),sK0)
      | ~ r2_hidden(k4_tarski(X1,X0),k4_relat_1(sK0))
      | ~ v1_relat_1(k4_relat_1(sK0)) ) ),
    inference(resolution,[],[f28,f44])).

fof(f44,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X5,X4),X0)
      | ~ r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0))
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X4),X0)
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | k4_relat_1(X0) != X1
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f66,plain,
    ( ~ spl10_1
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f50,f63,f59])).

fof(f50,plain,
    ( ~ sQ9_eqProxy(k1_relat_1(sK0),k2_relat_1(k4_relat_1(sK0)))
    | ~ sQ9_eqProxy(k2_relat_1(sK0),k1_relat_1(k4_relat_1(sK0))) ),
    inference(equality_proxy_replacement,[],[f29,f49,f49])).

fof(f29,plain,
    ( k1_relat_1(sK0) != k2_relat_1(k4_relat_1(sK0))
    | k2_relat_1(sK0) != k1_relat_1(k4_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:04:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (27738)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.48  % (27744)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.50  % (27733)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.51  % (27732)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (27730)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (27732)Refutation not found, incomplete strategy% (27732)------------------------------
% 0.20/0.52  % (27732)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (27732)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (27732)Memory used [KB]: 10618
% 0.20/0.52  % (27732)Time elapsed: 0.103 s
% 0.20/0.52  % (27732)------------------------------
% 0.20/0.52  % (27732)------------------------------
% 0.20/0.52  % (27730)Refutation not found, incomplete strategy% (27730)------------------------------
% 0.20/0.52  % (27730)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (27730)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (27730)Memory used [KB]: 10618
% 0.20/0.52  % (27730)Time elapsed: 0.085 s
% 0.20/0.52  % (27730)------------------------------
% 0.20/0.52  % (27730)------------------------------
% 0.20/0.52  % (27749)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.52  % (27749)Refutation not found, incomplete strategy% (27749)------------------------------
% 0.20/0.52  % (27749)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (27749)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (27749)Memory used [KB]: 10618
% 0.20/0.52  % (27749)Time elapsed: 0.085 s
% 0.20/0.52  % (27749)------------------------------
% 0.20/0.52  % (27749)------------------------------
% 0.20/0.52  % (27736)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.52  % (27731)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.53  % (27742)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.53  % (27746)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.53  % (27729)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.53  % (27737)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.53  % (27729)Refutation not found, incomplete strategy% (27729)------------------------------
% 0.20/0.53  % (27729)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (27729)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (27729)Memory used [KB]: 6140
% 0.20/0.53  % (27729)Time elapsed: 0.104 s
% 0.20/0.53  % (27729)------------------------------
% 0.20/0.53  % (27729)------------------------------
% 0.20/0.53  % (27748)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.53  % (27740)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.53  % (27743)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.53  % (27734)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.54  % (27745)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.54  % (27735)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.54  % (27741)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.55  % (27741)Refutation found. Thanks to Tanya!
% 0.20/0.55  % SZS status Theorem for theBenchmark
% 0.20/0.55  % SZS output start Proof for theBenchmark
% 0.20/0.55  fof(f359,plain,(
% 0.20/0.55    $false),
% 0.20/0.55    inference(avatar_sat_refutation,[],[f66,f77,f81,f82,f126,f203,f234,f325,f335,f336,f338,f355,f356])).
% 0.20/0.55  fof(f356,plain,(
% 0.20/0.55    spl10_9 | spl10_1 | ~spl10_11),
% 0.20/0.55    inference(avatar_split_clause,[],[f343,f113,f59,f104])).
% 0.20/0.55  fof(f104,plain,(
% 0.20/0.55    spl10_9 <=> r2_hidden(sK3(sK0,k1_relat_1(k4_relat_1(sK0))),k1_relat_1(k4_relat_1(sK0)))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 0.20/0.55  fof(f59,plain,(
% 0.20/0.55    spl10_1 <=> sQ9_eqProxy(k2_relat_1(sK0),k1_relat_1(k4_relat_1(sK0)))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.20/0.55  fof(f113,plain,(
% 0.20/0.55    spl10_11 <=> ! [X0] : ~r2_hidden(k4_tarski(X0,sK3(sK0,k1_relat_1(k4_relat_1(sK0)))),sK0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).
% 0.20/0.55  fof(f343,plain,(
% 0.20/0.55    sQ9_eqProxy(k2_relat_1(sK0),k1_relat_1(k4_relat_1(sK0))) | r2_hidden(sK3(sK0,k1_relat_1(k4_relat_1(sK0))),k1_relat_1(k4_relat_1(sK0))) | ~spl10_11),
% 0.20/0.55    inference(resolution,[],[f114,f54])).
% 0.20/0.55  fof(f54,plain,(
% 0.20/0.55    ( ! [X0,X1] : (sQ9_eqProxy(k2_relat_1(X0),X1) | r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)) )),
% 0.20/0.55    inference(equality_proxy_replacement,[],[f37,f49])).
% 0.20/0.55  fof(f49,plain,(
% 0.20/0.55    ! [X1,X0] : (sQ9_eqProxy(X0,X1) <=> X0 = X1)),
% 0.20/0.55    introduced(equality_proxy_definition,[new_symbols(naming,[sQ9_eqProxy])])).
% 0.20/0.55  fof(f37,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f21])).
% 0.20/0.55  fof(f21,plain,(
% 0.20/0.55    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f17,f20,f19,f18])).
% 0.20/0.55  fof(f18,plain,(
% 0.20/0.55    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f19,plain,(
% 0.20/0.55    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0) => r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f20,plain,(
% 0.20/0.55    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK5(X0,X5),X5),X0))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f17,plain,(
% 0.20/0.55    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.20/0.55    inference(rectify,[],[f16])).
% 0.20/0.55  fof(f16,plain,(
% 0.20/0.55    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 0.20/0.55    inference(nnf_transformation,[],[f2])).
% 0.20/0.55  fof(f2,axiom,(
% 0.20/0.55    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 0.20/0.55  fof(f114,plain,(
% 0.20/0.55    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK3(sK0,k1_relat_1(k4_relat_1(sK0)))),sK0)) ) | ~spl10_11),
% 0.20/0.55    inference(avatar_component_clause,[],[f113])).
% 0.20/0.55  fof(f355,plain,(
% 0.20/0.55    ~spl10_9 | ~spl10_4 | ~spl10_11),
% 0.20/0.55    inference(avatar_split_clause,[],[f353,f113,f75,f104])).
% 0.20/0.55  fof(f75,plain,(
% 0.20/0.55    spl10_4 <=> ! [X1,X0] : (r2_hidden(k4_tarski(X0,X1),sK0) | ~r2_hidden(k4_tarski(X1,X0),k4_relat_1(sK0)))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 0.20/0.55  fof(f353,plain,(
% 0.20/0.55    ~r2_hidden(sK3(sK0,k1_relat_1(k4_relat_1(sK0))),k1_relat_1(k4_relat_1(sK0))) | (~spl10_4 | ~spl10_11)),
% 0.20/0.55    inference(resolution,[],[f341,f48])).
% 0.20/0.55  fof(f48,plain,(
% 0.20/0.55    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 0.20/0.55    inference(equality_resolution,[],[f39])).
% 0.20/0.55  fof(f39,plain,(
% 0.20/0.55    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 0.20/0.55    inference(cnf_transformation,[],[f27])).
% 0.20/0.55  fof(f27,plain,(
% 0.20/0.55    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK6(X0,X1),X3),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f23,f26,f25,f24])).
% 0.20/0.55  fof(f24,plain,(
% 0.20/0.55    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK6(X0,X1),X3),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0) | r2_hidden(sK6(X0,X1),X1))))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f25,plain,(
% 0.20/0.55    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f26,plain,(
% 0.20/0.55    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f23,plain,(
% 0.20/0.55    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.20/0.55    inference(rectify,[],[f22])).
% 0.20/0.55  fof(f22,plain,(
% 0.20/0.55    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 0.20/0.55    inference(nnf_transformation,[],[f1])).
% 0.20/0.55  fof(f1,axiom,(
% 0.20/0.55    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 0.20/0.55  fof(f341,plain,(
% 0.20/0.55    ( ! [X0] : (~r2_hidden(k4_tarski(sK3(sK0,k1_relat_1(k4_relat_1(sK0))),X0),k4_relat_1(sK0))) ) | (~spl10_4 | ~spl10_11)),
% 0.20/0.55    inference(resolution,[],[f114,f76])).
% 0.20/0.55  fof(f76,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,X1),sK0) | ~r2_hidden(k4_tarski(X1,X0),k4_relat_1(sK0))) ) | ~spl10_4),
% 0.20/0.55    inference(avatar_component_clause,[],[f75])).
% 0.20/0.55  fof(f338,plain,(
% 0.20/0.55    spl10_14 | spl10_2 | ~spl10_12),
% 0.20/0.55    inference(avatar_split_clause,[],[f204,f119,f63,f128])).
% 0.20/0.55  fof(f128,plain,(
% 0.20/0.55    spl10_14 <=> ! [X0] : ~r2_hidden(k4_tarski(sK6(sK0,k2_relat_1(k4_relat_1(sK0))),X0),sK0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).
% 0.20/0.55  fof(f63,plain,(
% 0.20/0.55    spl10_2 <=> sQ9_eqProxy(k1_relat_1(sK0),k2_relat_1(k4_relat_1(sK0)))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.20/0.55  fof(f119,plain,(
% 0.20/0.55    spl10_12 <=> r2_hidden(sK6(sK0,k2_relat_1(k4_relat_1(sK0))),k2_relat_1(k4_relat_1(sK0)))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).
% 0.20/0.55  fof(f204,plain,(
% 0.20/0.55    ( ! [X0] : (sQ9_eqProxy(k1_relat_1(sK0),k2_relat_1(k4_relat_1(sK0))) | ~r2_hidden(k4_tarski(sK6(sK0,k2_relat_1(k4_relat_1(sK0))),X0),sK0)) ) | ~spl10_12),
% 0.20/0.55    inference(resolution,[],[f121,f55])).
% 0.20/0.55  fof(f55,plain,(
% 0.20/0.55    ( ! [X0,X3,X1] : (sQ9_eqProxy(k1_relat_1(X0),X1) | ~r2_hidden(k4_tarski(sK6(X0,X1),X3),X0) | ~r2_hidden(sK6(X0,X1),X1)) )),
% 0.20/0.55    inference(equality_proxy_replacement,[],[f42,f49])).
% 0.20/0.55  fof(f42,plain,(
% 0.20/0.55    ( ! [X0,X3,X1] : (k1_relat_1(X0) = X1 | ~r2_hidden(k4_tarski(sK6(X0,X1),X3),X0) | ~r2_hidden(sK6(X0,X1),X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f27])).
% 0.20/0.55  fof(f121,plain,(
% 0.20/0.55    r2_hidden(sK6(sK0,k2_relat_1(k4_relat_1(sK0))),k2_relat_1(k4_relat_1(sK0))) | ~spl10_12),
% 0.20/0.55    inference(avatar_component_clause,[],[f119])).
% 0.20/0.55  fof(f336,plain,(
% 0.20/0.55    spl10_11 | spl10_1 | ~spl10_9),
% 0.20/0.55    inference(avatar_split_clause,[],[f245,f104,f59,f113])).
% 0.20/0.55  fof(f245,plain,(
% 0.20/0.55    ( ! [X0] : (sQ9_eqProxy(k2_relat_1(sK0),k1_relat_1(k4_relat_1(sK0))) | ~r2_hidden(k4_tarski(X0,sK3(sK0,k1_relat_1(k4_relat_1(sK0)))),sK0)) ) | ~spl10_9),
% 0.20/0.55    inference(resolution,[],[f106,f53])).
% 0.20/0.55  fof(f53,plain,(
% 0.20/0.55    ( ! [X0,X3,X1] : (sQ9_eqProxy(k2_relat_1(X0),X1) | ~r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0) | ~r2_hidden(sK3(X0,X1),X1)) )),
% 0.20/0.55    inference(equality_proxy_replacement,[],[f38,f49])).
% 0.20/0.55  fof(f38,plain,(
% 0.20/0.55    ( ! [X0,X3,X1] : (k2_relat_1(X0) = X1 | ~r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0) | ~r2_hidden(sK3(X0,X1),X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f21])).
% 0.20/0.55  fof(f106,plain,(
% 0.20/0.55    r2_hidden(sK3(sK0,k1_relat_1(k4_relat_1(sK0))),k1_relat_1(k4_relat_1(sK0))) | ~spl10_9),
% 0.20/0.55    inference(avatar_component_clause,[],[f104])).
% 0.20/0.55  fof(f335,plain,(
% 0.20/0.55    spl10_12 | ~spl10_5 | ~spl10_13),
% 0.20/0.55    inference(avatar_split_clause,[],[f330,f123,f79,f119])).
% 0.20/0.55  fof(f79,plain,(
% 0.20/0.55    spl10_5 <=> ! [X3,X2] : (r2_hidden(k4_tarski(X2,X3),k4_relat_1(sK0)) | ~r2_hidden(k4_tarski(X3,X2),sK0))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 0.20/0.55  fof(f123,plain,(
% 0.20/0.55    spl10_13 <=> r2_hidden(k4_tarski(sK6(sK0,k2_relat_1(k4_relat_1(sK0))),sK7(sK0,k2_relat_1(k4_relat_1(sK0)))),sK0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).
% 0.20/0.55  fof(f330,plain,(
% 0.20/0.55    r2_hidden(sK6(sK0,k2_relat_1(k4_relat_1(sK0))),k2_relat_1(k4_relat_1(sK0))) | (~spl10_5 | ~spl10_13)),
% 0.20/0.55    inference(resolution,[],[f125,f178])).
% 0.20/0.55  fof(f178,plain,(
% 0.20/0.55    ( ! [X4,X5] : (~r2_hidden(k4_tarski(X4,X5),sK0) | r2_hidden(X4,k2_relat_1(k4_relat_1(sK0)))) ) | ~spl10_5),
% 0.20/0.55    inference(resolution,[],[f80,f45])).
% 0.20/0.55  fof(f45,plain,(
% 0.20/0.55    ( ! [X6,X0,X5] : (r2_hidden(X5,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X6,X5),X0)) )),
% 0.20/0.55    inference(equality_resolution,[],[f36])).
% 0.20/0.55  fof(f36,plain,(
% 0.20/0.55    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 0.20/0.55    inference(cnf_transformation,[],[f21])).
% 0.20/0.55  fof(f80,plain,(
% 0.20/0.55    ( ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),k4_relat_1(sK0)) | ~r2_hidden(k4_tarski(X3,X2),sK0)) ) | ~spl10_5),
% 0.20/0.55    inference(avatar_component_clause,[],[f79])).
% 0.20/0.55  fof(f125,plain,(
% 0.20/0.55    r2_hidden(k4_tarski(sK6(sK0,k2_relat_1(k4_relat_1(sK0))),sK7(sK0,k2_relat_1(k4_relat_1(sK0)))),sK0) | ~spl10_13),
% 0.20/0.55    inference(avatar_component_clause,[],[f123])).
% 0.20/0.55  fof(f325,plain,(
% 0.20/0.55    ~spl10_12 | ~spl10_4 | ~spl10_14),
% 0.20/0.55    inference(avatar_split_clause,[],[f320,f128,f75,f119])).
% 0.20/0.55  fof(f320,plain,(
% 0.20/0.55    ~r2_hidden(sK6(sK0,k2_relat_1(k4_relat_1(sK0))),k2_relat_1(k4_relat_1(sK0))) | (~spl10_4 | ~spl10_14)),
% 0.20/0.55    inference(resolution,[],[f207,f46])).
% 0.20/0.55  fof(f46,plain,(
% 0.20/0.55    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 0.20/0.55    inference(equality_resolution,[],[f35])).
% 0.20/0.55  fof(f35,plain,(
% 0.20/0.55    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 0.20/0.55    inference(cnf_transformation,[],[f21])).
% 0.20/0.55  fof(f207,plain,(
% 0.20/0.55    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK6(sK0,k2_relat_1(k4_relat_1(sK0)))),k4_relat_1(sK0))) ) | (~spl10_4 | ~spl10_14)),
% 0.20/0.55    inference(resolution,[],[f129,f76])).
% 0.20/0.55  fof(f129,plain,(
% 0.20/0.55    ( ! [X0] : (~r2_hidden(k4_tarski(sK6(sK0,k2_relat_1(k4_relat_1(sK0))),X0),sK0)) ) | ~spl10_14),
% 0.20/0.55    inference(avatar_component_clause,[],[f128])).
% 0.20/0.55  fof(f234,plain,(
% 0.20/0.55    ~spl10_22 | ~spl10_3 | spl10_11 | spl10_9),
% 0.20/0.55    inference(avatar_split_clause,[],[f230,f104,f113,f71,f194])).
% 0.20/0.55  fof(f194,plain,(
% 0.20/0.55    spl10_22 <=> v1_relat_1(sK0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).
% 0.20/0.55  fof(f71,plain,(
% 0.20/0.55    spl10_3 <=> v1_relat_1(k4_relat_1(sK0))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.20/0.55  fof(f230,plain,(
% 0.20/0.55    ( ! [X1] : (~r2_hidden(k4_tarski(X1,sK3(sK0,k1_relat_1(k4_relat_1(sK0)))),sK0) | ~v1_relat_1(k4_relat_1(sK0)) | ~v1_relat_1(sK0)) ) | spl10_9),
% 0.20/0.55    inference(resolution,[],[f150,f43])).
% 0.20/0.55  fof(f43,plain,(
% 0.20/0.55    ( ! [X4,X0,X5] : (r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X4),X0) | ~v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.55    inference(equality_resolution,[],[f32])).
% 0.20/0.55  fof(f32,plain,(
% 0.20/0.55    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X5,X4),X0) | k4_relat_1(X0) != X1 | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f15])).
% 0.20/0.55  fof(f15,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (((k4_relat_1(X0) = X1 | ((~r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0) | ~r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)) & (r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0) | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X5,X4),X0)) & (r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X4,X5),X1))) | k4_relat_1(X0) != X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f13,f14])).
% 0.20/0.55  fof(f14,plain,(
% 0.20/0.55    ! [X1,X0] : (? [X2,X3] : ((~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(k4_tarski(X2,X3),X1))) => ((~r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0) | ~r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)) & (r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0) | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1))))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f13,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (((k4_relat_1(X0) = X1 | ? [X2,X3] : ((~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X5,X4),X0)) & (r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X4,X5),X1))) | k4_relat_1(X0) != X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.55    inference(rectify,[],[f12])).
% 0.20/0.55  fof(f12,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (((k4_relat_1(X0) = X1 | ? [X2,X3] : ((~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X3,X2),X0)) & (r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X1))) | k4_relat_1(X0) != X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.55    inference(nnf_transformation,[],[f9])).
% 0.20/0.55  fof(f9,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : ((k4_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> r2_hidden(k4_tarski(X3,X2),X0))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f3])).
% 0.20/0.55  fof(f3,axiom,(
% 0.20/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (k4_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> r2_hidden(k4_tarski(X3,X2),X0)))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_relat_1)).
% 0.20/0.55  fof(f150,plain,(
% 0.20/0.55    ( ! [X0] : (~r2_hidden(k4_tarski(sK3(sK0,k1_relat_1(k4_relat_1(sK0))),X0),k4_relat_1(sK0))) ) | spl10_9),
% 0.20/0.55    inference(resolution,[],[f105,f47])).
% 0.20/0.55  fof(f47,plain,(
% 0.20/0.55    ( ! [X6,X0,X5] : (r2_hidden(X5,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X5,X6),X0)) )),
% 0.20/0.55    inference(equality_resolution,[],[f40])).
% 0.20/0.55  fof(f40,plain,(
% 0.20/0.55    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 0.20/0.55    inference(cnf_transformation,[],[f27])).
% 0.20/0.55  fof(f105,plain,(
% 0.20/0.55    ~r2_hidden(sK3(sK0,k1_relat_1(k4_relat_1(sK0))),k1_relat_1(k4_relat_1(sK0))) | spl10_9),
% 0.20/0.55    inference(avatar_component_clause,[],[f104])).
% 0.20/0.55  fof(f203,plain,(
% 0.20/0.55    spl10_22),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f202])).
% 0.20/0.55  fof(f202,plain,(
% 0.20/0.55    $false | spl10_22),
% 0.20/0.55    inference(resolution,[],[f196,f28])).
% 0.20/0.55  fof(f28,plain,(
% 0.20/0.55    v1_relat_1(sK0)),
% 0.20/0.55    inference(cnf_transformation,[],[f11])).
% 0.20/0.55  fof(f11,plain,(
% 0.20/0.55    (k1_relat_1(sK0) != k2_relat_1(k4_relat_1(sK0)) | k2_relat_1(sK0) != k1_relat_1(k4_relat_1(sK0))) & v1_relat_1(sK0)),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f10])).
% 0.20/0.55  fof(f10,plain,(
% 0.20/0.55    ? [X0] : ((k1_relat_1(X0) != k2_relat_1(k4_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(k4_relat_1(X0))) & v1_relat_1(X0)) => ((k1_relat_1(sK0) != k2_relat_1(k4_relat_1(sK0)) | k2_relat_1(sK0) != k1_relat_1(k4_relat_1(sK0))) & v1_relat_1(sK0))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f7,plain,(
% 0.20/0.55    ? [X0] : ((k1_relat_1(X0) != k2_relat_1(k4_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(k4_relat_1(X0))) & v1_relat_1(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f6])).
% 0.20/0.55  fof(f6,negated_conjecture,(
% 0.20/0.55    ~! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.20/0.55    inference(negated_conjecture,[],[f5])).
% 0.20/0.55  fof(f5,conjecture,(
% 0.20/0.55    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).
% 0.20/0.55  fof(f196,plain,(
% 0.20/0.55    ~v1_relat_1(sK0) | spl10_22),
% 0.20/0.55    inference(avatar_component_clause,[],[f194])).
% 0.20/0.55  fof(f126,plain,(
% 0.20/0.55    spl10_12 | spl10_13 | spl10_2),
% 0.20/0.55    inference(avatar_split_clause,[],[f116,f63,f123,f119])).
% 0.20/0.55  fof(f116,plain,(
% 0.20/0.55    r2_hidden(k4_tarski(sK6(sK0,k2_relat_1(k4_relat_1(sK0))),sK7(sK0,k2_relat_1(k4_relat_1(sK0)))),sK0) | r2_hidden(sK6(sK0,k2_relat_1(k4_relat_1(sK0))),k2_relat_1(k4_relat_1(sK0))) | spl10_2),
% 0.20/0.55    inference(resolution,[],[f65,f56])).
% 0.20/0.55  fof(f56,plain,(
% 0.20/0.55    ( ! [X0,X1] : (sQ9_eqProxy(k1_relat_1(X0),X1) | r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1)) )),
% 0.20/0.55    inference(equality_proxy_replacement,[],[f41,f49])).
% 0.20/0.55  fof(f41,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k1_relat_1(X0) = X1 | r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f27])).
% 0.20/0.55  fof(f65,plain,(
% 0.20/0.55    ~sQ9_eqProxy(k1_relat_1(sK0),k2_relat_1(k4_relat_1(sK0))) | spl10_2),
% 0.20/0.55    inference(avatar_component_clause,[],[f63])).
% 0.20/0.55  fof(f82,plain,(
% 0.20/0.55    spl10_3),
% 0.20/0.55    inference(avatar_split_clause,[],[f69,f71])).
% 0.20/0.55  fof(f69,plain,(
% 0.20/0.55    v1_relat_1(k4_relat_1(sK0))),
% 0.20/0.55    inference(resolution,[],[f28,f30])).
% 0.20/0.55  fof(f30,plain,(
% 0.20/0.55    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f8])).
% 0.20/0.55  fof(f8,plain,(
% 0.20/0.55    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f4])).
% 0.20/0.55  fof(f4,axiom,(
% 0.20/0.55    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.20/0.55  fof(f81,plain,(
% 0.20/0.55    ~spl10_3 | spl10_5),
% 0.20/0.55    inference(avatar_split_clause,[],[f68,f79,f71])).
% 0.20/0.55  fof(f68,plain,(
% 0.20/0.55    ( ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),k4_relat_1(sK0)) | ~r2_hidden(k4_tarski(X3,X2),sK0) | ~v1_relat_1(k4_relat_1(sK0))) )),
% 0.20/0.55    inference(resolution,[],[f28,f43])).
% 0.20/0.55  fof(f77,plain,(
% 0.20/0.55    ~spl10_3 | spl10_4),
% 0.20/0.55    inference(avatar_split_clause,[],[f67,f75,f71])).
% 0.20/0.55  fof(f67,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,X1),sK0) | ~r2_hidden(k4_tarski(X1,X0),k4_relat_1(sK0)) | ~v1_relat_1(k4_relat_1(sK0))) )),
% 0.20/0.55    inference(resolution,[],[f28,f44])).
% 0.20/0.55  fof(f44,plain,(
% 0.20/0.55    ( ! [X4,X0,X5] : (r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0)) | ~v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.55    inference(equality_resolution,[],[f31])).
% 0.20/0.55  fof(f31,plain,(
% 0.20/0.55    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X4,X5),X1) | k4_relat_1(X0) != X1 | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f15])).
% 0.20/0.55  fof(f66,plain,(
% 0.20/0.55    ~spl10_1 | ~spl10_2),
% 0.20/0.55    inference(avatar_split_clause,[],[f50,f63,f59])).
% 0.20/0.55  fof(f50,plain,(
% 0.20/0.55    ~sQ9_eqProxy(k1_relat_1(sK0),k2_relat_1(k4_relat_1(sK0))) | ~sQ9_eqProxy(k2_relat_1(sK0),k1_relat_1(k4_relat_1(sK0)))),
% 0.20/0.55    inference(equality_proxy_replacement,[],[f29,f49,f49])).
% 0.20/0.55  fof(f29,plain,(
% 0.20/0.55    k1_relat_1(sK0) != k2_relat_1(k4_relat_1(sK0)) | k2_relat_1(sK0) != k1_relat_1(k4_relat_1(sK0))),
% 0.20/0.55    inference(cnf_transformation,[],[f11])).
% 0.20/0.55  % SZS output end Proof for theBenchmark
% 0.20/0.55  % (27741)------------------------------
% 0.20/0.55  % (27741)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (27741)Termination reason: Refutation
% 0.20/0.55  
% 0.20/0.55  % (27741)Memory used [KB]: 6268
% 0.20/0.55  % (27741)Time elapsed: 0.116 s
% 0.20/0.55  % (27741)------------------------------
% 0.20/0.55  % (27741)------------------------------
% 0.20/0.55  % (27728)Success in time 0.189 s
%------------------------------------------------------------------------------
