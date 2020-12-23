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
% DateTime   : Thu Dec  3 12:46:58 EST 2020

% Result     : Theorem 0.14s
% Output     : Refutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 259 expanded)
%              Number of leaves         :   28 ( 100 expanded)
%              Depth                    :   11
%              Number of atoms          :  376 ( 849 expanded)
%              Number of equality atoms :  132 ( 380 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f657,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f83,f92,f98,f105,f112,f360,f436,f510,f515,f643,f651,f655,f656])).

fof(f656,plain,
    ( sK0 != sK9(sK0,k1_relat_1(sK2))
    | r2_hidden(sK9(sK0,k1_relat_1(sK2)),k1_relat_1(sK2))
    | ~ r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f655,plain,
    ( ~ spl10_17
    | ~ spl10_19
    | spl10_20 ),
    inference(avatar_contradiction_clause,[],[f652])).

fof(f652,plain,
    ( $false
    | ~ spl10_17
    | ~ spl10_19
    | spl10_20 ),
    inference(unit_resulting_resolution,[],[f641,f638,f445])).

fof(f445,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK2))
        | sK1 = X0 )
    | ~ spl10_17 ),
    inference(resolution,[],[f443,f67])).

fof(f67,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f15,f18,f17,f16])).

fof(f16,plain,(
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

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
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
    inference(rectify,[],[f14])).

fof(f14,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f443,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(k4_tarski(X3,X4),sK2)
        | sK1 = X4 )
    | ~ spl10_17 ),
    inference(superposition,[],[f62,f419])).

fof(f419,plain,
    ( sK2 = k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1))
    | ~ spl10_17 ),
    inference(avatar_component_clause,[],[f417])).

fof(f417,plain,
    ( spl10_17
  <=> sK2 = k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_enumset1(X3,X3,X3)))
      | X1 = X3 ) ),
    inference(definition_unfolding,[],[f49,f54])).

fof(f54,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f47,f53])).

fof(f53,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f47,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
        | X1 != X3
        | ~ r2_hidden(X0,X2) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
        | X1 != X3
        | ~ r2_hidden(X0,X2) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
    <=> ( X1 = X3
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).

fof(f638,plain,
    ( r2_hidden(sK9(sK1,k2_relat_1(sK2)),k2_relat_1(sK2))
    | ~ spl10_19 ),
    inference(avatar_component_clause,[],[f636])).

fof(f636,plain,
    ( spl10_19
  <=> r2_hidden(sK9(sK1,k2_relat_1(sK2)),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).

fof(f641,plain,
    ( sK1 != sK9(sK1,k2_relat_1(sK2))
    | spl10_20 ),
    inference(avatar_component_clause,[],[f640])).

fof(f640,plain,
    ( spl10_20
  <=> sK1 = sK9(sK1,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).

fof(f651,plain,
    ( ~ spl10_6
    | spl10_4
    | ~ spl10_20 ),
    inference(avatar_split_clause,[],[f650,f640,f89,f102])).

fof(f102,plain,
    ( spl10_6
  <=> r2_hidden(sK1,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f89,plain,
    ( spl10_4
  <=> k2_relat_1(sK2) = k1_enumset1(sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f650,plain,
    ( k2_relat_1(sK2) = k1_enumset1(sK1,sK1,sK1)
    | ~ r2_hidden(sK1,k2_relat_1(sK2))
    | ~ spl10_20 ),
    inference(trivial_inequality_removal,[],[f649])).

fof(f649,plain,
    ( sK1 != sK1
    | k2_relat_1(sK2) = k1_enumset1(sK1,sK1,sK1)
    | ~ r2_hidden(sK1,k2_relat_1(sK2))
    | ~ spl10_20 ),
    inference(superposition,[],[f57,f642])).

fof(f642,plain,
    ( sK1 = sK9(sK1,k2_relat_1(sK2))
    | ~ spl10_20 ),
    inference(avatar_component_clause,[],[f640])).

fof(f57,plain,(
    ! [X0,X1] :
      ( sK9(X0,X1) != X0
      | k1_enumset1(X0,X0,X0) = X1
      | ~ r2_hidden(sK9(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f46,f54])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK9(X0,X1) != X0
      | ~ r2_hidden(sK9(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK9(X0,X1) != X0
            | ~ r2_hidden(sK9(X0,X1),X1) )
          & ( sK9(X0,X1) = X0
            | r2_hidden(sK9(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f27,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK9(X0,X1) != X0
          | ~ r2_hidden(sK9(X0,X1),X1) )
        & ( sK9(X0,X1) = X0
          | r2_hidden(sK9(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f643,plain,
    ( spl10_19
    | spl10_20
    | spl10_4 ),
    inference(avatar_split_clause,[],[f481,f89,f640,f636])).

fof(f481,plain,
    ( sK1 = sK9(sK1,k2_relat_1(sK2))
    | r2_hidden(sK9(sK1,k2_relat_1(sK2)),k2_relat_1(sK2))
    | spl10_4 ),
    inference(equality_resolution,[],[f370])).

fof(f370,plain,
    ( ! [X0] :
        ( k2_relat_1(sK2) != X0
        | sK1 = sK9(sK1,X0)
        | r2_hidden(sK9(sK1,X0),X0) )
    | spl10_4 ),
    inference(superposition,[],[f91,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_enumset1(X0,X0,X0) = X1
      | sK9(X0,X1) = X0
      | r2_hidden(sK9(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f45,f54])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK9(X0,X1) = X0
      | r2_hidden(sK9(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f91,plain,
    ( k2_relat_1(sK2) != k1_enumset1(sK1,sK1,sK1)
    | spl10_4 ),
    inference(avatar_component_clause,[],[f89])).

fof(f515,plain,
    ( spl10_3
    | ~ spl10_14
    | ~ spl10_15 ),
    inference(avatar_contradiction_clause,[],[f511])).

fof(f511,plain,
    ( $false
    | spl10_3
    | ~ spl10_14
    | ~ spl10_15 ),
    inference(unit_resulting_resolution,[],[f355,f87,f359,f57])).

fof(f359,plain,
    ( sK0 = sK9(sK0,k1_relat_1(sK2))
    | ~ spl10_15 ),
    inference(avatar_component_clause,[],[f357])).

fof(f357,plain,
    ( spl10_15
  <=> sK0 = sK9(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).

fof(f87,plain,
    ( k1_relat_1(sK2) != k1_enumset1(sK0,sK0,sK0)
    | spl10_3 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl10_3
  <=> k1_relat_1(sK2) = k1_enumset1(sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f355,plain,
    ( r2_hidden(sK9(sK0,k1_relat_1(sK2)),k1_relat_1(sK2))
    | ~ spl10_14 ),
    inference(avatar_component_clause,[],[f353])).

fof(f353,plain,
    ( spl10_14
  <=> r2_hidden(sK9(sK0,k1_relat_1(sK2)),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f510,plain,
    ( spl10_15
    | ~ spl10_14
    | ~ spl10_17 ),
    inference(avatar_split_clause,[],[f507,f417,f353,f357])).

fof(f507,plain,
    ( sK0 = sK9(sK0,k1_relat_1(sK2))
    | ~ spl10_14
    | ~ spl10_17 ),
    inference(resolution,[],[f496,f355])).

fof(f496,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k1_relat_1(sK2))
        | sK0 = X4 )
    | ~ spl10_17 ),
    inference(resolution,[],[f483,f69])).

fof(f69,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f21,f24,f23,f22])).

fof(f22,plain,(
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

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f483,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(X2,X3),sK2)
        | sK0 = X2 )
    | ~ spl10_17 ),
    inference(resolution,[],[f442,f72])).

fof(f72,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_enumset1(X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f43,f54])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f442,plain,
    ( ! [X2,X1] :
        ( r2_hidden(X1,k1_enumset1(sK0,sK0,sK0))
        | ~ r2_hidden(k4_tarski(X1,X2),sK2) )
    | ~ spl10_17 ),
    inference(superposition,[],[f63,f419])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_enumset1(X3,X3,X3)))
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f48,f54])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f436,plain,
    ( spl10_17
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f399,f80,f417])).

fof(f80,plain,
    ( spl10_2
  <=> sK2 = k1_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f399,plain,
    ( sK2 = k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1))
    | ~ spl10_2 ),
    inference(superposition,[],[f82,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2)) = k1_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(definition_unfolding,[],[f52,f53,f54,f53])).

fof(f52,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f82,plain,
    ( sK2 = k1_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f360,plain,
    ( spl10_14
    | spl10_15
    | spl10_3 ),
    inference(avatar_split_clause,[],[f351,f85,f357,f353])).

fof(f351,plain,
    ( sK0 = sK9(sK0,k1_relat_1(sK2))
    | r2_hidden(sK9(sK0,k1_relat_1(sK2)),k1_relat_1(sK2))
    | spl10_3 ),
    inference(equality_resolution,[],[f293])).

fof(f293,plain,
    ( ! [X1] :
        ( k1_relat_1(sK2) != X1
        | sK0 = sK9(sK0,X1)
        | r2_hidden(sK9(sK0,X1),X1) )
    | spl10_3 ),
    inference(superposition,[],[f87,f58])).

fof(f112,plain,
    ( spl10_7
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f106,f95,f109])).

fof(f109,plain,
    ( spl10_7
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f95,plain,
    ( spl10_5
  <=> r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f106,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl10_5 ),
    inference(resolution,[],[f68,f97])).

fof(f97,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f95])).

fof(f68,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X0)
      | r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f105,plain,
    ( spl10_6
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f99,f95,f102])).

fof(f99,plain,
    ( r2_hidden(sK1,k2_relat_1(sK2))
    | ~ spl10_5 ),
    inference(resolution,[],[f66,f97])).

fof(f66,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X6,X5),X0)
      | r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f98,plain,
    ( spl10_5
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f93,f80,f95])).

fof(f93,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl10_2 ),
    inference(superposition,[],[f71,f82])).

fof(f71,plain,(
    ! [X3] : r2_hidden(X3,k1_enumset1(X3,X3,X3)) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_enumset1(X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f44,f54])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f92,plain,
    ( ~ spl10_3
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f55,f89,f85])).

fof(f55,plain,
    ( k2_relat_1(sK2) != k1_enumset1(sK1,sK1,sK1)
    | k1_relat_1(sK2) != k1_enumset1(sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f34,f54,f54])).

fof(f34,plain,
    ( k2_relat_1(sK2) != k1_tarski(sK1)
    | k1_tarski(sK0) != k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ( k2_relat_1(sK2) != k1_tarski(sK1)
      | k1_tarski(sK0) != k1_relat_1(sK2) )
    & sK2 = k1_tarski(k4_tarski(sK0,sK1))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2] :
        ( ( k2_relat_1(X2) != k1_tarski(X1)
          | k1_tarski(X0) != k1_relat_1(X2) )
        & k1_tarski(k4_tarski(X0,X1)) = X2
        & v1_relat_1(X2) )
   => ( ( k2_relat_1(sK2) != k1_tarski(sK1)
        | k1_tarski(sK0) != k1_relat_1(sK2) )
      & sK2 = k1_tarski(k4_tarski(sK0,sK1))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relat_1(X2) != k1_tarski(X1)
        | k1_tarski(X0) != k1_relat_1(X2) )
      & k1_tarski(k4_tarski(X0,X1)) = X2
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ( k2_relat_1(X2) != k1_tarski(X1)
        | k1_tarski(X0) != k1_relat_1(X2) )
      & k1_tarski(k4_tarski(X0,X1)) = X2
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( k1_tarski(k4_tarski(X0,X1)) = X2
         => ( k2_relat_1(X2) = k1_tarski(X1)
            & k1_tarski(X0) = k1_relat_1(X2) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( k1_tarski(k4_tarski(X0,X1)) = X2
       => ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_tarski(X0) = k1_relat_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relat_1)).

fof(f83,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f56,f80])).

fof(f56,plain,(
    sK2 = k1_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)) ),
    inference(definition_unfolding,[],[f33,f54])).

fof(f33,plain,(
    sK2 = k1_tarski(k4_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.08  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.09  % Command    : run_vampire %s %d
% 0.09/0.29  % Computer   : n002.cluster.edu
% 0.09/0.29  % Model      : x86_64 x86_64
% 0.09/0.29  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.29  % Memory     : 8042.1875MB
% 0.09/0.29  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.29  % CPULimit   : 60
% 0.09/0.29  % WCLimit    : 600
% 0.09/0.29  % DateTime   : Tue Dec  1 15:20:51 EST 2020
% 0.09/0.29  % CPUTime    : 
% 0.14/0.38  % (31928)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.14/0.39  % (31950)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.14/0.43  % (31931)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.14/0.43  % (31943)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.14/0.44  % (31933)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.14/0.44  % (31930)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.14/0.44  % (31935)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.14/0.45  % (31948)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.14/0.45  % (31946)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.14/0.45  % (31941)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.14/0.45  % (31932)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.14/0.45  % (31955)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.14/0.45  % (31938)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.14/0.45  % (31945)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.14/0.45  % (31934)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.14/0.45  % (31937)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.14/0.45  % (31954)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.14/0.45  % (31952)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.14/0.45  % (31936)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.14/0.46  % (31940)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.14/0.46  % (31942)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.14/0.46  % (31939)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.14/0.46  % (31929)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.14/0.46  % (31957)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.14/0.46  % (31953)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.14/0.46  % (31957)Refutation not found, incomplete strategy% (31957)------------------------------
% 0.14/0.46  % (31957)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.14/0.46  % (31957)Termination reason: Refutation not found, incomplete strategy
% 0.14/0.46  
% 0.14/0.46  % (31957)Memory used [KB]: 1663
% 0.14/0.46  % (31957)Time elapsed: 0.129 s
% 0.14/0.46  % (31957)------------------------------
% 0.14/0.46  % (31957)------------------------------
% 0.14/0.47  % (31951)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.14/0.47  % (31947)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.14/0.47  % (31944)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.14/0.47  % (31944)Refutation not found, incomplete strategy% (31944)------------------------------
% 0.14/0.47  % (31944)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.14/0.48  % (31949)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.14/0.48  % (31944)Termination reason: Refutation not found, incomplete strategy
% 0.14/0.48  
% 0.14/0.48  % (31944)Memory used [KB]: 10618
% 0.14/0.48  % (31944)Time elapsed: 0.125 s
% 0.14/0.48  % (31944)------------------------------
% 0.14/0.48  % (31944)------------------------------
% 0.14/0.48  % (31956)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.14/0.51  % (31951)Refutation found. Thanks to Tanya!
% 0.14/0.51  % SZS status Theorem for theBenchmark
% 0.14/0.51  % SZS output start Proof for theBenchmark
% 0.14/0.51  fof(f657,plain,(
% 0.14/0.51    $false),
% 0.14/0.51    inference(avatar_sat_refutation,[],[f83,f92,f98,f105,f112,f360,f436,f510,f515,f643,f651,f655,f656])).
% 0.14/0.51  fof(f656,plain,(
% 0.14/0.51    sK0 != sK9(sK0,k1_relat_1(sK2)) | r2_hidden(sK9(sK0,k1_relat_1(sK2)),k1_relat_1(sK2)) | ~r2_hidden(sK0,k1_relat_1(sK2))),
% 0.14/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.14/0.51  fof(f655,plain,(
% 0.14/0.51    ~spl10_17 | ~spl10_19 | spl10_20),
% 0.14/0.51    inference(avatar_contradiction_clause,[],[f652])).
% 0.14/0.51  fof(f652,plain,(
% 0.14/0.51    $false | (~spl10_17 | ~spl10_19 | spl10_20)),
% 0.14/0.51    inference(unit_resulting_resolution,[],[f641,f638,f445])).
% 0.14/0.51  fof(f445,plain,(
% 0.14/0.51    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK2)) | sK1 = X0) ) | ~spl10_17),
% 0.14/0.51    inference(resolution,[],[f443,f67])).
% 0.14/0.51  fof(f67,plain,(
% 0.14/0.51    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 0.14/0.51    inference(equality_resolution,[],[f35])).
% 0.14/0.51  fof(f35,plain,(
% 0.14/0.51    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 0.14/0.51    inference(cnf_transformation,[],[f19])).
% 0.14/0.51  fof(f19,plain,(
% 0.14/0.51    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.14/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f15,f18,f17,f16])).
% 0.14/0.51  fof(f16,plain,(
% 0.14/0.51    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 0.14/0.51    introduced(choice_axiom,[])).
% 0.14/0.51  fof(f17,plain,(
% 0.14/0.51    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0) => r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0))),
% 0.14/0.51    introduced(choice_axiom,[])).
% 0.14/0.51  fof(f18,plain,(
% 0.14/0.51    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK5(X0,X5),X5),X0))),
% 0.14/0.51    introduced(choice_axiom,[])).
% 0.14/0.51  fof(f15,plain,(
% 0.14/0.51    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.14/0.51    inference(rectify,[],[f14])).
% 0.14/0.51  fof(f14,plain,(
% 0.14/0.51    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 0.14/0.51    inference(nnf_transformation,[],[f7])).
% 0.14/0.51  fof(f7,axiom,(
% 0.14/0.51    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.14/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 0.14/0.51  fof(f443,plain,(
% 0.14/0.51    ( ! [X4,X3] : (~r2_hidden(k4_tarski(X3,X4),sK2) | sK1 = X4) ) | ~spl10_17),
% 0.14/0.51    inference(superposition,[],[f62,f419])).
% 0.14/0.51  fof(f419,plain,(
% 0.14/0.51    sK2 = k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)) | ~spl10_17),
% 0.14/0.51    inference(avatar_component_clause,[],[f417])).
% 0.14/0.51  fof(f417,plain,(
% 0.14/0.51    spl10_17 <=> sK2 = k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1))),
% 0.14/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).
% 0.14/0.51  fof(f62,plain,(
% 0.14/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_enumset1(X3,X3,X3))) | X1 = X3) )),
% 0.14/0.51    inference(definition_unfolding,[],[f49,f54])).
% 0.14/0.51  fof(f54,plain,(
% 0.14/0.51    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.14/0.51    inference(definition_unfolding,[],[f47,f53])).
% 0.14/0.51  fof(f53,plain,(
% 0.14/0.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.14/0.51    inference(cnf_transformation,[],[f3])).
% 0.14/0.51  fof(f3,axiom,(
% 0.14/0.51    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.14/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.14/0.51  fof(f47,plain,(
% 0.14/0.51    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.14/0.51    inference(cnf_transformation,[],[f2])).
% 0.14/0.51  fof(f2,axiom,(
% 0.14/0.51    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.14/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.14/0.51  fof(f49,plain,(
% 0.14/0.51    ( ! [X2,X0,X3,X1] : (X1 = X3 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))) )),
% 0.14/0.51    inference(cnf_transformation,[],[f31])).
% 0.14/0.51  fof(f31,plain,(
% 0.14/0.51    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | X1 != X3 | ~r2_hidden(X0,X2)) & ((X1 = X3 & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 0.14/0.51    inference(flattening,[],[f30])).
% 0.14/0.51  fof(f30,plain,(
% 0.14/0.51    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | (X1 != X3 | ~r2_hidden(X0,X2))) & ((X1 = X3 & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 0.14/0.51    inference(nnf_transformation,[],[f4])).
% 0.14/0.51  fof(f4,axiom,(
% 0.14/0.51    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) <=> (X1 = X3 & r2_hidden(X0,X2)))),
% 0.14/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).
% 0.14/0.51  fof(f638,plain,(
% 0.14/0.51    r2_hidden(sK9(sK1,k2_relat_1(sK2)),k2_relat_1(sK2)) | ~spl10_19),
% 0.14/0.51    inference(avatar_component_clause,[],[f636])).
% 0.14/0.51  fof(f636,plain,(
% 0.14/0.51    spl10_19 <=> r2_hidden(sK9(sK1,k2_relat_1(sK2)),k2_relat_1(sK2))),
% 0.14/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).
% 0.14/0.51  fof(f641,plain,(
% 0.14/0.51    sK1 != sK9(sK1,k2_relat_1(sK2)) | spl10_20),
% 0.14/0.51    inference(avatar_component_clause,[],[f640])).
% 0.14/0.51  fof(f640,plain,(
% 0.14/0.51    spl10_20 <=> sK1 = sK9(sK1,k2_relat_1(sK2))),
% 0.14/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).
% 0.14/0.51  fof(f651,plain,(
% 0.14/0.51    ~spl10_6 | spl10_4 | ~spl10_20),
% 0.14/0.51    inference(avatar_split_clause,[],[f650,f640,f89,f102])).
% 0.14/0.51  fof(f102,plain,(
% 0.14/0.51    spl10_6 <=> r2_hidden(sK1,k2_relat_1(sK2))),
% 0.14/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 0.14/0.51  fof(f89,plain,(
% 0.14/0.51    spl10_4 <=> k2_relat_1(sK2) = k1_enumset1(sK1,sK1,sK1)),
% 0.14/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 0.14/0.51  fof(f650,plain,(
% 0.14/0.51    k2_relat_1(sK2) = k1_enumset1(sK1,sK1,sK1) | ~r2_hidden(sK1,k2_relat_1(sK2)) | ~spl10_20),
% 0.14/0.51    inference(trivial_inequality_removal,[],[f649])).
% 0.14/0.51  fof(f649,plain,(
% 0.14/0.51    sK1 != sK1 | k2_relat_1(sK2) = k1_enumset1(sK1,sK1,sK1) | ~r2_hidden(sK1,k2_relat_1(sK2)) | ~spl10_20),
% 0.14/0.51    inference(superposition,[],[f57,f642])).
% 0.14/0.51  fof(f642,plain,(
% 0.14/0.51    sK1 = sK9(sK1,k2_relat_1(sK2)) | ~spl10_20),
% 0.14/0.51    inference(avatar_component_clause,[],[f640])).
% 0.14/0.51  fof(f57,plain,(
% 0.14/0.51    ( ! [X0,X1] : (sK9(X0,X1) != X0 | k1_enumset1(X0,X0,X0) = X1 | ~r2_hidden(sK9(X0,X1),X1)) )),
% 0.14/0.51    inference(definition_unfolding,[],[f46,f54])).
% 0.14/0.51  fof(f46,plain,(
% 0.14/0.51    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK9(X0,X1) != X0 | ~r2_hidden(sK9(X0,X1),X1)) )),
% 0.14/0.51    inference(cnf_transformation,[],[f29])).
% 0.14/0.51  fof(f29,plain,(
% 0.14/0.51    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK9(X0,X1) != X0 | ~r2_hidden(sK9(X0,X1),X1)) & (sK9(X0,X1) = X0 | r2_hidden(sK9(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.14/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f27,f28])).
% 0.14/0.51  fof(f28,plain,(
% 0.14/0.51    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK9(X0,X1) != X0 | ~r2_hidden(sK9(X0,X1),X1)) & (sK9(X0,X1) = X0 | r2_hidden(sK9(X0,X1),X1))))),
% 0.14/0.51    introduced(choice_axiom,[])).
% 0.14/0.51  fof(f27,plain,(
% 0.14/0.51    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.14/0.51    inference(rectify,[],[f26])).
% 0.14/0.51  fof(f26,plain,(
% 0.14/0.51    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.14/0.51    inference(nnf_transformation,[],[f1])).
% 0.14/0.51  fof(f1,axiom,(
% 0.14/0.51    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.14/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.14/0.51  fof(f643,plain,(
% 0.14/0.51    spl10_19 | spl10_20 | spl10_4),
% 0.14/0.51    inference(avatar_split_clause,[],[f481,f89,f640,f636])).
% 0.14/0.51  fof(f481,plain,(
% 0.14/0.51    sK1 = sK9(sK1,k2_relat_1(sK2)) | r2_hidden(sK9(sK1,k2_relat_1(sK2)),k2_relat_1(sK2)) | spl10_4),
% 0.14/0.51    inference(equality_resolution,[],[f370])).
% 0.14/0.51  fof(f370,plain,(
% 0.14/0.51    ( ! [X0] : (k2_relat_1(sK2) != X0 | sK1 = sK9(sK1,X0) | r2_hidden(sK9(sK1,X0),X0)) ) | spl10_4),
% 0.14/0.51    inference(superposition,[],[f91,f58])).
% 0.14/0.51  fof(f58,plain,(
% 0.14/0.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X0) = X1 | sK9(X0,X1) = X0 | r2_hidden(sK9(X0,X1),X1)) )),
% 0.14/0.51    inference(definition_unfolding,[],[f45,f54])).
% 0.14/0.51  fof(f45,plain,(
% 0.14/0.51    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK9(X0,X1) = X0 | r2_hidden(sK9(X0,X1),X1)) )),
% 0.14/0.51    inference(cnf_transformation,[],[f29])).
% 0.14/0.51  fof(f91,plain,(
% 0.14/0.51    k2_relat_1(sK2) != k1_enumset1(sK1,sK1,sK1) | spl10_4),
% 0.14/0.51    inference(avatar_component_clause,[],[f89])).
% 0.14/0.51  fof(f515,plain,(
% 0.14/0.51    spl10_3 | ~spl10_14 | ~spl10_15),
% 0.14/0.51    inference(avatar_contradiction_clause,[],[f511])).
% 0.14/0.51  fof(f511,plain,(
% 0.14/0.51    $false | (spl10_3 | ~spl10_14 | ~spl10_15)),
% 0.14/0.51    inference(unit_resulting_resolution,[],[f355,f87,f359,f57])).
% 0.14/0.51  fof(f359,plain,(
% 0.14/0.51    sK0 = sK9(sK0,k1_relat_1(sK2)) | ~spl10_15),
% 0.14/0.51    inference(avatar_component_clause,[],[f357])).
% 0.14/0.51  fof(f357,plain,(
% 0.14/0.51    spl10_15 <=> sK0 = sK9(sK0,k1_relat_1(sK2))),
% 0.14/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).
% 0.14/0.51  fof(f87,plain,(
% 0.14/0.51    k1_relat_1(sK2) != k1_enumset1(sK0,sK0,sK0) | spl10_3),
% 0.14/0.51    inference(avatar_component_clause,[],[f85])).
% 0.14/0.51  fof(f85,plain,(
% 0.14/0.51    spl10_3 <=> k1_relat_1(sK2) = k1_enumset1(sK0,sK0,sK0)),
% 0.14/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.14/0.51  fof(f355,plain,(
% 0.14/0.51    r2_hidden(sK9(sK0,k1_relat_1(sK2)),k1_relat_1(sK2)) | ~spl10_14),
% 0.14/0.51    inference(avatar_component_clause,[],[f353])).
% 0.14/0.51  fof(f353,plain,(
% 0.14/0.51    spl10_14 <=> r2_hidden(sK9(sK0,k1_relat_1(sK2)),k1_relat_1(sK2))),
% 0.14/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).
% 0.14/0.51  fof(f510,plain,(
% 0.14/0.51    spl10_15 | ~spl10_14 | ~spl10_17),
% 0.14/0.51    inference(avatar_split_clause,[],[f507,f417,f353,f357])).
% 0.14/0.51  fof(f507,plain,(
% 0.14/0.51    sK0 = sK9(sK0,k1_relat_1(sK2)) | (~spl10_14 | ~spl10_17)),
% 0.14/0.51    inference(resolution,[],[f496,f355])).
% 0.14/0.51  fof(f496,plain,(
% 0.14/0.51    ( ! [X4] : (~r2_hidden(X4,k1_relat_1(sK2)) | sK0 = X4) ) | ~spl10_17),
% 0.14/0.51    inference(resolution,[],[f483,f69])).
% 0.14/0.51  fof(f69,plain,(
% 0.14/0.51    ( ! [X0,X5] : (r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) | ~r2_hidden(X5,k1_relat_1(X0))) )),
% 0.14/0.51    inference(equality_resolution,[],[f39])).
% 0.14/0.51  fof(f39,plain,(
% 0.14/0.51    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 0.14/0.51    inference(cnf_transformation,[],[f25])).
% 0.14/0.51  fof(f25,plain,(
% 0.14/0.51    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK6(X0,X1),X3),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.14/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f21,f24,f23,f22])).
% 0.14/0.51  fof(f22,plain,(
% 0.14/0.51    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK6(X0,X1),X3),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0) | r2_hidden(sK6(X0,X1),X1))))),
% 0.14/0.51    introduced(choice_axiom,[])).
% 0.14/0.51  fof(f23,plain,(
% 0.14/0.51    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0))),
% 0.14/0.51    introduced(choice_axiom,[])).
% 0.14/0.51  fof(f24,plain,(
% 0.14/0.51    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0))),
% 0.14/0.51    introduced(choice_axiom,[])).
% 0.14/0.51  fof(f21,plain,(
% 0.14/0.51    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.14/0.51    inference(rectify,[],[f20])).
% 0.14/0.51  fof(f20,plain,(
% 0.14/0.51    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 0.14/0.51    inference(nnf_transformation,[],[f6])).
% 0.14/0.52  fof(f6,axiom,(
% 0.14/0.52    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.14/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 0.14/0.52  fof(f483,plain,(
% 0.14/0.52    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),sK2) | sK0 = X2) ) | ~spl10_17),
% 0.14/0.52    inference(resolution,[],[f442,f72])).
% 0.14/0.52  fof(f72,plain,(
% 0.14/0.52    ( ! [X0,X3] : (~r2_hidden(X3,k1_enumset1(X0,X0,X0)) | X0 = X3) )),
% 0.14/0.52    inference(equality_resolution,[],[f60])).
% 0.14/0.52  fof(f60,plain,(
% 0.14/0.52    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_enumset1(X0,X0,X0) != X1) )),
% 0.14/0.52    inference(definition_unfolding,[],[f43,f54])).
% 0.14/0.52  fof(f43,plain,(
% 0.14/0.52    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.14/0.52    inference(cnf_transformation,[],[f29])).
% 0.14/0.52  fof(f442,plain,(
% 0.14/0.52    ( ! [X2,X1] : (r2_hidden(X1,k1_enumset1(sK0,sK0,sK0)) | ~r2_hidden(k4_tarski(X1,X2),sK2)) ) | ~spl10_17),
% 0.14/0.52    inference(superposition,[],[f63,f419])).
% 0.14/0.52  fof(f63,plain,(
% 0.14/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_enumset1(X3,X3,X3))) | r2_hidden(X0,X2)) )),
% 0.14/0.52    inference(definition_unfolding,[],[f48,f54])).
% 0.14/0.52  fof(f48,plain,(
% 0.14/0.52    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))) )),
% 0.14/0.52    inference(cnf_transformation,[],[f31])).
% 0.14/0.52  fof(f436,plain,(
% 0.14/0.52    spl10_17 | ~spl10_2),
% 0.14/0.52    inference(avatar_split_clause,[],[f399,f80,f417])).
% 0.14/0.52  fof(f80,plain,(
% 0.14/0.52    spl10_2 <=> sK2 = k1_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))),
% 0.14/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.14/0.52  fof(f399,plain,(
% 0.14/0.52    sK2 = k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK1,sK1,sK1)) | ~spl10_2),
% 0.14/0.52    inference(superposition,[],[f82,f64])).
% 0.14/0.52  fof(f64,plain,(
% 0.14/0.52    ( ! [X2,X0,X1] : (k2_zfmisc_1(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2)) = k1_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 0.14/0.52    inference(definition_unfolding,[],[f52,f53,f54,f53])).
% 0.14/0.53  fof(f52,plain,(
% 0.14/0.53    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 0.14/0.53    inference(cnf_transformation,[],[f5])).
% 0.14/0.53  fof(f5,axiom,(
% 0.14/0.53    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 0.14/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 0.14/0.53  fof(f82,plain,(
% 0.14/0.53    sK2 = k1_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)) | ~spl10_2),
% 0.14/0.53    inference(avatar_component_clause,[],[f80])).
% 0.14/0.53  fof(f360,plain,(
% 0.14/0.53    spl10_14 | spl10_15 | spl10_3),
% 0.14/0.53    inference(avatar_split_clause,[],[f351,f85,f357,f353])).
% 0.14/0.53  fof(f351,plain,(
% 0.14/0.53    sK0 = sK9(sK0,k1_relat_1(sK2)) | r2_hidden(sK9(sK0,k1_relat_1(sK2)),k1_relat_1(sK2)) | spl10_3),
% 0.14/0.53    inference(equality_resolution,[],[f293])).
% 0.14/0.53  fof(f293,plain,(
% 0.14/0.53    ( ! [X1] : (k1_relat_1(sK2) != X1 | sK0 = sK9(sK0,X1) | r2_hidden(sK9(sK0,X1),X1)) ) | spl10_3),
% 0.14/0.53    inference(superposition,[],[f87,f58])).
% 0.14/0.53  fof(f112,plain,(
% 0.14/0.53    spl10_7 | ~spl10_5),
% 0.14/0.53    inference(avatar_split_clause,[],[f106,f95,f109])).
% 0.14/0.53  fof(f109,plain,(
% 0.14/0.53    spl10_7 <=> r2_hidden(sK0,k1_relat_1(sK2))),
% 0.14/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 0.14/0.53  fof(f95,plain,(
% 0.14/0.53    spl10_5 <=> r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 0.14/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 0.14/0.53  fof(f106,plain,(
% 0.14/0.53    r2_hidden(sK0,k1_relat_1(sK2)) | ~spl10_5),
% 0.14/0.53    inference(resolution,[],[f68,f97])).
% 0.14/0.53  fof(f97,plain,(
% 0.14/0.53    r2_hidden(k4_tarski(sK0,sK1),sK2) | ~spl10_5),
% 0.14/0.53    inference(avatar_component_clause,[],[f95])).
% 0.14/0.53  fof(f68,plain,(
% 0.14/0.53    ( ! [X6,X0,X5] : (~r2_hidden(k4_tarski(X5,X6),X0) | r2_hidden(X5,k1_relat_1(X0))) )),
% 0.14/0.53    inference(equality_resolution,[],[f40])).
% 0.14/0.53  fof(f40,plain,(
% 0.14/0.53    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 0.14/0.53    inference(cnf_transformation,[],[f25])).
% 0.14/0.53  fof(f105,plain,(
% 0.14/0.53    spl10_6 | ~spl10_5),
% 0.14/0.53    inference(avatar_split_clause,[],[f99,f95,f102])).
% 0.14/0.53  fof(f99,plain,(
% 0.14/0.53    r2_hidden(sK1,k2_relat_1(sK2)) | ~spl10_5),
% 0.14/0.53    inference(resolution,[],[f66,f97])).
% 0.14/0.53  fof(f66,plain,(
% 0.14/0.53    ( ! [X6,X0,X5] : (~r2_hidden(k4_tarski(X6,X5),X0) | r2_hidden(X5,k2_relat_1(X0))) )),
% 0.14/0.53    inference(equality_resolution,[],[f36])).
% 0.14/0.53  fof(f36,plain,(
% 0.14/0.53    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X6,X5),X0) | k2_relat_1(X0) != X1) )),
% 0.14/0.53    inference(cnf_transformation,[],[f19])).
% 0.14/0.53  fof(f98,plain,(
% 0.14/0.53    spl10_5 | ~spl10_2),
% 0.14/0.53    inference(avatar_split_clause,[],[f93,f80,f95])).
% 0.14/0.53  fof(f93,plain,(
% 0.14/0.53    r2_hidden(k4_tarski(sK0,sK1),sK2) | ~spl10_2),
% 0.14/0.53    inference(superposition,[],[f71,f82])).
% 0.14/0.53  fof(f71,plain,(
% 0.14/0.53    ( ! [X3] : (r2_hidden(X3,k1_enumset1(X3,X3,X3))) )),
% 0.14/0.53    inference(equality_resolution,[],[f70])).
% 0.14/0.53  fof(f70,plain,(
% 0.14/0.53    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_enumset1(X3,X3,X3) != X1) )),
% 0.14/0.53    inference(equality_resolution,[],[f59])).
% 0.14/0.53  fof(f59,plain,(
% 0.14/0.53    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_enumset1(X0,X0,X0) != X1) )),
% 0.14/0.53    inference(definition_unfolding,[],[f44,f54])).
% 0.14/0.53  fof(f44,plain,(
% 0.14/0.53    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.14/0.53    inference(cnf_transformation,[],[f29])).
% 0.14/0.53  fof(f92,plain,(
% 0.14/0.53    ~spl10_3 | ~spl10_4),
% 0.14/0.53    inference(avatar_split_clause,[],[f55,f89,f85])).
% 0.14/0.53  fof(f55,plain,(
% 0.14/0.53    k2_relat_1(sK2) != k1_enumset1(sK1,sK1,sK1) | k1_relat_1(sK2) != k1_enumset1(sK0,sK0,sK0)),
% 0.14/0.53    inference(definition_unfolding,[],[f34,f54,f54])).
% 0.14/0.53  fof(f34,plain,(
% 0.14/0.53    k2_relat_1(sK2) != k1_tarski(sK1) | k1_tarski(sK0) != k1_relat_1(sK2)),
% 0.14/0.53    inference(cnf_transformation,[],[f13])).
% 0.14/0.53  fof(f13,plain,(
% 0.14/0.53    (k2_relat_1(sK2) != k1_tarski(sK1) | k1_tarski(sK0) != k1_relat_1(sK2)) & sK2 = k1_tarski(k4_tarski(sK0,sK1)) & v1_relat_1(sK2)),
% 0.14/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).
% 0.14/0.53  fof(f12,plain,(
% 0.14/0.53    ? [X0,X1,X2] : ((k2_relat_1(X2) != k1_tarski(X1) | k1_tarski(X0) != k1_relat_1(X2)) & k1_tarski(k4_tarski(X0,X1)) = X2 & v1_relat_1(X2)) => ((k2_relat_1(sK2) != k1_tarski(sK1) | k1_tarski(sK0) != k1_relat_1(sK2)) & sK2 = k1_tarski(k4_tarski(sK0,sK1)) & v1_relat_1(sK2))),
% 0.14/0.53    introduced(choice_axiom,[])).
% 0.14/0.53  fof(f11,plain,(
% 0.14/0.53    ? [X0,X1,X2] : ((k2_relat_1(X2) != k1_tarski(X1) | k1_tarski(X0) != k1_relat_1(X2)) & k1_tarski(k4_tarski(X0,X1)) = X2 & v1_relat_1(X2))),
% 0.14/0.53    inference(flattening,[],[f10])).
% 0.14/0.53  fof(f10,plain,(
% 0.14/0.53    ? [X0,X1,X2] : (((k2_relat_1(X2) != k1_tarski(X1) | k1_tarski(X0) != k1_relat_1(X2)) & k1_tarski(k4_tarski(X0,X1)) = X2) & v1_relat_1(X2))),
% 0.14/0.53    inference(ennf_transformation,[],[f9])).
% 0.14/0.53  fof(f9,negated_conjecture,(
% 0.14/0.53    ~! [X0,X1,X2] : (v1_relat_1(X2) => (k1_tarski(k4_tarski(X0,X1)) = X2 => (k2_relat_1(X2) = k1_tarski(X1) & k1_tarski(X0) = k1_relat_1(X2))))),
% 0.14/0.53    inference(negated_conjecture,[],[f8])).
% 0.14/0.53  fof(f8,conjecture,(
% 0.14/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => (k1_tarski(k4_tarski(X0,X1)) = X2 => (k2_relat_1(X2) = k1_tarski(X1) & k1_tarski(X0) = k1_relat_1(X2))))),
% 0.14/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relat_1)).
% 0.14/0.53  fof(f83,plain,(
% 0.14/0.53    spl10_2),
% 0.14/0.53    inference(avatar_split_clause,[],[f56,f80])).
% 0.14/0.53  fof(f56,plain,(
% 0.14/0.53    sK2 = k1_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1))),
% 0.14/0.53    inference(definition_unfolding,[],[f33,f54])).
% 0.14/0.53  fof(f33,plain,(
% 0.14/0.53    sK2 = k1_tarski(k4_tarski(sK0,sK1))),
% 0.14/0.53    inference(cnf_transformation,[],[f13])).
% 0.14/0.53  % SZS output end Proof for theBenchmark
% 0.14/0.53  % (31951)------------------------------
% 0.14/0.53  % (31951)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.14/0.53  % (31951)Termination reason: Refutation
% 0.14/0.53  
% 0.14/0.53  % (31951)Memory used [KB]: 11129
% 0.14/0.53  % (31951)Time elapsed: 0.174 s
% 0.14/0.53  % (31951)------------------------------
% 0.14/0.53  % (31951)------------------------------
% 0.14/0.53  % (31927)Success in time 0.224 s
%------------------------------------------------------------------------------
