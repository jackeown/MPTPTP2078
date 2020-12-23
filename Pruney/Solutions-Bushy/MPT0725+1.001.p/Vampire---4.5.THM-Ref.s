%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0725+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:32 EST 2020

% Result     : Theorem 5.16s
% Output     : Refutation 5.16s
% Verified   : 
% Statistics : Number of formulae       :  359 (1487 expanded)
%              Number of leaves         :   95 ( 533 expanded)
%              Depth                    :   19
%              Number of atoms          :  979 (7897 expanded)
%              Number of equality atoms :  221 (3981 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3466,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f79,f84,f89,f94,f99,f107,f119,f124,f131,f136,f141,f161,f166,f176,f181,f186,f197,f202,f207,f212,f217,f253,f264,f269,f274,f279,f300,f311,f316,f321,f326,f331,f342,f347,f352,f357,f438,f445,f450,f455,f460,f465,f471,f476,f481,f486,f491,f496,f501,f506,f511,f586,f591,f596,f601,f606,f651,f665,f670,f675,f680,f725,f738,f743,f748,f753,f1447,f2993,f3004,f3149,f3160,f3277,f3288,f3297,f3308,f3330,f3464])).

fof(f3464,plain,
    ( ~ spl9_3
    | ~ spl9_80 ),
    inference(avatar_contradiction_clause,[],[f3463])).

fof(f3463,plain,
    ( $false
    | ~ spl9_3
    | ~ spl9_80 ),
    inference(subsumption_resolution,[],[f3376,f83])).

fof(f83,plain,
    ( r2_hidden(sK2,sK3)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl9_3
  <=> r2_hidden(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f3376,plain,
    ( ~ r2_hidden(sK2,sK3)
    | ~ spl9_80 ),
    inference(superposition,[],[f813,f3329])).

fof(f3329,plain,
    ( sK3 = sK7(k3_enumset1(sK1,sK5,sK4,sK3,sK2))
    | ~ spl9_80 ),
    inference(avatar_component_clause,[],[f3327])).

fof(f3327,plain,
    ( spl9_80
  <=> sK3 = sK7(k3_enumset1(sK1,sK5,sK4,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_80])])).

fof(f813,plain,(
    ! [X4,X2,X0,X3,X1] : ~ r2_hidden(X0,sK7(k3_enumset1(X1,X2,X3,X4,X0))) ),
    inference(unit_resulting_resolution,[],[f408,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK7(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(condensation,[],[f48])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,sK7(X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK7(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK7(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f19,f27])).

fof(f27,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK7(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK7(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

fof(f408,plain,(
    ! [X4,X2,X0,X3,X1] : r2_hidden(X0,k3_enumset1(X1,X2,X3,X4,X0)) ),
    inference(unit_resulting_resolution,[],[f68,f63])).

fof(f63,plain,(
    ! [X4,X2,X7,X5,X3,X1] :
      ( ~ sP0(X7,X1,X2,X3,X4,X5)
      | r2_hidden(X7,X5) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r2_hidden(X7,X5)
      | X0 != X7
      | ~ sP0(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( sP0(X0,X1,X2,X3,X4,X5)
        | ( ( ( sK8(X0,X1,X2,X3,X4,X5) != X0
              & sK8(X0,X1,X2,X3,X4,X5) != X1
              & sK8(X0,X1,X2,X3,X4,X5) != X2
              & sK8(X0,X1,X2,X3,X4,X5) != X3
              & sK8(X0,X1,X2,X3,X4,X5) != X4 )
            | ~ r2_hidden(sK8(X0,X1,X2,X3,X4,X5),X5) )
          & ( sK8(X0,X1,X2,X3,X4,X5) = X0
            | sK8(X0,X1,X2,X3,X4,X5) = X1
            | sK8(X0,X1,X2,X3,X4,X5) = X2
            | sK8(X0,X1,X2,X3,X4,X5) = X3
            | sK8(X0,X1,X2,X3,X4,X5) = X4
            | r2_hidden(sK8(X0,X1,X2,X3,X4,X5),X5) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X5)
              | ( X0 != X7
                & X1 != X7
                & X2 != X7
                & X3 != X7
                & X4 != X7 ) )
            & ( X0 = X7
              | X1 = X7
              | X2 = X7
              | X3 = X7
              | X4 = X7
              | ~ r2_hidden(X7,X5) ) )
        | ~ sP0(X0,X1,X2,X3,X4,X5) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f31,f32])).

fof(f32,plain,(
    ! [X5,X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( ( ( X0 != X6
              & X1 != X6
              & X2 != X6
              & X3 != X6
              & X4 != X6 )
            | ~ r2_hidden(X6,X5) )
          & ( X0 = X6
            | X1 = X6
            | X2 = X6
            | X3 = X6
            | X4 = X6
            | r2_hidden(X6,X5) ) )
     => ( ( ( sK8(X0,X1,X2,X3,X4,X5) != X0
            & sK8(X0,X1,X2,X3,X4,X5) != X1
            & sK8(X0,X1,X2,X3,X4,X5) != X2
            & sK8(X0,X1,X2,X3,X4,X5) != X3
            & sK8(X0,X1,X2,X3,X4,X5) != X4 )
          | ~ r2_hidden(sK8(X0,X1,X2,X3,X4,X5),X5) )
        & ( sK8(X0,X1,X2,X3,X4,X5) = X0
          | sK8(X0,X1,X2,X3,X4,X5) = X1
          | sK8(X0,X1,X2,X3,X4,X5) = X2
          | sK8(X0,X1,X2,X3,X4,X5) = X3
          | sK8(X0,X1,X2,X3,X4,X5) = X4
          | r2_hidden(sK8(X0,X1,X2,X3,X4,X5),X5) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( sP0(X0,X1,X2,X3,X4,X5)
        | ? [X6] :
            ( ( ( X0 != X6
                & X1 != X6
                & X2 != X6
                & X3 != X6
                & X4 != X6 )
              | ~ r2_hidden(X6,X5) )
            & ( X0 = X6
              | X1 = X6
              | X2 = X6
              | X3 = X6
              | X4 = X6
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X5)
              | ( X0 != X7
                & X1 != X7
                & X2 != X7
                & X3 != X7
                & X4 != X7 ) )
            & ( X0 = X7
              | X1 = X7
              | X2 = X7
              | X3 = X7
              | X4 = X7
              | ~ r2_hidden(X7,X5) ) )
        | ~ sP0(X0,X1,X2,X3,X4,X5) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X4,X3,X2,X1,X0,X5] :
      ( ( sP0(X4,X3,X2,X1,X0,X5)
        | ? [X6] :
            ( ( ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 )
              | ~ r2_hidden(X6,X5) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X5)
              | ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 ) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | ~ r2_hidden(X6,X5) ) )
        | ~ sP0(X4,X3,X2,X1,X0,X5) ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X4,X3,X2,X1,X0,X5] :
      ( ( sP0(X4,X3,X2,X1,X0,X5)
        | ? [X6] :
            ( ( ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 )
              | ~ r2_hidden(X6,X5) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X5)
              | ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 ) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | ~ r2_hidden(X6,X5) ) )
        | ~ sP0(X4,X3,X2,X1,X0,X5) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X4,X3,X2,X1,X0,X5] :
      ( sP0(X4,X3,X2,X1,X0,X5)
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ( X4 = X6
            | X3 = X6
            | X2 = X6
            | X1 = X6
            | X0 = X6 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] : sP0(X4,X3,X2,X1,X0,k3_enumset1(X0,X1,X2,X3,X4)) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sP0(X4,X3,X2,X1,X0,X5)
      | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( k3_enumset1(X0,X1,X2,X3,X4) = X5
        | ~ sP0(X4,X3,X2,X1,X0,X5) )
      & ( sP0(X4,X3,X2,X1,X0,X5)
        | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> sP0(X4,X3,X2,X1,X0,X5) ) ),
    inference(definition_folding,[],[f20,f21])).

fof(f20,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ( X4 = X6
            | X3 = X6
            | X2 = X6
            | X1 = X6
            | X0 = X6 ) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ~ ( X4 != X6
              & X3 != X6
              & X2 != X6
              & X1 != X6
              & X0 != X6 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_enumset1)).

fof(f3330,plain,
    ( spl9_80
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f3313,f96,f91,f86,f76,f3327])).

fof(f76,plain,
    ( spl9_2
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f86,plain,
    ( spl9_4
  <=> r2_hidden(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f91,plain,
    ( spl9_5
  <=> r2_hidden(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f96,plain,
    ( spl9_6
  <=> r2_hidden(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f3313,plain,
    ( sK3 = sK7(k3_enumset1(sK1,sK5,sK4,sK3,sK2))
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(unit_resulting_resolution,[],[f88,f3212])).

fof(f3212,plain,
    ( ! [X7] :
        ( ~ r2_hidden(X7,sK4)
        | sK7(k3_enumset1(sK1,sK5,sK4,X7,sK2)) = X7 )
    | ~ spl9_2
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(superposition,[],[f805,f3192])).

fof(f3192,plain,
    ( ! [X0] :
        ( sK4 = sK7(k3_enumset1(sK1,sK5,sK4,X0,sK2))
        | sK7(k3_enumset1(sK1,sK5,sK4,X0,sK2)) = X0 )
    | ~ spl9_2
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(resolution,[],[f3082,f93])).

fof(f93,plain,
    ( r2_hidden(sK4,sK5)
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f91])).

fof(f3082,plain,
    ( ! [X10,X11] :
        ( ~ r2_hidden(X10,sK5)
        | sK7(k3_enumset1(sK1,sK5,X10,X11,sK2)) = X11
        | sK7(k3_enumset1(sK1,sK5,X10,X11,sK2)) = X10 )
    | ~ spl9_2
    | ~ spl9_6 ),
    inference(superposition,[],[f797,f3036])).

fof(f3036,plain,
    ( ! [X0,X1] :
        ( sK5 = sK7(k3_enumset1(sK1,sK5,X0,X1,sK2))
        | sK7(k3_enumset1(sK1,sK5,X0,X1,sK2)) = X1
        | sK7(k3_enumset1(sK1,sK5,X0,X1,sK2)) = X0 )
    | ~ spl9_2
    | ~ spl9_6 ),
    inference(resolution,[],[f2909,f98])).

fof(f98,plain,
    ( r2_hidden(sK5,sK1)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f96])).

fof(f2909,plain,
    ( ! [X10,X11,X9] :
        ( ~ r2_hidden(X9,sK1)
        | sK7(k3_enumset1(sK1,X9,X10,X11,sK2)) = X9
        | sK7(k3_enumset1(sK1,X9,X10,X11,sK2)) = X11
        | sK7(k3_enumset1(sK1,X9,X10,X11,sK2)) = X10 )
    | ~ spl9_2 ),
    inference(superposition,[],[f764,f2881])).

fof(f2881,plain,
    ( ! [X41,X42,X40] :
        ( sK1 = sK7(k3_enumset1(sK1,X40,X41,X42,sK2))
        | sK7(k3_enumset1(sK1,X40,X41,X42,sK2)) = X40
        | sK7(k3_enumset1(sK1,X40,X41,X42,sK2)) = X42
        | sK7(k3_enumset1(sK1,X40,X41,X42,sK2)) = X41 )
    | ~ spl9_2 ),
    inference(resolution,[],[f1667,f78])).

fof(f78,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f1667,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ r2_hidden(X5,X9)
      | sK7(k3_enumset1(X5,X6,X7,X8,X9)) = X6
      | sK7(k3_enumset1(X5,X6,X7,X8,X9)) = X5
      | sK7(k3_enumset1(X5,X6,X7,X8,X9)) = X8
      | sK7(k3_enumset1(X5,X6,X7,X8,X9)) = X7 ) ),
    inference(superposition,[],[f731,f962])).

fof(f962,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sK7(k3_enumset1(X0,X1,X2,X3,X4)) = X4
      | sK7(k3_enumset1(X0,X1,X2,X3,X4)) = X1
      | sK7(k3_enumset1(X0,X1,X2,X3,X4)) = X0
      | sK7(k3_enumset1(X0,X1,X2,X3,X4)) = X3
      | sK7(k3_enumset1(X0,X1,X2,X3,X4)) = X2 ) ),
    inference(resolution,[],[f730,f466])).

fof(f466,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(X1,k3_enumset1(X4,X3,X2,X0,X5))
      | X1 = X2
      | X1 = X3
      | X1 = X4
      | X0 = X1
      | X1 = X5 ) ),
    inference(resolution,[],[f49,f68])).

fof(f49,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3,X4,X5)
      | X1 = X7
      | X2 = X7
      | X3 = X7
      | X4 = X7
      | ~ r2_hidden(X7,X5)
      | X0 = X7 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f730,plain,(
    ! [X4,X2,X0,X3,X1] : r2_hidden(sK7(k3_enumset1(X0,X1,X2,X3,X4)),k3_enumset1(X0,X1,X2,X3,X4)) ),
    inference(unit_resulting_resolution,[],[f404,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X1),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f404,plain,(
    ! [X4,X2,X0,X3,X1] : r2_hidden(X0,k3_enumset1(X0,X1,X2,X3,X4)) ),
    inference(unit_resulting_resolution,[],[f68,f67])).

fof(f67,plain,(
    ! [X2,X0,X7,X5,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3,X7,X5)
      | r2_hidden(X7,X5) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r2_hidden(X7,X5)
      | X4 != X7
      | ~ sP0(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f731,plain,(
    ! [X4,X2,X0,X3,X1] : ~ r2_hidden(X0,sK7(k3_enumset1(X0,X1,X2,X3,X4))) ),
    inference(unit_resulting_resolution,[],[f404,f69])).

fof(f764,plain,(
    ! [X4,X2,X0,X3,X1] : ~ r2_hidden(X0,sK7(k3_enumset1(X1,X0,X2,X3,X4))) ),
    inference(unit_resulting_resolution,[],[f405,f69])).

fof(f405,plain,(
    ! [X4,X2,X0,X3,X1] : r2_hidden(X0,k3_enumset1(X1,X0,X2,X3,X4)) ),
    inference(unit_resulting_resolution,[],[f68,f66])).

fof(f66,plain,(
    ! [X4,X2,X0,X7,X5,X1] :
      ( ~ sP0(X0,X1,X2,X7,X4,X5)
      | r2_hidden(X7,X5) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r2_hidden(X7,X5)
      | X3 != X7
      | ~ sP0(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f797,plain,(
    ! [X4,X2,X0,X3,X1] : ~ r2_hidden(X0,sK7(k3_enumset1(X1,X2,X0,X3,X4))) ),
    inference(unit_resulting_resolution,[],[f406,f69])).

fof(f406,plain,(
    ! [X4,X2,X0,X3,X1] : r2_hidden(X0,k3_enumset1(X1,X2,X0,X3,X4)) ),
    inference(unit_resulting_resolution,[],[f68,f65])).

fof(f65,plain,(
    ! [X4,X0,X7,X5,X3,X1] :
      ( ~ sP0(X0,X1,X7,X3,X4,X5)
      | r2_hidden(X7,X5) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r2_hidden(X7,X5)
      | X2 != X7
      | ~ sP0(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f805,plain,(
    ! [X4,X2,X0,X3,X1] : ~ r2_hidden(X0,sK7(k3_enumset1(X1,X2,X3,X0,X4))) ),
    inference(unit_resulting_resolution,[],[f407,f69])).

fof(f407,plain,(
    ! [X4,X2,X0,X3,X1] : r2_hidden(X0,k3_enumset1(X1,X2,X3,X0,X4)) ),
    inference(unit_resulting_resolution,[],[f68,f64])).

fof(f64,plain,(
    ! [X4,X2,X0,X7,X5,X3] :
      ( ~ sP0(X0,X7,X2,X3,X4,X5)
      | r2_hidden(X7,X5) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r2_hidden(X7,X5)
      | X1 != X7
      | ~ sP0(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f88,plain,
    ( r2_hidden(sK3,sK4)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f86])).

fof(f3308,plain,
    ( ~ spl9_79
    | spl9_10
    | spl9_78 ),
    inference(avatar_split_clause,[],[f3303,f3294,f128,f3305])).

fof(f3305,plain,
    ( spl9_79
  <=> m1_subset_1(sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_79])])).

fof(f128,plain,
    ( spl9_10
  <=> v1_xboole_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f3294,plain,
    ( spl9_78
  <=> r2_hidden(sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_78])])).

fof(f3303,plain,
    ( ~ m1_subset_1(sK4,sK4)
    | spl9_10
    | spl9_78 ),
    inference(unit_resulting_resolution,[],[f130,f3296,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f3296,plain,
    ( ~ r2_hidden(sK4,sK4)
    | spl9_78 ),
    inference(avatar_component_clause,[],[f3294])).

fof(f130,plain,
    ( ~ v1_xboole_0(sK4)
    | spl9_10 ),
    inference(avatar_component_clause,[],[f128])).

fof(f3297,plain,
    ( spl9_75
    | ~ spl9_78
    | ~ spl9_2
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f3211,f96,f91,f76,f3294,f3271])).

fof(f3271,plain,
    ( spl9_75
  <=> ! [X3] : sK7(k3_enumset1(sK1,sK5,sK4,X3,sK2)) = X3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_75])])).

fof(f3211,plain,
    ( ! [X6] :
        ( ~ r2_hidden(sK4,sK4)
        | sK7(k3_enumset1(sK1,sK5,sK4,X6,sK2)) = X6 )
    | ~ spl9_2
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(superposition,[],[f797,f3192])).

fof(f3288,plain,
    ( ~ spl9_77
    | spl9_10
    | spl9_76 ),
    inference(avatar_split_clause,[],[f3283,f3274,f128,f3285])).

fof(f3285,plain,
    ( spl9_77
  <=> m1_subset_1(sK1,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_77])])).

fof(f3274,plain,
    ( spl9_76
  <=> r2_hidden(sK1,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_76])])).

fof(f3283,plain,
    ( ~ m1_subset_1(sK1,sK4)
    | spl9_10
    | spl9_76 ),
    inference(unit_resulting_resolution,[],[f130,f3276,f43])).

fof(f3276,plain,
    ( ~ r2_hidden(sK1,sK4)
    | spl9_76 ),
    inference(avatar_component_clause,[],[f3274])).

fof(f3277,plain,
    ( spl9_75
    | ~ spl9_76
    | ~ spl9_2
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f3208,f96,f91,f76,f3274,f3271])).

fof(f3208,plain,
    ( ! [X3] :
        ( ~ r2_hidden(sK1,sK4)
        | sK7(k3_enumset1(sK1,sK5,sK4,X3,sK2)) = X3 )
    | ~ spl9_2
    | ~ spl9_5
    | ~ spl9_6 ),
    inference(superposition,[],[f731,f3192])).

fof(f3160,plain,
    ( ~ spl9_74
    | spl9_11
    | spl9_73 ),
    inference(avatar_split_clause,[],[f3155,f3146,f133,f3157])).

fof(f3157,plain,
    ( spl9_74
  <=> m1_subset_1(sK5,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_74])])).

fof(f133,plain,
    ( spl9_11
  <=> v1_xboole_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f3146,plain,
    ( spl9_73
  <=> r2_hidden(sK5,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_73])])).

fof(f3155,plain,
    ( ~ m1_subset_1(sK5,sK5)
    | spl9_11
    | spl9_73 ),
    inference(unit_resulting_resolution,[],[f135,f3148,f43])).

fof(f3148,plain,
    ( ~ r2_hidden(sK5,sK5)
    | spl9_73 ),
    inference(avatar_component_clause,[],[f3146])).

fof(f135,plain,
    ( ~ v1_xboole_0(sK5)
    | spl9_11 ),
    inference(avatar_component_clause,[],[f133])).

fof(f3149,plain,
    ( spl9_72
    | ~ spl9_73
    | ~ spl9_2
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f3081,f96,f76,f3146,f3143])).

fof(f3143,plain,
    ( spl9_72
  <=> ! [X9,X8] :
        ( sK7(k3_enumset1(sK1,sK5,X8,X9,sK2)) = X9
        | sK7(k3_enumset1(sK1,sK5,X8,X9,sK2)) = X8 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_72])])).

fof(f3081,plain,
    ( ! [X8,X9] :
        ( ~ r2_hidden(sK5,sK5)
        | sK7(k3_enumset1(sK1,sK5,X8,X9,sK2)) = X9
        | sK7(k3_enumset1(sK1,sK5,X8,X9,sK2)) = X8 )
    | ~ spl9_2
    | ~ spl9_6 ),
    inference(superposition,[],[f764,f3036])).

fof(f3004,plain,
    ( ~ spl9_71
    | spl9_12
    | spl9_70 ),
    inference(avatar_split_clause,[],[f2999,f2990,f138,f3001])).

fof(f3001,plain,
    ( spl9_71
  <=> m1_subset_1(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_71])])).

fof(f138,plain,
    ( spl9_12
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f2990,plain,
    ( spl9_70
  <=> r2_hidden(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_70])])).

fof(f2999,plain,
    ( ~ m1_subset_1(sK1,sK1)
    | spl9_12
    | spl9_70 ),
    inference(unit_resulting_resolution,[],[f140,f2992,f43])).

fof(f2992,plain,
    ( ~ r2_hidden(sK1,sK1)
    | spl9_70 ),
    inference(avatar_component_clause,[],[f2990])).

fof(f140,plain,
    ( ~ v1_xboole_0(sK1)
    | spl9_12 ),
    inference(avatar_component_clause,[],[f138])).

fof(f2993,plain,
    ( spl9_69
    | ~ spl9_70
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f2907,f76,f2990,f2987])).

fof(f2987,plain,
    ( spl9_69
  <=> ! [X3,X5,X4] :
        ( sK7(k3_enumset1(sK1,X3,X4,X5,sK2)) = X3
        | sK7(k3_enumset1(sK1,X3,X4,X5,sK2)) = X4
        | sK7(k3_enumset1(sK1,X3,X4,X5,sK2)) = X5 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_69])])).

fof(f2907,plain,
    ( ! [X4,X5,X3] :
        ( ~ r2_hidden(sK1,sK1)
        | sK7(k3_enumset1(sK1,X3,X4,X5,sK2)) = X3
        | sK7(k3_enumset1(sK1,X3,X4,X5,sK2)) = X5
        | sK7(k3_enumset1(sK1,X3,X4,X5,sK2)) = X4 )
    | ~ spl9_2 ),
    inference(superposition,[],[f731,f2881])).

fof(f1447,plain,
    ( spl9_68
    | ~ spl9_1
    | ~ spl9_7 ),
    inference(avatar_split_clause,[],[f1290,f104,f71,f1444])).

fof(f1444,plain,
    ( spl9_68
  <=> o_0_0_xboole_0 = sK8(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_68])])).

fof(f71,plain,
    ( spl9_1
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f104,plain,
    ( spl9_7
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f1290,plain,
    ( o_0_0_xboole_0 = sK8(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl9_1
    | ~ spl9_7 ),
    inference(forward_demodulation,[],[f1288,f106])).

fof(f106,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f104])).

fof(f1288,plain,
    ( k1_xboole_0 = sK8(k1_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,k1_xboole_0,o_0_0_xboole_0)
    | ~ spl9_1
    | ~ spl9_7 ),
    inference(unit_resulting_resolution,[],[f106,f1266])).

fof(f1266,plain,
    ( ! [X0,X1] :
        ( X0 != X1
        | sK8(X0,X1,X1,X1,X0,o_0_0_xboole_0) = X0 )
    | ~ spl9_1 ),
    inference(equality_factoring,[],[f1251])).

fof(f1251,plain,
    ( ! [X0,X1] :
        ( sK8(X0,X1,X1,X1,X0,o_0_0_xboole_0) = X1
        | sK8(X0,X1,X1,X1,X0,o_0_0_xboole_0) = X0 )
    | ~ spl9_1 ),
    inference(equality_resolution,[],[f1247])).

fof(f1247,plain,
    ( ! [X2,X0,X1] :
        ( X1 != X2
        | sK8(X0,X1,X2,X2,X0,o_0_0_xboole_0) = X1
        | sK8(X0,X1,X2,X2,X0,o_0_0_xboole_0) = X0 )
    | ~ spl9_1 ),
    inference(equality_factoring,[],[f1232])).

fof(f1232,plain,
    ( ! [X2,X0,X1] :
        ( sK8(X0,X1,X2,X2,X0,o_0_0_xboole_0) = X2
        | sK8(X0,X1,X2,X2,X0,o_0_0_xboole_0) = X1
        | sK8(X0,X1,X2,X2,X0,o_0_0_xboole_0) = X0 )
    | ~ spl9_1 ),
    inference(equality_resolution,[],[f1186])).

fof(f1186,plain,
    ( ! [X2,X0,X3,X1] :
        ( X2 != X3
        | sK8(X0,X1,X2,X3,X0,o_0_0_xboole_0) = X2
        | sK8(X0,X1,X2,X3,X0,o_0_0_xboole_0) = X1
        | sK8(X0,X1,X2,X3,X0,o_0_0_xboole_0) = X0 )
    | ~ spl9_1 ),
    inference(equality_factoring,[],[f1021])).

fof(f1021,plain,
    ( ! [X39,X41,X42,X40] :
        ( sK8(X39,X40,X41,X42,X39,o_0_0_xboole_0) = X42
        | sK8(X39,X40,X41,X42,X39,o_0_0_xboole_0) = X41
        | sK8(X39,X40,X41,X42,X39,o_0_0_xboole_0) = X40
        | sK8(X39,X40,X41,X42,X39,o_0_0_xboole_0) = X39 )
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f1013,f254])).

fof(f254,plain,
    ( ! [X4,X2,X0,X3,X1] : ~ sP0(X0,X1,X2,X3,X4,o_0_0_xboole_0)
    | ~ spl9_1 ),
    inference(unit_resulting_resolution,[],[f113,f63])).

fof(f113,plain,
    ( ! [X0] : ~ r2_hidden(X0,o_0_0_xboole_0)
    | ~ spl9_1 ),
    inference(unit_resulting_resolution,[],[f73,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(f73,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f71])).

fof(f1013,plain,
    ( ! [X39,X41,X42,X40] :
        ( sK8(X39,X40,X41,X42,X39,o_0_0_xboole_0) = X40
        | sK8(X39,X40,X41,X42,X39,o_0_0_xboole_0) = X41
        | sK8(X39,X40,X41,X42,X39,o_0_0_xboole_0) = X42
        | sP0(X39,X40,X41,X42,X39,o_0_0_xboole_0)
        | sK8(X39,X40,X41,X42,X39,o_0_0_xboole_0) = X39 )
    | ~ spl9_1 ),
    inference(resolution,[],[f824,f113])).

fof(f824,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(sK8(X0,X1,X2,X3,X0,X4),X4)
      | sK8(X0,X1,X2,X3,X0,X4) = X1
      | sK8(X0,X1,X2,X3,X0,X4) = X2
      | sK8(X0,X1,X2,X3,X0,X4) = X3
      | sP0(X0,X1,X2,X3,X0,X4)
      | sK8(X0,X1,X2,X3,X0,X4) = X0 ) ),
    inference(equality_resolution,[],[f617])).

fof(f617,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X0 != X4
      | sK8(X0,X1,X2,X3,X4,X5) = X0
      | sK8(X0,X1,X2,X3,X4,X5) = X1
      | sK8(X0,X1,X2,X3,X4,X5) = X2
      | sK8(X0,X1,X2,X3,X4,X5) = X3
      | sP0(X0,X1,X2,X3,X4,X5)
      | r2_hidden(sK8(X0,X1,X2,X3,X4,X5),X5) ) ),
    inference(equality_factoring,[],[f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sK8(X0,X1,X2,X3,X4,X5) = X4
      | sK8(X0,X1,X2,X3,X4,X5) = X0
      | sK8(X0,X1,X2,X3,X4,X5) = X1
      | sK8(X0,X1,X2,X3,X4,X5) = X2
      | sK8(X0,X1,X2,X3,X4,X5) = X3
      | sP0(X0,X1,X2,X3,X4,X5)
      | r2_hidden(sK8(X0,X1,X2,X3,X4,X5),X5) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f753,plain,
    ( ~ spl9_67
    | ~ spl9_42 ),
    inference(avatar_split_clause,[],[f545,f457,f750])).

fof(f750,plain,
    ( spl9_67
  <=> r2_hidden(sK6(sK5),sK7(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_67])])).

fof(f457,plain,
    ( spl9_42
  <=> r2_hidden(sK6(sK5),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_42])])).

fof(f545,plain,
    ( ~ r2_hidden(sK6(sK5),sK7(sK5))
    | ~ spl9_42 ),
    inference(unit_resulting_resolution,[],[f459,f69])).

fof(f459,plain,
    ( r2_hidden(sK6(sK5),sK5)
    | ~ spl9_42 ),
    inference(avatar_component_clause,[],[f457])).

fof(f748,plain,
    ( ~ spl9_66
    | ~ spl9_41 ),
    inference(avatar_split_clause,[],[f538,f452,f745])).

fof(f745,plain,
    ( spl9_66
  <=> r2_hidden(sK6(sK4),sK7(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_66])])).

fof(f452,plain,
    ( spl9_41
  <=> r2_hidden(sK6(sK4),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_41])])).

fof(f538,plain,
    ( ~ r2_hidden(sK6(sK4),sK7(sK4))
    | ~ spl9_41 ),
    inference(unit_resulting_resolution,[],[f454,f69])).

fof(f454,plain,
    ( r2_hidden(sK6(sK4),sK4)
    | ~ spl9_41 ),
    inference(avatar_component_clause,[],[f452])).

fof(f743,plain,
    ( ~ spl9_65
    | ~ spl9_40 ),
    inference(avatar_split_clause,[],[f531,f447,f740])).

fof(f740,plain,
    ( spl9_65
  <=> r2_hidden(sK6(sK3),sK7(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_65])])).

fof(f447,plain,
    ( spl9_40
  <=> r2_hidden(sK6(sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_40])])).

fof(f531,plain,
    ( ~ r2_hidden(sK6(sK3),sK7(sK3))
    | ~ spl9_40 ),
    inference(unit_resulting_resolution,[],[f449,f69])).

fof(f449,plain,
    ( r2_hidden(sK6(sK3),sK3)
    | ~ spl9_40 ),
    inference(avatar_component_clause,[],[f447])).

fof(f738,plain,
    ( ~ spl9_64
    | ~ spl9_39 ),
    inference(avatar_split_clause,[],[f524,f442,f735])).

fof(f735,plain,
    ( spl9_64
  <=> r2_hidden(sK6(sK2),sK7(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_64])])).

fof(f442,plain,
    ( spl9_39
  <=> r2_hidden(sK6(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_39])])).

fof(f524,plain,
    ( ~ r2_hidden(sK6(sK2),sK7(sK2))
    | ~ spl9_39 ),
    inference(unit_resulting_resolution,[],[f444,f69])).

fof(f444,plain,
    ( r2_hidden(sK6(sK2),sK2)
    | ~ spl9_39 ),
    inference(avatar_component_clause,[],[f442])).

fof(f725,plain,
    ( ~ spl9_63
    | ~ spl9_38 ),
    inference(avatar_split_clause,[],[f517,f435,f722])).

fof(f722,plain,
    ( spl9_63
  <=> r2_hidden(sK6(sK1),sK7(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_63])])).

fof(f435,plain,
    ( spl9_38
  <=> r2_hidden(sK6(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_38])])).

fof(f517,plain,
    ( ~ r2_hidden(sK6(sK1),sK7(sK1))
    | ~ spl9_38 ),
    inference(unit_resulting_resolution,[],[f437,f69])).

fof(f437,plain,
    ( r2_hidden(sK6(sK1),sK1)
    | ~ spl9_38 ),
    inference(avatar_component_clause,[],[f435])).

fof(f680,plain,
    ( ~ spl9_62
    | ~ spl9_32 ),
    inference(avatar_split_clause,[],[f392,f323,f677])).

fof(f677,plain,
    ( spl9_62
  <=> r2_hidden(sK7(sK1),sK7(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_62])])).

fof(f323,plain,
    ( spl9_32
  <=> r2_hidden(sK7(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).

fof(f392,plain,
    ( ~ r2_hidden(sK7(sK1),sK7(sK1))
    | ~ spl9_32 ),
    inference(unit_resulting_resolution,[],[f325,f69])).

fof(f325,plain,
    ( r2_hidden(sK7(sK1),sK1)
    | ~ spl9_32 ),
    inference(avatar_component_clause,[],[f323])).

fof(f675,plain,
    ( ~ spl9_61
    | ~ spl9_31 ),
    inference(avatar_split_clause,[],[f385,f318,f672])).

fof(f672,plain,
    ( spl9_61
  <=> r2_hidden(sK7(sK5),sK7(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_61])])).

fof(f318,plain,
    ( spl9_31
  <=> r2_hidden(sK7(sK5),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).

fof(f385,plain,
    ( ~ r2_hidden(sK7(sK5),sK7(sK5))
    | ~ spl9_31 ),
    inference(unit_resulting_resolution,[],[f320,f69])).

fof(f320,plain,
    ( r2_hidden(sK7(sK5),sK5)
    | ~ spl9_31 ),
    inference(avatar_component_clause,[],[f318])).

fof(f670,plain,
    ( ~ spl9_60
    | ~ spl9_30 ),
    inference(avatar_split_clause,[],[f378,f313,f667])).

fof(f667,plain,
    ( spl9_60
  <=> r2_hidden(sK7(sK4),sK7(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_60])])).

fof(f313,plain,
    ( spl9_30
  <=> r2_hidden(sK7(sK4),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).

fof(f378,plain,
    ( ~ r2_hidden(sK7(sK4),sK7(sK4))
    | ~ spl9_30 ),
    inference(unit_resulting_resolution,[],[f315,f69])).

fof(f315,plain,
    ( r2_hidden(sK7(sK4),sK4)
    | ~ spl9_30 ),
    inference(avatar_component_clause,[],[f313])).

fof(f665,plain,
    ( ~ spl9_59
    | ~ spl9_29 ),
    inference(avatar_split_clause,[],[f371,f308,f662])).

fof(f662,plain,
    ( spl9_59
  <=> r2_hidden(sK7(sK3),sK7(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_59])])).

fof(f308,plain,
    ( spl9_29
  <=> r2_hidden(sK7(sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).

fof(f371,plain,
    ( ~ r2_hidden(sK7(sK3),sK7(sK3))
    | ~ spl9_29 ),
    inference(unit_resulting_resolution,[],[f310,f69])).

fof(f310,plain,
    ( r2_hidden(sK7(sK3),sK3)
    | ~ spl9_29 ),
    inference(avatar_component_clause,[],[f308])).

fof(f651,plain,
    ( ~ spl9_58
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f358,f297,f648])).

fof(f648,plain,
    ( spl9_58
  <=> r2_hidden(sK7(sK2),sK7(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_58])])).

fof(f297,plain,
    ( spl9_28
  <=> r2_hidden(sK7(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).

fof(f358,plain,
    ( ~ r2_hidden(sK7(sK2),sK7(sK2))
    | ~ spl9_28 ),
    inference(unit_resulting_resolution,[],[f299,f69])).

fof(f299,plain,
    ( r2_hidden(sK7(sK2),sK2)
    | ~ spl9_28 ),
    inference(avatar_component_clause,[],[f297])).

fof(f606,plain,
    ( ~ spl9_57
    | ~ spl9_42 ),
    inference(avatar_split_clause,[],[f541,f457,f603])).

fof(f603,plain,
    ( spl9_57
  <=> r2_hidden(sK5,sK6(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_57])])).

fof(f541,plain,
    ( ~ r2_hidden(sK5,sK6(sK5))
    | ~ spl9_42 ),
    inference(unit_resulting_resolution,[],[f459,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f601,plain,
    ( ~ spl9_56
    | ~ spl9_41 ),
    inference(avatar_split_clause,[],[f534,f452,f598])).

fof(f598,plain,
    ( spl9_56
  <=> r2_hidden(sK4,sK6(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_56])])).

fof(f534,plain,
    ( ~ r2_hidden(sK4,sK6(sK4))
    | ~ spl9_41 ),
    inference(unit_resulting_resolution,[],[f454,f44])).

fof(f596,plain,
    ( ~ spl9_55
    | ~ spl9_40 ),
    inference(avatar_split_clause,[],[f527,f447,f593])).

fof(f593,plain,
    ( spl9_55
  <=> r2_hidden(sK3,sK6(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_55])])).

fof(f527,plain,
    ( ~ r2_hidden(sK3,sK6(sK3))
    | ~ spl9_40 ),
    inference(unit_resulting_resolution,[],[f449,f44])).

fof(f591,plain,
    ( ~ spl9_54
    | ~ spl9_39 ),
    inference(avatar_split_clause,[],[f520,f442,f588])).

fof(f588,plain,
    ( spl9_54
  <=> r2_hidden(sK2,sK6(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_54])])).

fof(f520,plain,
    ( ~ r2_hidden(sK2,sK6(sK2))
    | ~ spl9_39 ),
    inference(unit_resulting_resolution,[],[f444,f44])).

fof(f586,plain,
    ( ~ spl9_53
    | ~ spl9_38 ),
    inference(avatar_split_clause,[],[f513,f435,f583])).

fof(f583,plain,
    ( spl9_53
  <=> r2_hidden(sK1,sK6(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_53])])).

fof(f513,plain,
    ( ~ r2_hidden(sK1,sK6(sK1))
    | ~ spl9_38 ),
    inference(unit_resulting_resolution,[],[f437,f44])).

fof(f511,plain,
    ( ~ spl9_52
    | ~ spl9_32 ),
    inference(avatar_split_clause,[],[f396,f323,f508])).

fof(f508,plain,
    ( spl9_52
  <=> r2_hidden(sK1,sK7(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_52])])).

fof(f396,plain,
    ( ~ r2_hidden(sK1,sK7(sK1))
    | ~ spl9_32 ),
    inference(unit_resulting_resolution,[],[f325,f44])).

fof(f506,plain,
    ( spl9_51
    | ~ spl9_32 ),
    inference(avatar_split_clause,[],[f394,f323,f503])).

fof(f503,plain,
    ( spl9_51
  <=> m1_subset_1(sK7(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_51])])).

fof(f394,plain,
    ( m1_subset_1(sK7(sK1),sK1)
    | ~ spl9_32 ),
    inference(unit_resulting_resolution,[],[f325,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f501,plain,
    ( ~ spl9_50
    | ~ spl9_31 ),
    inference(avatar_split_clause,[],[f389,f318,f498])).

fof(f498,plain,
    ( spl9_50
  <=> r2_hidden(sK5,sK7(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_50])])).

fof(f389,plain,
    ( ~ r2_hidden(sK5,sK7(sK5))
    | ~ spl9_31 ),
    inference(unit_resulting_resolution,[],[f320,f44])).

fof(f496,plain,
    ( spl9_49
    | ~ spl9_31 ),
    inference(avatar_split_clause,[],[f387,f318,f493])).

fof(f493,plain,
    ( spl9_49
  <=> m1_subset_1(sK7(sK5),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_49])])).

fof(f387,plain,
    ( m1_subset_1(sK7(sK5),sK5)
    | ~ spl9_31 ),
    inference(unit_resulting_resolution,[],[f320,f45])).

fof(f491,plain,
    ( ~ spl9_48
    | ~ spl9_30 ),
    inference(avatar_split_clause,[],[f382,f313,f488])).

fof(f488,plain,
    ( spl9_48
  <=> r2_hidden(sK4,sK7(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_48])])).

fof(f382,plain,
    ( ~ r2_hidden(sK4,sK7(sK4))
    | ~ spl9_30 ),
    inference(unit_resulting_resolution,[],[f315,f44])).

fof(f486,plain,
    ( spl9_47
    | ~ spl9_30 ),
    inference(avatar_split_clause,[],[f380,f313,f483])).

fof(f483,plain,
    ( spl9_47
  <=> m1_subset_1(sK7(sK4),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_47])])).

fof(f380,plain,
    ( m1_subset_1(sK7(sK4),sK4)
    | ~ spl9_30 ),
    inference(unit_resulting_resolution,[],[f315,f45])).

fof(f481,plain,
    ( ~ spl9_46
    | ~ spl9_29 ),
    inference(avatar_split_clause,[],[f375,f308,f478])).

fof(f478,plain,
    ( spl9_46
  <=> r2_hidden(sK3,sK7(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_46])])).

fof(f375,plain,
    ( ~ r2_hidden(sK3,sK7(sK3))
    | ~ spl9_29 ),
    inference(unit_resulting_resolution,[],[f310,f44])).

fof(f476,plain,
    ( spl9_45
    | ~ spl9_29 ),
    inference(avatar_split_clause,[],[f373,f308,f473])).

fof(f473,plain,
    ( spl9_45
  <=> m1_subset_1(sK7(sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_45])])).

fof(f373,plain,
    ( m1_subset_1(sK7(sK3),sK3)
    | ~ spl9_29 ),
    inference(unit_resulting_resolution,[],[f310,f45])).

fof(f471,plain,
    ( ~ spl9_44
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f362,f297,f468])).

fof(f468,plain,
    ( spl9_44
  <=> r2_hidden(sK2,sK7(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_44])])).

fof(f362,plain,
    ( ~ r2_hidden(sK2,sK7(sK2))
    | ~ spl9_28 ),
    inference(unit_resulting_resolution,[],[f299,f44])).

fof(f465,plain,
    ( spl9_43
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f360,f297,f462])).

fof(f462,plain,
    ( spl9_43
  <=> m1_subset_1(sK7(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_43])])).

fof(f360,plain,
    ( m1_subset_1(sK7(sK2),sK2)
    | ~ spl9_28 ),
    inference(unit_resulting_resolution,[],[f299,f45])).

fof(f460,plain,
    ( spl9_42
    | spl9_11 ),
    inference(avatar_split_clause,[],[f233,f133,f457])).

fof(f233,plain,
    ( r2_hidden(sK6(sK5),sK5)
    | spl9_11 ),
    inference(unit_resulting_resolution,[],[f135,f42,f43])).

fof(f42,plain,(
    ! [X0] : m1_subset_1(sK6(X0),X0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] : m1_subset_1(sK6(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f4,f25])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f4,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f455,plain,
    ( spl9_41
    | spl9_10 ),
    inference(avatar_split_clause,[],[f232,f128,f452])).

fof(f232,plain,
    ( r2_hidden(sK6(sK4),sK4)
    | spl9_10 ),
    inference(unit_resulting_resolution,[],[f130,f42,f43])).

fof(f450,plain,
    ( spl9_40
    | spl9_9 ),
    inference(avatar_split_clause,[],[f231,f121,f447])).

fof(f121,plain,
    ( spl9_9
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f231,plain,
    ( r2_hidden(sK6(sK3),sK3)
    | spl9_9 ),
    inference(unit_resulting_resolution,[],[f123,f42,f43])).

fof(f123,plain,
    ( ~ v1_xboole_0(sK3)
    | spl9_9 ),
    inference(avatar_component_clause,[],[f121])).

fof(f445,plain,
    ( spl9_39
    | spl9_8 ),
    inference(avatar_split_clause,[],[f230,f116,f442])).

fof(f116,plain,
    ( spl9_8
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f230,plain,
    ( r2_hidden(sK6(sK2),sK2)
    | spl9_8 ),
    inference(unit_resulting_resolution,[],[f118,f42,f43])).

fof(f118,plain,
    ( ~ v1_xboole_0(sK2)
    | spl9_8 ),
    inference(avatar_component_clause,[],[f116])).

fof(f438,plain,
    ( spl9_38
    | spl9_12 ),
    inference(avatar_split_clause,[],[f229,f138,f435])).

fof(f229,plain,
    ( r2_hidden(sK6(sK1),sK1)
    | spl9_12 ),
    inference(unit_resulting_resolution,[],[f140,f42,f43])).

fof(f357,plain,
    ( ~ spl9_37
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f222,f96,f354])).

fof(f354,plain,
    ( spl9_37
  <=> r2_hidden(sK5,sK7(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_37])])).

fof(f222,plain,
    ( ~ r2_hidden(sK5,sK7(sK1))
    | ~ spl9_6 ),
    inference(unit_resulting_resolution,[],[f98,f69])).

fof(f352,plain,
    ( ~ spl9_36
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f221,f91,f349])).

fof(f349,plain,
    ( spl9_36
  <=> r2_hidden(sK4,sK7(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_36])])).

fof(f221,plain,
    ( ~ r2_hidden(sK4,sK7(sK5))
    | ~ spl9_5 ),
    inference(unit_resulting_resolution,[],[f93,f69])).

fof(f347,plain,
    ( ~ spl9_35
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f220,f86,f344])).

fof(f344,plain,
    ( spl9_35
  <=> r2_hidden(sK3,sK7(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_35])])).

fof(f220,plain,
    ( ~ r2_hidden(sK3,sK7(sK4))
    | ~ spl9_4 ),
    inference(unit_resulting_resolution,[],[f88,f69])).

fof(f342,plain,
    ( ~ spl9_34
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f219,f81,f339])).

fof(f339,plain,
    ( spl9_34
  <=> r2_hidden(sK2,sK7(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_34])])).

fof(f219,plain,
    ( ~ r2_hidden(sK2,sK7(sK3))
    | ~ spl9_3 ),
    inference(unit_resulting_resolution,[],[f83,f69])).

fof(f331,plain,
    ( ~ spl9_33
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f218,f76,f328])).

fof(f328,plain,
    ( spl9_33
  <=> r2_hidden(sK1,sK7(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_33])])).

fof(f218,plain,
    ( ~ r2_hidden(sK1,sK7(sK2))
    | ~ spl9_2 ),
    inference(unit_resulting_resolution,[],[f78,f69])).

fof(f326,plain,
    ( spl9_32
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f191,f96,f323])).

fof(f191,plain,
    ( r2_hidden(sK7(sK1),sK1)
    | ~ spl9_6 ),
    inference(unit_resulting_resolution,[],[f98,f47])).

fof(f321,plain,
    ( spl9_31
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f190,f91,f318])).

fof(f190,plain,
    ( r2_hidden(sK7(sK5),sK5)
    | ~ spl9_5 ),
    inference(unit_resulting_resolution,[],[f93,f47])).

fof(f316,plain,
    ( spl9_30
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f189,f86,f313])).

fof(f189,plain,
    ( r2_hidden(sK7(sK4),sK4)
    | ~ spl9_4 ),
    inference(unit_resulting_resolution,[],[f88,f47])).

fof(f311,plain,
    ( spl9_29
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f188,f81,f308])).

fof(f188,plain,
    ( r2_hidden(sK7(sK3),sK3)
    | ~ spl9_3 ),
    inference(unit_resulting_resolution,[],[f83,f47])).

fof(f300,plain,
    ( spl9_28
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f187,f76,f297])).

fof(f187,plain,
    ( r2_hidden(sK7(sK2),sK2)
    | ~ spl9_2 ),
    inference(unit_resulting_resolution,[],[f78,f47])).

fof(f279,plain,
    ( ~ spl9_27
    | spl9_11
    | spl9_17 ),
    inference(avatar_split_clause,[],[f228,f183,f133,f276])).

fof(f276,plain,
    ( spl9_27
  <=> m1_subset_1(sK1,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).

fof(f183,plain,
    ( spl9_17
  <=> r2_hidden(sK1,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f228,plain,
    ( ~ m1_subset_1(sK1,sK5)
    | spl9_11
    | spl9_17 ),
    inference(unit_resulting_resolution,[],[f185,f135,f43])).

fof(f185,plain,
    ( ~ r2_hidden(sK1,sK5)
    | spl9_17 ),
    inference(avatar_component_clause,[],[f183])).

fof(f274,plain,
    ( ~ spl9_26
    | spl9_10
    | spl9_16 ),
    inference(avatar_split_clause,[],[f227,f178,f128,f271])).

fof(f271,plain,
    ( spl9_26
  <=> m1_subset_1(sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

fof(f178,plain,
    ( spl9_16
  <=> r2_hidden(sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f227,plain,
    ( ~ m1_subset_1(sK5,sK4)
    | spl9_10
    | spl9_16 ),
    inference(unit_resulting_resolution,[],[f180,f130,f43])).

fof(f180,plain,
    ( ~ r2_hidden(sK5,sK4)
    | spl9_16 ),
    inference(avatar_component_clause,[],[f178])).

fof(f269,plain,
    ( ~ spl9_25
    | spl9_9
    | spl9_15 ),
    inference(avatar_split_clause,[],[f226,f173,f121,f266])).

fof(f266,plain,
    ( spl9_25
  <=> m1_subset_1(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).

fof(f173,plain,
    ( spl9_15
  <=> r2_hidden(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f226,plain,
    ( ~ m1_subset_1(sK4,sK3)
    | spl9_9
    | spl9_15 ),
    inference(unit_resulting_resolution,[],[f175,f123,f43])).

fof(f175,plain,
    ( ~ r2_hidden(sK4,sK3)
    | spl9_15 ),
    inference(avatar_component_clause,[],[f173])).

fof(f264,plain,
    ( ~ spl9_24
    | spl9_8
    | spl9_14 ),
    inference(avatar_split_clause,[],[f225,f163,f116,f261])).

fof(f261,plain,
    ( spl9_24
  <=> m1_subset_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).

fof(f163,plain,
    ( spl9_14
  <=> r2_hidden(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f225,plain,
    ( ~ m1_subset_1(sK3,sK2)
    | spl9_8
    | spl9_14 ),
    inference(unit_resulting_resolution,[],[f165,f118,f43])).

fof(f165,plain,
    ( ~ r2_hidden(sK3,sK2)
    | spl9_14 ),
    inference(avatar_component_clause,[],[f163])).

fof(f253,plain,
    ( ~ spl9_23
    | spl9_12
    | spl9_13 ),
    inference(avatar_split_clause,[],[f224,f158,f138,f250])).

fof(f250,plain,
    ( spl9_23
  <=> m1_subset_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).

fof(f158,plain,
    ( spl9_13
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f224,plain,
    ( ~ m1_subset_1(sK2,sK1)
    | spl9_12
    | spl9_13 ),
    inference(unit_resulting_resolution,[],[f160,f140,f43])).

fof(f160,plain,
    ( ~ r2_hidden(sK2,sK1)
    | spl9_13 ),
    inference(avatar_component_clause,[],[f158])).

fof(f217,plain,
    ( spl9_22
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f171,f96,f214])).

fof(f214,plain,
    ( spl9_22
  <=> m1_subset_1(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f171,plain,
    ( m1_subset_1(sK5,sK1)
    | ~ spl9_6 ),
    inference(unit_resulting_resolution,[],[f98,f45])).

fof(f212,plain,
    ( spl9_21
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f170,f91,f209])).

fof(f209,plain,
    ( spl9_21
  <=> m1_subset_1(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f170,plain,
    ( m1_subset_1(sK4,sK5)
    | ~ spl9_5 ),
    inference(unit_resulting_resolution,[],[f93,f45])).

fof(f207,plain,
    ( spl9_20
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f169,f86,f204])).

fof(f204,plain,
    ( spl9_20
  <=> m1_subset_1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f169,plain,
    ( m1_subset_1(sK3,sK4)
    | ~ spl9_4 ),
    inference(unit_resulting_resolution,[],[f88,f45])).

fof(f202,plain,
    ( spl9_19
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f168,f81,f199])).

fof(f199,plain,
    ( spl9_19
  <=> m1_subset_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f168,plain,
    ( m1_subset_1(sK2,sK3)
    | ~ spl9_3 ),
    inference(unit_resulting_resolution,[],[f83,f45])).

fof(f197,plain,
    ( spl9_18
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f167,f76,f194])).

fof(f194,plain,
    ( spl9_18
  <=> m1_subset_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f167,plain,
    ( m1_subset_1(sK1,sK2)
    | ~ spl9_2 ),
    inference(unit_resulting_resolution,[],[f78,f45])).

fof(f186,plain,
    ( ~ spl9_17
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f151,f96,f183])).

fof(f151,plain,
    ( ~ r2_hidden(sK1,sK5)
    | ~ spl9_6 ),
    inference(unit_resulting_resolution,[],[f98,f44])).

fof(f181,plain,
    ( ~ spl9_16
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f150,f91,f178])).

fof(f150,plain,
    ( ~ r2_hidden(sK5,sK4)
    | ~ spl9_5 ),
    inference(unit_resulting_resolution,[],[f93,f44])).

fof(f176,plain,
    ( ~ spl9_15
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f149,f86,f173])).

fof(f149,plain,
    ( ~ r2_hidden(sK4,sK3)
    | ~ spl9_4 ),
    inference(unit_resulting_resolution,[],[f88,f44])).

fof(f166,plain,
    ( ~ spl9_14
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f148,f81,f163])).

fof(f148,plain,
    ( ~ r2_hidden(sK3,sK2)
    | ~ spl9_3 ),
    inference(unit_resulting_resolution,[],[f83,f44])).

fof(f161,plain,
    ( ~ spl9_13
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f147,f76,f158])).

fof(f147,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ spl9_2 ),
    inference(unit_resulting_resolution,[],[f78,f44])).

fof(f141,plain,
    ( ~ spl9_12
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f112,f96,f138])).

fof(f112,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl9_6 ),
    inference(unit_resulting_resolution,[],[f98,f46])).

fof(f136,plain,
    ( ~ spl9_11
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f111,f91,f133])).

fof(f111,plain,
    ( ~ v1_xboole_0(sK5)
    | ~ spl9_5 ),
    inference(unit_resulting_resolution,[],[f93,f46])).

fof(f131,plain,
    ( ~ spl9_10
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f110,f86,f128])).

fof(f110,plain,
    ( ~ v1_xboole_0(sK4)
    | ~ spl9_4 ),
    inference(unit_resulting_resolution,[],[f88,f46])).

fof(f124,plain,
    ( ~ spl9_9
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f109,f81,f121])).

fof(f109,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl9_3 ),
    inference(unit_resulting_resolution,[],[f83,f46])).

fof(f119,plain,
    ( ~ spl9_8
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f108,f76,f116])).

fof(f108,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl9_2 ),
    inference(unit_resulting_resolution,[],[f78,f46])).

fof(f107,plain,
    ( spl9_7
    | ~ spl9_1 ),
    inference(avatar_split_clause,[],[f100,f71,f104])).

fof(f100,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl9_1 ),
    inference(unit_resulting_resolution,[],[f73,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(f99,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f39,f96])).

fof(f39,plain,(
    r2_hidden(sK5,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( r2_hidden(sK5,sK1)
    & r2_hidden(sK4,sK5)
    & r2_hidden(sK3,sK4)
    & r2_hidden(sK2,sK3)
    & r2_hidden(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f12,f23])).

fof(f23,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( r2_hidden(X4,X0)
        & r2_hidden(X3,X4)
        & r2_hidden(X2,X3)
        & r2_hidden(X1,X2)
        & r2_hidden(X0,X1) )
   => ( r2_hidden(sK5,sK1)
      & r2_hidden(sK4,sK5)
      & r2_hidden(sK3,sK4)
      & r2_hidden(sK2,sK3)
      & r2_hidden(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( r2_hidden(X4,X0)
      & r2_hidden(X3,X4)
      & r2_hidden(X2,X3)
      & r2_hidden(X1,X2)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ~ ( r2_hidden(X4,X0)
          & r2_hidden(X3,X4)
          & r2_hidden(X2,X3)
          & r2_hidden(X1,X2)
          & r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ~ ( r2_hidden(X4,X0)
        & r2_hidden(X3,X4)
        & r2_hidden(X2,X3)
        & r2_hidden(X1,X2)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_ordinal1)).

fof(f94,plain,(
    spl9_5 ),
    inference(avatar_split_clause,[],[f38,f91])).

fof(f38,plain,(
    r2_hidden(sK4,sK5) ),
    inference(cnf_transformation,[],[f24])).

fof(f89,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f37,f86])).

fof(f37,plain,(
    r2_hidden(sK3,sK4) ),
    inference(cnf_transformation,[],[f24])).

fof(f84,plain,(
    spl9_3 ),
    inference(avatar_split_clause,[],[f36,f81])).

fof(f36,plain,(
    r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f79,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f35,f76])).

fof(f35,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f74,plain,(
    spl9_1 ),
    inference(avatar_split_clause,[],[f40,f71])).

fof(f40,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

%------------------------------------------------------------------------------
