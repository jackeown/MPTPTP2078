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
% DateTime   : Thu Dec  3 12:56:03 EST 2020

% Result     : Theorem 3.70s
% Output     : Refutation 3.70s
% Verified   : 
% Statistics : Number of formulae       :  238 ( 585 expanded)
%              Number of leaves         :   52 ( 215 expanded)
%              Depth                    :   15
%              Number of atoms          : 1028 (2757 expanded)
%              Number of equality atoms :  115 ( 323 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4362,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f123,f126,f130,f134,f138,f142,f194,f258,f348,f359,f502,f514,f579,f596,f643,f687,f771,f861,f871,f893,f1359,f1362,f3065,f3956,f3984,f3996,f3998,f4111,f4134,f4139,f4144,f4160,f4237,f4285])).

fof(f4285,plain,
    ( ~ spl14_37
    | ~ spl14_35 ),
    inference(avatar_split_clause,[],[f848,f384,f392])).

fof(f392,plain,
    ( spl14_37
  <=> r1_tarski(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_37])])).

fof(f384,plain,
    ( spl14_35
  <=> r2_hidden(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_35])])).

fof(f848,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | ~ spl14_35 ),
    inference(resolution,[],[f385,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f385,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl14_35 ),
    inference(avatar_component_clause,[],[f384])).

fof(f4237,plain,
    ( k1_xboole_0 != sK12(sK2,sK1)
    | sK0 != sK1
    | ~ r2_hidden(sK0,sK12(sK2,sK1))
    | r2_hidden(sK0,k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f4160,plain,
    ( spl14_107
    | spl14_421
    | ~ spl14_6
    | ~ spl14_28
    | ~ spl14_296 ),
    inference(avatar_split_clause,[],[f3070,f3063,f346,f140,f4158,f994])).

fof(f994,plain,
    ( spl14_107
  <=> r2_hidden(k4_tarski(sK1,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_107])])).

fof(f4158,plain,
    ( spl14_421
  <=> k1_xboole_0 = sK12(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_421])])).

fof(f140,plain,
    ( spl14_6
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_6])])).

fof(f346,plain,
    ( spl14_28
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | r2_hidden(sK3(sK2,X0),X0)
        | ~ r1_tarski(X0,k3_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_28])])).

fof(f3063,plain,
    ( spl14_296
  <=> ! [X5] :
        ( k1_xboole_0 = sK12(sK2,X5)
        | ~ r2_hidden(sK3(sK2,sK12(sK2,X5)),sK12(sK2,sK1))
        | r2_hidden(k4_tarski(sK1,X5),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_296])])).

fof(f3070,plain,
    ( k1_xboole_0 = sK12(sK2,sK1)
    | r2_hidden(k4_tarski(sK1,sK1),sK2)
    | ~ spl14_6
    | ~ spl14_28
    | ~ spl14_296 ),
    inference(duplicate_literal_removal,[],[f3066])).

fof(f3066,plain,
    ( k1_xboole_0 = sK12(sK2,sK1)
    | r2_hidden(k4_tarski(sK1,sK1),sK2)
    | k1_xboole_0 = sK12(sK2,sK1)
    | ~ spl14_6
    | ~ spl14_28
    | ~ spl14_296 ),
    inference(resolution,[],[f3064,f352])).

fof(f352,plain,
    ( ! [X2] :
        ( r2_hidden(sK3(sK2,sK12(sK2,X2)),sK12(sK2,X2))
        | k1_xboole_0 = sK12(sK2,X2) )
    | ~ spl14_6
    | ~ spl14_28 ),
    inference(resolution,[],[f347,f176])).

fof(f176,plain,
    ( ! [X0] : r1_tarski(sK12(sK2,X0),k3_relat_1(sK2))
    | ~ spl14_6 ),
    inference(duplicate_literal_removal,[],[f174])).

fof(f174,plain,
    ( ! [X0] :
        ( r1_tarski(sK12(sK2,X0),k3_relat_1(sK2))
        | r1_tarski(sK12(sK2,X0),k3_relat_1(sK2)) )
    | ~ spl14_6 ),
    inference(resolution,[],[f173,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK13(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK13(X0,X1),X1)
          & r2_hidden(sK13(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f62,f63])).

fof(f63,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK13(X0,X1),X1)
        & r2_hidden(sK13(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f173,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK13(sK12(sK2,X0),X1),k3_relat_1(sK2))
        | r1_tarski(sK12(sK2,X0),X1) )
    | ~ spl14_6 ),
    inference(resolution,[],[f172,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK13(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f172,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK12(sK2,X1))
        | r2_hidden(X0,k3_relat_1(sK2)) )
    | ~ spl14_6 ),
    inference(resolution,[],[f99,f141])).

fof(f141,plain,
    ( v1_relat_1(sK2)
    | ~ spl14_6 ),
    inference(avatar_component_clause,[],[f140])).

fof(f99,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X3,sK12(X0,X1))
      | r2_hidden(X3,k3_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( ( r2_hidden(X3,sK12(X0,X1))
            | r2_hidden(k4_tarski(X3,X1),X0)
            | ~ r2_hidden(X3,k3_relat_1(X0)) )
          & ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
              & r2_hidden(X3,k3_relat_1(X0)) )
            | ~ r2_hidden(X3,sK12(X0,X1)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f56,f57])).

fof(f57,plain,(
    ! [X1,X0] :
      ( ? [X2] :
        ! [X3] :
          ( ( r2_hidden(X3,X2)
            | r2_hidden(k4_tarski(X3,X1),X0)
            | ~ r2_hidden(X3,k3_relat_1(X0)) )
          & ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
              & r2_hidden(X3,k3_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) ) )
     => ! [X3] :
          ( ( r2_hidden(X3,sK12(X0,X1))
            | r2_hidden(k4_tarski(X3,X1),X0)
            | ~ r2_hidden(X3,k3_relat_1(X0)) )
          & ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
              & r2_hidden(X3,k3_relat_1(X0)) )
            | ~ r2_hidden(X3,sK12(X0,X1)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ? [X2] :
        ! [X3] :
          ( ( r2_hidden(X3,X2)
            | r2_hidden(k4_tarski(X3,X1),X0)
            | ~ r2_hidden(X3,k3_relat_1(X0)) )
          & ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
              & r2_hidden(X3,k3_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ? [X2] :
        ! [X3] :
          ( ( r2_hidden(X3,X2)
            | r2_hidden(k4_tarski(X3,X1),X0)
            | ~ r2_hidden(X3,k3_relat_1(X0)) )
          & ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
              & r2_hidden(X3,k3_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ? [X2] :
        ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(k4_tarski(X3,X1),X0)
            & r2_hidden(X3,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => ? [X2] :
        ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(k4_tarski(X3,X1),X0)
            & r2_hidden(X3,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s1_xboole_0__e7_18__wellord1)).

fof(f347,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k3_relat_1(sK2))
        | r2_hidden(sK3(sK2,X0),X0)
        | k1_xboole_0 = X0 )
    | ~ spl14_28 ),
    inference(avatar_component_clause,[],[f346])).

fof(f3064,plain,
    ( ! [X5] :
        ( ~ r2_hidden(sK3(sK2,sK12(sK2,X5)),sK12(sK2,sK1))
        | k1_xboole_0 = sK12(sK2,X5)
        | r2_hidden(k4_tarski(sK1,X5),sK2) )
    | ~ spl14_296 ),
    inference(avatar_component_clause,[],[f3063])).

fof(f4144,plain,
    ( sK0 != sK1
    | r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ r2_hidden(k4_tarski(sK1,sK1),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f4139,plain,
    ( ~ spl14_6
    | ~ spl14_395 ),
    inference(avatar_split_clause,[],[f4137,f3991,f140])).

fof(f3991,plain,
    ( spl14_395
  <=> r2_hidden(sK1,k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_395])])).

fof(f4137,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl14_395 ),
    inference(resolution,[],[f4133,f114])).

fof(f114,plain,(
    ! [X4,X0] :
      ( ~ r2_hidden(X4,k1_wellord1(X0,X4))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f113])).

fof(f113,plain,(
    ! [X4,X2,X0] :
      ( ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X4) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 != X4
      | ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ( ( ~ r2_hidden(k4_tarski(sK11(X0,X1,X2),X1),X0)
                | sK11(X0,X1,X2) = X1
                | ~ r2_hidden(sK11(X0,X1,X2),X2) )
              & ( ( r2_hidden(k4_tarski(sK11(X0,X1,X2),X1),X0)
                  & sK11(X0,X1,X2) != X1 )
                | r2_hidden(sK11(X0,X1,X2),X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f52,f53])).

fof(f53,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
            | X1 = X3
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k4_tarski(X3,X1),X0)
              & X1 != X3 )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK11(X0,X1,X2),X1),X0)
          | sK11(X0,X1,X2) = X1
          | ~ r2_hidden(sK11(X0,X1,X2),X2) )
        & ( ( r2_hidden(k4_tarski(sK11(X0,X1,X2),X1),X0)
            & sK11(X0,X1,X2) != X1 )
          | r2_hidden(sK11(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3 )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | ~ r2_hidden(X3,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3 )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | ~ r2_hidden(X3,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord1)).

fof(f4133,plain,
    ( r2_hidden(sK1,k1_wellord1(sK2,sK1))
    | ~ spl14_395 ),
    inference(avatar_component_clause,[],[f3991])).

fof(f4134,plain,
    ( spl14_395
    | ~ spl14_2
    | ~ spl14_219 ),
    inference(avatar_split_clause,[],[f4124,f2064,f121,f3991])).

fof(f121,plain,
    ( spl14_2
  <=> r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).

fof(f2064,plain,
    ( spl14_219
  <=> r2_hidden(sK1,k1_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_219])])).

fof(f4124,plain,
    ( r2_hidden(sK1,k1_wellord1(sK2,sK1))
    | ~ spl14_2
    | ~ spl14_219 ),
    inference(resolution,[],[f4119,f2065])).

fof(f2065,plain,
    ( r2_hidden(sK1,k1_wellord1(sK2,sK0))
    | ~ spl14_219 ),
    inference(avatar_component_clause,[],[f2064])).

fof(f4119,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_wellord1(sK2,sK0))
        | r2_hidden(X0,k1_wellord1(sK2,sK1)) )
    | ~ spl14_2 ),
    inference(resolution,[],[f125,f105])).

fof(f105,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f125,plain,
    ( r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ spl14_2 ),
    inference(avatar_component_clause,[],[f121])).

fof(f4111,plain,
    ( spl14_219
    | spl14_136
    | ~ spl14_6
    | ~ spl14_106 ),
    inference(avatar_split_clause,[],[f4106,f990,f140,f1176,f2064])).

fof(f1176,plain,
    ( spl14_136
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_136])])).

fof(f990,plain,
    ( spl14_106
  <=> r2_hidden(k4_tarski(sK1,sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_106])])).

fof(f4106,plain,
    ( sK0 = sK1
    | r2_hidden(sK1,k1_wellord1(sK2,sK0))
    | ~ spl14_6
    | ~ spl14_106 ),
    inference(resolution,[],[f991,f292])).

fof(f292,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | X0 = X1
        | r2_hidden(X0,k1_wellord1(sK2,X1)) )
    | ~ spl14_6 ),
    inference(resolution,[],[f111,f141])).

fof(f111,plain,(
    ! [X4,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | r2_hidden(X4,k1_wellord1(X0,X1)) ) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f991,plain,
    ( r2_hidden(k4_tarski(sK1,sK0),sK2)
    | ~ spl14_106 ),
    inference(avatar_component_clause,[],[f990])).

fof(f3998,plain,
    ( spl14_1
    | ~ spl14_4
    | ~ spl14_6
    | spl14_21 ),
    inference(avatar_split_clause,[],[f1195,f256,f140,f132,f118])).

fof(f118,plain,
    ( spl14_1
  <=> r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).

fof(f132,plain,
    ( spl14_4
  <=> r2_hidden(sK0,k3_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_4])])).

fof(f256,plain,
    ( spl14_21
  <=> r2_hidden(sK0,sK12(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_21])])).

fof(f1195,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl14_4
    | ~ spl14_6
    | spl14_21 ),
    inference(resolution,[],[f257,f436])).

fof(f436,plain,
    ( ! [X0] :
        ( r2_hidden(sK0,sK12(sK2,X0))
        | r2_hidden(k4_tarski(sK0,X0),sK2) )
    | ~ spl14_4
    | ~ spl14_6 ),
    inference(resolution,[],[f434,f133])).

fof(f133,plain,
    ( r2_hidden(sK0,k3_relat_1(sK2))
    | ~ spl14_4 ),
    inference(avatar_component_clause,[],[f132])).

fof(f434,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k3_relat_1(sK2))
        | r2_hidden(k4_tarski(X0,X1),sK2)
        | r2_hidden(X0,sK12(sK2,X1)) )
    | ~ spl14_6 ),
    inference(resolution,[],[f101,f141])).

fof(f101,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X3,X1),X0)
      | ~ r2_hidden(X3,k3_relat_1(X0))
      | r2_hidden(X3,sK12(X0,X1)) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f257,plain,
    ( ~ r2_hidden(sK0,sK12(sK2,sK1))
    | spl14_21 ),
    inference(avatar_component_clause,[],[f256])).

fof(f3996,plain,
    ( spl14_136
    | spl14_106
    | spl14_1
    | ~ spl14_3
    | ~ spl14_4
    | ~ spl14_84 ),
    inference(avatar_split_clause,[],[f1523,f869,f132,f128,f118,f990,f1176])).

fof(f128,plain,
    ( spl14_3
  <=> r2_hidden(sK1,k3_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_3])])).

fof(f869,plain,
    ( spl14_84
  <=> ! [X1,X0] :
        ( r2_hidden(k4_tarski(X0,X1),sK2)
        | r2_hidden(k4_tarski(X1,X0),sK2)
        | ~ r2_hidden(X0,k3_relat_1(sK2))
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | X0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_84])])).

fof(f1523,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | r2_hidden(k4_tarski(sK1,sK0),sK2)
    | sK0 = sK1
    | ~ spl14_3
    | ~ spl14_4
    | ~ spl14_84 ),
    inference(resolution,[],[f1141,f129])).

fof(f129,plain,
    ( r2_hidden(sK1,k3_relat_1(sK2))
    | ~ spl14_3 ),
    inference(avatar_component_clause,[],[f128])).

fof(f1141,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k3_relat_1(sK2))
        | r2_hidden(k4_tarski(sK0,X0),sK2)
        | r2_hidden(k4_tarski(X0,sK0),sK2)
        | sK0 = X0 )
    | ~ spl14_4
    | ~ spl14_84 ),
    inference(resolution,[],[f870,f133])).

fof(f870,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k3_relat_1(sK2))
        | r2_hidden(k4_tarski(X1,X0),sK2)
        | r2_hidden(k4_tarski(X0,X1),sK2)
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | X0 = X1 )
    | ~ spl14_84 ),
    inference(avatar_component_clause,[],[f869])).

fof(f3984,plain,
    ( spl14_2
    | spl14_136
    | ~ spl14_1
    | ~ spl14_6
    | ~ spl14_45
    | ~ spl14_391 ),
    inference(avatar_split_clause,[],[f3970,f3954,f500,f140,f118,f1176,f121])).

fof(f500,plain,
    ( spl14_45
  <=> ! [X1,X0] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | X0 = X1
        | ~ r2_hidden(k4_tarski(X1,X0),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_45])])).

fof(f3954,plain,
    ( spl14_391
  <=> sK1 = sK13(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_391])])).

fof(f3970,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),sK2)
    | sK0 = sK1
    | r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ spl14_6
    | ~ spl14_45
    | ~ spl14_391 ),
    inference(superposition,[],[f556,f3955])).

fof(f3955,plain,
    ( sK1 = sK13(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ spl14_391 ),
    inference(avatar_component_clause,[],[f3954])).

fof(f556,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,sK13(k1_wellord1(sK2,X0),X1)),sK2)
        | sK13(k1_wellord1(sK2,X0),X1) = X0
        | r1_tarski(k1_wellord1(sK2,X0),X1) )
    | ~ spl14_6
    | ~ spl14_45 ),
    inference(resolution,[],[f501,f181])).

fof(f181,plain,
    ( ! [X2,X1] :
        ( r2_hidden(k4_tarski(sK13(k1_wellord1(sK2,X1),X2),X1),sK2)
        | r1_tarski(k1_wellord1(sK2,X1),X2) )
    | ~ spl14_6 ),
    inference(resolution,[],[f179,f106])).

fof(f179,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_wellord1(sK2,X1))
        | r2_hidden(k4_tarski(X0,X1),sK2) )
    | ~ spl14_6 ),
    inference(resolution,[],[f112,f141])).

fof(f112,plain,(
    ! [X4,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X4,k1_wellord1(X0,X1))
      | r2_hidden(k4_tarski(X4,X1),X0) ) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k4_tarski(X4,X1),X0)
      | ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f501,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | X0 = X1
        | ~ r2_hidden(k4_tarski(X1,X0),sK2) )
    | ~ spl14_45 ),
    inference(avatar_component_clause,[],[f500])).

fof(f3956,plain,
    ( spl14_2
    | spl14_391
    | ~ spl14_1
    | ~ spl14_6
    | ~ spl14_51 ),
    inference(avatar_split_clause,[],[f3952,f577,f140,f118,f3954,f121])).

fof(f577,plain,
    ( spl14_51
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | r2_hidden(k4_tarski(X2,X1),sK2)
        | ~ r2_hidden(k4_tarski(X2,X0),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_51])])).

fof(f3952,plain,
    ( sK1 = sK13(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ spl14_1
    | ~ spl14_6
    | ~ spl14_51 ),
    inference(duplicate_literal_removal,[],[f3948])).

fof(f3948,plain,
    ( sK1 = sK13(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ spl14_1
    | ~ spl14_6
    | ~ spl14_51 ),
    inference(resolution,[],[f1685,f107])).

fof(f1685,plain,
    ( ! [X3] :
        ( r2_hidden(sK13(k1_wellord1(sK2,sK0),X3),k1_wellord1(sK2,sK1))
        | sK1 = sK13(k1_wellord1(sK2,sK0),X3)
        | r1_tarski(k1_wellord1(sK2,sK0),X3) )
    | ~ spl14_1
    | ~ spl14_6
    | ~ spl14_51 ),
    inference(resolution,[],[f1404,f292])).

fof(f1404,plain,
    ( ! [X1] :
        ( r2_hidden(k4_tarski(sK13(k1_wellord1(sK2,sK0),X1),sK1),sK2)
        | r1_tarski(k1_wellord1(sK2,sK0),X1) )
    | ~ spl14_1
    | ~ spl14_6
    | ~ spl14_51 ),
    inference(resolution,[],[f1187,f181])).

fof(f1187,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK0),sK2)
        | r2_hidden(k4_tarski(X0,sK1),sK2) )
    | ~ spl14_1
    | ~ spl14_51 ),
    inference(resolution,[],[f124,f578])).

fof(f578,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | r2_hidden(k4_tarski(X2,X1),sK2)
        | ~ r2_hidden(k4_tarski(X2,X0),sK2) )
    | ~ spl14_51 ),
    inference(avatar_component_clause,[],[f577])).

fof(f124,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl14_1 ),
    inference(avatar_component_clause,[],[f118])).

fof(f3065,plain,
    ( ~ spl14_6
    | spl14_296
    | ~ spl14_3
    | ~ spl14_6
    | ~ spl14_64 ),
    inference(avatar_split_clause,[],[f3055,f685,f140,f128,f3063,f140])).

fof(f685,plain,
    ( spl14_64
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | r2_hidden(k4_tarski(sK3(sK2,X1),X0),sK2)
        | ~ r1_tarski(X1,k3_relat_1(sK2))
        | k1_xboole_0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_64])])).

fof(f3055,plain,
    ( ! [X5] :
        ( k1_xboole_0 = sK12(sK2,X5)
        | r2_hidden(k4_tarski(sK1,X5),sK2)
        | ~ r2_hidden(sK3(sK2,sK12(sK2,X5)),sK12(sK2,sK1))
        | ~ v1_relat_1(sK2) )
    | ~ spl14_3
    | ~ spl14_6
    | ~ spl14_64 ),
    inference(resolution,[],[f2758,f100])).

fof(f100,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X1),X0)
      | ~ r2_hidden(X3,sK12(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f2758,plain,
    ( ! [X3] :
        ( r2_hidden(k4_tarski(sK3(sK2,sK12(sK2,X3)),sK1),sK2)
        | k1_xboole_0 = sK12(sK2,X3)
        | r2_hidden(k4_tarski(sK1,X3),sK2) )
    | ~ spl14_3
    | ~ spl14_6
    | ~ spl14_64 ),
    inference(resolution,[],[f806,f437])).

fof(f437,plain,
    ( ! [X1] :
        ( r2_hidden(sK1,sK12(sK2,X1))
        | r2_hidden(k4_tarski(sK1,X1),sK2) )
    | ~ spl14_3
    | ~ spl14_6 ),
    inference(resolution,[],[f434,f129])).

fof(f806,plain,
    ( ! [X6,X7] :
        ( ~ r2_hidden(X7,sK12(sK2,X6))
        | r2_hidden(k4_tarski(sK3(sK2,sK12(sK2,X6)),X7),sK2)
        | k1_xboole_0 = sK12(sK2,X6) )
    | ~ spl14_6
    | ~ spl14_64 ),
    inference(resolution,[],[f686,f176])).

fof(f686,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,k3_relat_1(sK2))
        | r2_hidden(k4_tarski(sK3(sK2,X1),X0),sK2)
        | ~ r2_hidden(X0,X1)
        | k1_xboole_0 = X1 )
    | ~ spl14_64 ),
    inference(avatar_component_clause,[],[f685])).

fof(f1362,plain,(
    spl14_141 ),
    inference(avatar_contradiction_clause,[],[f1361])).

fof(f1361,plain,
    ( $false
    | spl14_141 ),
    inference(resolution,[],[f1358,f115])).

fof(f115,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1358,plain,
    ( ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0))
    | spl14_141 ),
    inference(avatar_component_clause,[],[f1357])).

fof(f1357,plain,
    ( spl14_141
  <=> r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_141])])).

fof(f1359,plain,
    ( ~ spl14_141
    | spl14_2
    | ~ spl14_136 ),
    inference(avatar_split_clause,[],[f1336,f1176,f121,f1357])).

fof(f1336,plain,
    ( ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0))
    | spl14_2
    | ~ spl14_136 ),
    inference(superposition,[],[f122,f1177])).

fof(f1177,plain,
    ( sK0 = sK1
    | ~ spl14_136 ),
    inference(avatar_component_clause,[],[f1176])).

fof(f122,plain,
    ( ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | spl14_2 ),
    inference(avatar_component_clause,[],[f121])).

fof(f893,plain,
    ( ~ spl14_6
    | ~ spl14_5
    | spl14_83 ),
    inference(avatar_split_clause,[],[f876,f866,f136,f140])).

fof(f136,plain,
    ( spl14_5
  <=> v2_wellord1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_5])])).

fof(f866,plain,
    ( spl14_83
  <=> v6_relat_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_83])])).

fof(f876,plain,
    ( ~ v2_wellord1(sK2)
    | ~ v1_relat_1(sK2)
    | spl14_83 ),
    inference(resolution,[],[f867,f90])).

fof(f90,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ v1_wellord1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v1_wellord1(X0)
            & v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v2_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ v1_wellord1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v1_wellord1(X0)
            & v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v2_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_wellord1)).

fof(f867,plain,
    ( ~ v6_relat_2(sK2)
    | spl14_83 ),
    inference(avatar_component_clause,[],[f866])).

fof(f871,plain,
    ( ~ spl14_83
    | spl14_84
    | ~ spl14_6 ),
    inference(avatar_split_clause,[],[f864,f140,f869,f866])).

fof(f864,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,X1),sK2)
        | X0 = X1
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | ~ r2_hidden(X0,k3_relat_1(sK2))
        | ~ v6_relat_2(sK2)
        | r2_hidden(k4_tarski(X1,X0),sK2) )
    | ~ spl14_6 ),
    inference(resolution,[],[f77,f141])).

fof(f77,plain,(
    ! [X4,X0,X3] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X3,X4),X0)
      | X3 = X4
      | ~ r2_hidden(X4,k3_relat_1(X0))
      | ~ r2_hidden(X3,k3_relat_1(X0))
      | ~ v6_relat_2(X0)
      | r2_hidden(k4_tarski(X4,X3),X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ( ~ r2_hidden(k4_tarski(sK7(X0),sK6(X0)),X0)
            & ~ r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0)
            & sK6(X0) != sK7(X0)
            & r2_hidden(sK7(X0),k3_relat_1(X0))
            & r2_hidden(sK6(X0),k3_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( r2_hidden(k4_tarski(X4,X3),X0)
              | r2_hidden(k4_tarski(X3,X4),X0)
              | X3 = X4
              | ~ r2_hidden(X4,k3_relat_1(X0))
              | ~ r2_hidden(X3,k3_relat_1(X0)) )
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f41,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ~ r2_hidden(k4_tarski(X2,X1),X0)
          & ~ r2_hidden(k4_tarski(X1,X2),X0)
          & X1 != X2
          & r2_hidden(X2,k3_relat_1(X0))
          & r2_hidden(X1,k3_relat_1(X0)) )
     => ( ~ r2_hidden(k4_tarski(sK7(X0),sK6(X0)),X0)
        & ~ r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0)
        & sK6(X0) != sK7(X0)
        & r2_hidden(sK7(X0),k3_relat_1(X0))
        & r2_hidden(sK6(X0),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ? [X1,X2] :
              ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( r2_hidden(k4_tarski(X4,X3),X0)
              | r2_hidden(k4_tarski(X3,X4),X0)
              | X3 = X4
              | ~ r2_hidden(X4,k3_relat_1(X0))
              | ~ r2_hidden(X3,k3_relat_1(X0)) )
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ? [X1,X2] :
              ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) )
        & ( ! [X1,X2] :
              ( r2_hidden(k4_tarski(X2,X1),X0)
              | r2_hidden(k4_tarski(X1,X2),X0)
              | X1 = X2
              | ~ r2_hidden(X2,k3_relat_1(X0))
              | ~ r2_hidden(X1,k3_relat_1(X0)) )
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ( r2_hidden(k4_tarski(X2,X1),X0)
            | r2_hidden(k4_tarski(X1,X2),X0)
            | X1 = X2
            | ~ r2_hidden(X2,k3_relat_1(X0))
            | ~ r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ~ ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l4_wellord1)).

fof(f861,plain,
    ( ~ spl14_12
    | ~ spl14_29
    | spl14_37 ),
    inference(avatar_contradiction_clause,[],[f860])).

fof(f860,plain,
    ( $false
    | ~ spl14_12
    | ~ spl14_29
    | spl14_37 ),
    inference(resolution,[],[f393,f399])).

fof(f399,plain,
    ( ! [X4] : r1_tarski(k1_xboole_0,X4)
    | ~ spl14_12
    | ~ spl14_29 ),
    inference(superposition,[],[f219,f355])).

fof(f355,plain,
    ( k1_xboole_0 = k1_wellord1(sK2,k2_relat_1(sK2))
    | ~ spl14_29 ),
    inference(avatar_component_clause,[],[f354])).

fof(f354,plain,
    ( spl14_29
  <=> k1_xboole_0 = k1_wellord1(sK2,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_29])])).

fof(f219,plain,
    ( ! [X0] : r1_tarski(k1_wellord1(sK2,k2_relat_1(sK2)),X0)
    | ~ spl14_12 ),
    inference(resolution,[],[f202,f115])).

fof(f202,plain,
    ( ! [X10,X9] :
        ( ~ r1_tarski(k2_relat_1(sK2),X9)
        | r1_tarski(k1_wellord1(sK2,X9),X10) )
    | ~ spl14_12 ),
    inference(resolution,[],[f193,f108])).

fof(f193,plain,
    ( ! [X2,X3] :
        ( r2_hidden(X2,k2_relat_1(sK2))
        | r1_tarski(k1_wellord1(sK2,X2),X3) )
    | ~ spl14_12 ),
    inference(avatar_component_clause,[],[f192])).

fof(f192,plain,
    ( spl14_12
  <=> ! [X3,X2] :
        ( r1_tarski(k1_wellord1(sK2,X2),X3)
        | r2_hidden(X2,k2_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_12])])).

fof(f393,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | spl14_37 ),
    inference(avatar_component_clause,[],[f392])).

fof(f771,plain,
    ( ~ spl14_12
    | spl14_59 ),
    inference(avatar_contradiction_clause,[],[f769])).

fof(f769,plain,
    ( $false
    | ~ spl14_12
    | spl14_59 ),
    inference(resolution,[],[f642,f219])).

fof(f642,plain,
    ( ~ r1_tarski(k1_wellord1(sK2,k2_relat_1(sK2)),sK3(sK2,k1_wellord1(sK2,k2_relat_1(sK2))))
    | spl14_59 ),
    inference(avatar_component_clause,[],[f641])).

fof(f641,plain,
    ( spl14_59
  <=> r1_tarski(k1_wellord1(sK2,k2_relat_1(sK2)),sK3(sK2,k1_wellord1(sK2,k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_59])])).

fof(f687,plain,
    ( ~ spl14_5
    | spl14_64
    | ~ spl14_6 ),
    inference(avatar_split_clause,[],[f683,f140,f685,f136])).

fof(f683,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | k1_xboole_0 = X1
        | ~ r1_tarski(X1,k3_relat_1(sK2))
        | ~ v2_wellord1(sK2)
        | r2_hidden(k4_tarski(sK3(sK2,X1),X0),sK2) )
    | ~ spl14_6 ),
    inference(resolution,[],[f72,f141])).

fof(f72,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X3,X1)
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,k3_relat_1(X0))
      | ~ v2_wellord1(X0)
      | r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ! [X3] :
                ( r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
                | ~ r2_hidden(X3,X1) )
            & r2_hidden(sK3(X0,X1),X1) )
          | k1_xboole_0 = X1
          | ~ r1_tarski(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK3(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( r2_hidden(k4_tarski(X2,X3),X0)
                  | ~ r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
          | k1_xboole_0 = X1
          | ~ r1_tarski(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( r2_hidden(k4_tarski(X2,X3),X0)
                  | ~ r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
          | k1_xboole_0 = X1
          | ~ r1_tarski(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( ! [X2] :
                  ~ ( ! [X3] :
                        ( r2_hidden(X3,X1)
                       => r2_hidden(k4_tarski(X2,X3),X0) )
                    & r2_hidden(X2,X1) )
              & k1_xboole_0 != X1
              & r1_tarski(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_wellord1)).

fof(f643,plain,
    ( ~ spl14_59
    | ~ spl14_30 ),
    inference(avatar_split_clause,[],[f631,f357,f641])).

fof(f357,plain,
    ( spl14_30
  <=> r2_hidden(sK3(sK2,k1_wellord1(sK2,k2_relat_1(sK2))),k1_wellord1(sK2,k2_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_30])])).

fof(f631,plain,
    ( ~ r1_tarski(k1_wellord1(sK2,k2_relat_1(sK2)),sK3(sK2,k1_wellord1(sK2,k2_relat_1(sK2))))
    | ~ spl14_30 ),
    inference(resolution,[],[f358,f108])).

fof(f358,plain,
    ( r2_hidden(sK3(sK2,k1_wellord1(sK2,k2_relat_1(sK2))),k1_wellord1(sK2,k2_relat_1(sK2)))
    | ~ spl14_30 ),
    inference(avatar_component_clause,[],[f357])).

fof(f596,plain,
    ( ~ spl14_6
    | ~ spl14_5
    | spl14_50 ),
    inference(avatar_split_clause,[],[f583,f574,f136,f140])).

fof(f574,plain,
    ( spl14_50
  <=> v8_relat_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_50])])).

fof(f583,plain,
    ( ~ v2_wellord1(sK2)
    | ~ v1_relat_1(sK2)
    | spl14_50 ),
    inference(resolution,[],[f575,f88])).

fof(f88,plain,(
    ! [X0] :
      ( v8_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f575,plain,
    ( ~ v8_relat_2(sK2)
    | spl14_50 ),
    inference(avatar_component_clause,[],[f574])).

fof(f579,plain,
    ( ~ spl14_50
    | spl14_51
    | ~ spl14_6 ),
    inference(avatar_split_clause,[],[f572,f140,f577,f574])).

fof(f572,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | ~ r2_hidden(k4_tarski(X2,X0),sK2)
        | ~ v8_relat_2(sK2)
        | r2_hidden(k4_tarski(X2,X1),sK2) )
    | ~ spl14_6 ),
    inference(resolution,[],[f83,f141])).

fof(f83,plain,(
    ! [X6,X4,X0,X5] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X4,X5),X0)
      | ~ v8_relat_2(X0)
      | r2_hidden(k4_tarski(X4,X6),X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( ( v8_relat_2(X0)
          | ( ~ r2_hidden(k4_tarski(sK8(X0),sK10(X0)),X0)
            & r2_hidden(k4_tarski(sK9(X0),sK10(X0)),X0)
            & r2_hidden(k4_tarski(sK8(X0),sK9(X0)),X0) ) )
        & ( ! [X4,X5,X6] :
              ( r2_hidden(k4_tarski(X4,X6),X0)
              | ~ r2_hidden(k4_tarski(X5,X6),X0)
              | ~ r2_hidden(k4_tarski(X4,X5),X0) )
          | ~ v8_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f45,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1,X2,X3] :
          ( ~ r2_hidden(k4_tarski(X1,X3),X0)
          & r2_hidden(k4_tarski(X2,X3),X0)
          & r2_hidden(k4_tarski(X1,X2),X0) )
     => ( ~ r2_hidden(k4_tarski(sK8(X0),sK10(X0)),X0)
        & r2_hidden(k4_tarski(sK9(X0),sK10(X0)),X0)
        & r2_hidden(k4_tarski(sK8(X0),sK9(X0)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ( ( v8_relat_2(X0)
          | ? [X1,X2,X3] :
              ( ~ r2_hidden(k4_tarski(X1,X3),X0)
              & r2_hidden(k4_tarski(X2,X3),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) ) )
        & ( ! [X4,X5,X6] :
              ( r2_hidden(k4_tarski(X4,X6),X0)
              | ~ r2_hidden(k4_tarski(X5,X6),X0)
              | ~ r2_hidden(k4_tarski(X4,X5),X0) )
          | ~ v8_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( ( v8_relat_2(X0)
          | ? [X1,X2,X3] :
              ( ~ r2_hidden(k4_tarski(X1,X3),X0)
              & r2_hidden(k4_tarski(X2,X3),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) ) )
        & ( ! [X1,X2,X3] :
              ( r2_hidden(k4_tarski(X1,X3),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(k4_tarski(X1,X2),X0) )
          | ~ v8_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v8_relat_2(X0)
      <=> ! [X1,X2,X3] :
            ( r2_hidden(k4_tarski(X1,X3),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v8_relat_2(X0)
      <=> ! [X1,X2,X3] :
            ( r2_hidden(k4_tarski(X1,X3),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v8_relat_2(X0)
      <=> ! [X1,X2,X3] :
            ( ( r2_hidden(k4_tarski(X2,X3),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) )
           => r2_hidden(k4_tarski(X1,X3),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l2_wellord1)).

fof(f514,plain,
    ( ~ spl14_6
    | ~ spl14_5
    | spl14_44 ),
    inference(avatar_split_clause,[],[f505,f497,f136,f140])).

fof(f497,plain,
    ( spl14_44
  <=> v4_relat_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_44])])).

fof(f505,plain,
    ( ~ v2_wellord1(sK2)
    | ~ v1_relat_1(sK2)
    | spl14_44 ),
    inference(resolution,[],[f498,f89])).

fof(f89,plain,(
    ! [X0] :
      ( v4_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f498,plain,
    ( ~ v4_relat_2(sK2)
    | spl14_44 ),
    inference(avatar_component_clause,[],[f497])).

fof(f502,plain,
    ( ~ spl14_44
    | spl14_45
    | ~ spl14_6 ),
    inference(avatar_split_clause,[],[f495,f140,f500,f497])).

fof(f495,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | ~ r2_hidden(k4_tarski(X1,X0),sK2)
        | ~ v4_relat_2(sK2)
        | X0 = X1 )
    | ~ spl14_6 ),
    inference(resolution,[],[f73,f141])).

fof(f73,plain,(
    ! [X4,X0,X3] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X4,X3),X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ v4_relat_2(X0)
      | X3 = X4 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( ( v4_relat_2(X0)
          | ( sK4(X0) != sK5(X0)
            & r2_hidden(k4_tarski(sK5(X0),sK4(X0)),X0)
            & r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | ~ r2_hidden(k4_tarski(X4,X3),X0)
              | ~ r2_hidden(k4_tarski(X3,X4),X0) )
          | ~ v4_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f37,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & r2_hidden(k4_tarski(X2,X1),X0)
          & r2_hidden(k4_tarski(X1,X2),X0) )
     => ( sK4(X0) != sK5(X0)
        & r2_hidden(k4_tarski(sK5(X0),sK4(X0)),X0)
        & r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ( ( v4_relat_2(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & r2_hidden(k4_tarski(X2,X1),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | ~ r2_hidden(k4_tarski(X4,X3),X0)
              | ~ r2_hidden(k4_tarski(X3,X4),X0) )
          | ~ v4_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( ( v4_relat_2(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & r2_hidden(k4_tarski(X2,X1),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) ) )
        & ( ! [X1,X2] :
              ( X1 = X2
              | ~ r2_hidden(k4_tarski(X2,X1),X0)
              | ~ r2_hidden(k4_tarski(X1,X2),X0) )
          | ~ v4_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v4_relat_2(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | ~ r2_hidden(k4_tarski(X2,X1),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v4_relat_2(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | ~ r2_hidden(k4_tarski(X2,X1),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v4_relat_2(X0)
      <=> ! [X1,X2] :
            ( ( r2_hidden(k4_tarski(X2,X1),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_wellord1)).

fof(f359,plain,
    ( spl14_29
    | spl14_30
    | ~ spl14_12
    | ~ spl14_28 ),
    inference(avatar_split_clause,[],[f349,f346,f192,f357,f354])).

fof(f349,plain,
    ( r2_hidden(sK3(sK2,k1_wellord1(sK2,k2_relat_1(sK2))),k1_wellord1(sK2,k2_relat_1(sK2)))
    | k1_xboole_0 = k1_wellord1(sK2,k2_relat_1(sK2))
    | ~ spl14_12
    | ~ spl14_28 ),
    inference(resolution,[],[f347,f219])).

fof(f348,plain,
    ( ~ spl14_5
    | spl14_28
    | ~ spl14_6 ),
    inference(avatar_split_clause,[],[f343,f140,f346,f136])).

fof(f343,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ r1_tarski(X0,k3_relat_1(sK2))
        | ~ v2_wellord1(sK2)
        | r2_hidden(sK3(sK2,X0),X0) )
    | ~ spl14_6 ),
    inference(resolution,[],[f71,f141])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,k3_relat_1(X0))
      | ~ v2_wellord1(X0)
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f258,plain,
    ( ~ spl14_6
    | ~ spl14_21
    | ~ spl14_1 ),
    inference(avatar_split_clause,[],[f251,f118,f256,f140])).

fof(f251,plain,
    ( ~ r2_hidden(sK0,sK12(sK2,sK1))
    | ~ v1_relat_1(sK2)
    | ~ spl14_1 ),
    inference(resolution,[],[f124,f100])).

fof(f194,plain,
    ( ~ spl14_6
    | spl14_12
    | ~ spl14_6 ),
    inference(avatar_split_clause,[],[f183,f140,f192,f140])).

fof(f183,plain,
    ( ! [X2,X3] :
        ( r1_tarski(k1_wellord1(sK2,X2),X3)
        | r2_hidden(X2,k2_relat_1(sK2))
        | ~ v1_relat_1(sK2) )
    | ~ spl14_6 ),
    inference(resolution,[],[f181,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

fof(f142,plain,(
    spl14_6 ),
    inference(avatar_split_clause,[],[f65,f140])).

fof(f65,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ( ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
      | ~ r2_hidden(k4_tarski(sK0,sK1),sK2) )
    & ( r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
      | r2_hidden(k4_tarski(sK0,sK1),sK2) )
    & r2_hidden(sK1,k3_relat_1(sK2))
    & r2_hidden(sK0,k3_relat_1(sK2))
    & v2_wellord1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f32])).

fof(f32,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) )
        & ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
          | r2_hidden(k4_tarski(X0,X1),X2) )
        & r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2))
        & v2_wellord1(X2)
        & v1_relat_1(X2) )
   => ( ( ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
        | ~ r2_hidden(k4_tarski(sK0,sK1),sK2) )
      & ( r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
        | r2_hidden(k4_tarski(sK0,sK1),sK2) )
      & r2_hidden(sK1,k3_relat_1(sK2))
      & r2_hidden(sK0,k3_relat_1(sK2))
      & v2_wellord1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
        | ~ r2_hidden(k4_tarski(X0,X1),X2) )
      & ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
        | r2_hidden(k4_tarski(X0,X1),X2) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
        | ~ r2_hidden(k4_tarski(X0,X1),X2) )
      & ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
        | r2_hidden(k4_tarski(X0,X1),X2) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( ( r2_hidden(X1,k3_relat_1(X2))
            & r2_hidden(X0,k3_relat_1(X2))
            & v2_wellord1(X2) )
         => ( r2_hidden(k4_tarski(X0,X1),X2)
          <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2))
          & v2_wellord1(X2) )
       => ( r2_hidden(k4_tarski(X0,X1),X2)
        <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_wellord1)).

fof(f138,plain,(
    spl14_5 ),
    inference(avatar_split_clause,[],[f66,f136])).

fof(f66,plain,(
    v2_wellord1(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f134,plain,(
    spl14_4 ),
    inference(avatar_split_clause,[],[f67,f132])).

fof(f67,plain,(
    r2_hidden(sK0,k3_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f33])).

fof(f130,plain,(
    spl14_3 ),
    inference(avatar_split_clause,[],[f68,f128])).

fof(f68,plain,(
    r2_hidden(sK1,k3_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f33])).

fof(f126,plain,
    ( spl14_1
    | spl14_2 ),
    inference(avatar_split_clause,[],[f69,f121,f118])).

fof(f69,plain,
    ( r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f123,plain,
    ( ~ spl14_1
    | ~ spl14_2 ),
    inference(avatar_split_clause,[],[f70,f121,f118])).

fof(f70,plain,
    ( ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:45:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.50  % (29995)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.51  % (30022)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.52  % (30004)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (30002)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.52  % (29997)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.31/0.52  % (30014)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.31/0.52  % (30006)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.31/0.52  % (30003)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.31/0.52  % (29993)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.31/0.52  % (29998)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.31/0.53  % (30021)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.31/0.53  % (29991)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.31/0.53  % (29992)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.31/0.53  % (30015)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.31/0.53  % (30011)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.31/0.53  % (29996)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.31/0.54  % (30019)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.31/0.54  % (30020)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.31/0.54  % (30018)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.31/0.54  % (30017)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.39/0.54  % (30010)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.39/0.54  % (30009)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.39/0.54  % (30007)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.39/0.54  % (30008)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.39/0.54  % (30009)Refutation not found, incomplete strategy% (30009)------------------------------
% 1.39/0.54  % (30009)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.54  % (30009)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.54  
% 1.39/0.54  % (30009)Memory used [KB]: 10746
% 1.39/0.54  % (30009)Time elapsed: 0.140 s
% 1.39/0.54  % (30009)------------------------------
% 1.39/0.54  % (30009)------------------------------
% 1.39/0.55  % (29999)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.39/0.55  % (30012)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.39/0.55  % (30000)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.39/0.55  % (30001)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.39/0.55  % (30005)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.39/0.56  % (30016)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 2.00/0.68  % (30043)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 3.46/0.82  % (29997)Time limit reached!
% 3.46/0.82  % (29997)------------------------------
% 3.46/0.82  % (29997)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.46/0.82  % (29997)Termination reason: Time limit
% 3.46/0.82  
% 3.46/0.82  % (29997)Memory used [KB]: 8059
% 3.46/0.82  % (29997)Time elapsed: 0.417 s
% 3.46/0.82  % (29997)------------------------------
% 3.46/0.82  % (29997)------------------------------
% 3.70/0.84  % (30011)Refutation found. Thanks to Tanya!
% 3.70/0.84  % SZS status Theorem for theBenchmark
% 3.70/0.84  % SZS output start Proof for theBenchmark
% 3.70/0.84  fof(f4362,plain,(
% 3.70/0.84    $false),
% 3.70/0.84    inference(avatar_sat_refutation,[],[f123,f126,f130,f134,f138,f142,f194,f258,f348,f359,f502,f514,f579,f596,f643,f687,f771,f861,f871,f893,f1359,f1362,f3065,f3956,f3984,f3996,f3998,f4111,f4134,f4139,f4144,f4160,f4237,f4285])).
% 3.70/0.84  fof(f4285,plain,(
% 3.70/0.84    ~spl14_37 | ~spl14_35),
% 3.70/0.84    inference(avatar_split_clause,[],[f848,f384,f392])).
% 3.70/0.84  fof(f392,plain,(
% 3.70/0.84    spl14_37 <=> r1_tarski(k1_xboole_0,sK0)),
% 3.70/0.84    introduced(avatar_definition,[new_symbols(naming,[spl14_37])])).
% 3.70/0.84  fof(f384,plain,(
% 3.70/0.84    spl14_35 <=> r2_hidden(sK0,k1_xboole_0)),
% 3.70/0.84    introduced(avatar_definition,[new_symbols(naming,[spl14_35])])).
% 3.70/0.84  fof(f848,plain,(
% 3.70/0.84    ~r1_tarski(k1_xboole_0,sK0) | ~spl14_35),
% 3.70/0.84    inference(resolution,[],[f385,f108])).
% 3.70/0.84  fof(f108,plain,(
% 3.70/0.84    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 3.70/0.84    inference(cnf_transformation,[],[f27])).
% 3.70/0.84  fof(f27,plain,(
% 3.70/0.84    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.70/0.84    inference(ennf_transformation,[],[f4])).
% 3.70/0.84  fof(f4,axiom,(
% 3.70/0.84    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.70/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 3.70/0.84  fof(f385,plain,(
% 3.70/0.84    r2_hidden(sK0,k1_xboole_0) | ~spl14_35),
% 3.70/0.84    inference(avatar_component_clause,[],[f384])).
% 3.70/0.84  fof(f4237,plain,(
% 3.70/0.84    k1_xboole_0 != sK12(sK2,sK1) | sK0 != sK1 | ~r2_hidden(sK0,sK12(sK2,sK1)) | r2_hidden(sK0,k1_xboole_0)),
% 3.70/0.84    introduced(theory_tautology_sat_conflict,[])).
% 3.70/0.84  fof(f4160,plain,(
% 3.70/0.84    spl14_107 | spl14_421 | ~spl14_6 | ~spl14_28 | ~spl14_296),
% 3.70/0.84    inference(avatar_split_clause,[],[f3070,f3063,f346,f140,f4158,f994])).
% 3.70/0.84  fof(f994,plain,(
% 3.70/0.84    spl14_107 <=> r2_hidden(k4_tarski(sK1,sK1),sK2)),
% 3.70/0.84    introduced(avatar_definition,[new_symbols(naming,[spl14_107])])).
% 3.70/0.84  fof(f4158,plain,(
% 3.70/0.84    spl14_421 <=> k1_xboole_0 = sK12(sK2,sK1)),
% 3.70/0.84    introduced(avatar_definition,[new_symbols(naming,[spl14_421])])).
% 3.70/0.84  fof(f140,plain,(
% 3.70/0.84    spl14_6 <=> v1_relat_1(sK2)),
% 3.70/0.84    introduced(avatar_definition,[new_symbols(naming,[spl14_6])])).
% 3.70/0.84  fof(f346,plain,(
% 3.70/0.84    spl14_28 <=> ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK3(sK2,X0),X0) | ~r1_tarski(X0,k3_relat_1(sK2)))),
% 3.70/0.84    introduced(avatar_definition,[new_symbols(naming,[spl14_28])])).
% 3.70/0.84  fof(f3063,plain,(
% 3.70/0.84    spl14_296 <=> ! [X5] : (k1_xboole_0 = sK12(sK2,X5) | ~r2_hidden(sK3(sK2,sK12(sK2,X5)),sK12(sK2,sK1)) | r2_hidden(k4_tarski(sK1,X5),sK2))),
% 3.70/0.84    introduced(avatar_definition,[new_symbols(naming,[spl14_296])])).
% 3.70/0.84  fof(f3070,plain,(
% 3.70/0.84    k1_xboole_0 = sK12(sK2,sK1) | r2_hidden(k4_tarski(sK1,sK1),sK2) | (~spl14_6 | ~spl14_28 | ~spl14_296)),
% 3.70/0.84    inference(duplicate_literal_removal,[],[f3066])).
% 3.70/0.84  fof(f3066,plain,(
% 3.70/0.84    k1_xboole_0 = sK12(sK2,sK1) | r2_hidden(k4_tarski(sK1,sK1),sK2) | k1_xboole_0 = sK12(sK2,sK1) | (~spl14_6 | ~spl14_28 | ~spl14_296)),
% 3.70/0.84    inference(resolution,[],[f3064,f352])).
% 3.70/0.84  fof(f352,plain,(
% 3.70/0.84    ( ! [X2] : (r2_hidden(sK3(sK2,sK12(sK2,X2)),sK12(sK2,X2)) | k1_xboole_0 = sK12(sK2,X2)) ) | (~spl14_6 | ~spl14_28)),
% 3.70/0.84    inference(resolution,[],[f347,f176])).
% 3.70/0.84  fof(f176,plain,(
% 3.70/0.84    ( ! [X0] : (r1_tarski(sK12(sK2,X0),k3_relat_1(sK2))) ) | ~spl14_6),
% 3.70/0.84    inference(duplicate_literal_removal,[],[f174])).
% 3.70/0.84  fof(f174,plain,(
% 3.70/0.84    ( ! [X0] : (r1_tarski(sK12(sK2,X0),k3_relat_1(sK2)) | r1_tarski(sK12(sK2,X0),k3_relat_1(sK2))) ) | ~spl14_6),
% 3.70/0.84    inference(resolution,[],[f173,f107])).
% 3.70/0.84  fof(f107,plain,(
% 3.70/0.84    ( ! [X0,X1] : (~r2_hidden(sK13(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 3.70/0.84    inference(cnf_transformation,[],[f64])).
% 3.70/0.84  fof(f64,plain,(
% 3.70/0.84    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK13(X0,X1),X1) & r2_hidden(sK13(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.70/0.84    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f62,f63])).
% 3.70/0.84  fof(f63,plain,(
% 3.70/0.84    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK13(X0,X1),X1) & r2_hidden(sK13(X0,X1),X0)))),
% 3.70/0.84    introduced(choice_axiom,[])).
% 3.70/0.84  fof(f62,plain,(
% 3.70/0.84    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.70/0.84    inference(rectify,[],[f61])).
% 3.70/0.84  fof(f61,plain,(
% 3.70/0.84    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.70/0.84    inference(nnf_transformation,[],[f26])).
% 3.70/0.84  fof(f26,plain,(
% 3.70/0.84    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.70/0.84    inference(ennf_transformation,[],[f1])).
% 3.70/0.84  fof(f1,axiom,(
% 3.70/0.84    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.70/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 3.70/0.84  fof(f173,plain,(
% 3.70/0.84    ( ! [X0,X1] : (r2_hidden(sK13(sK12(sK2,X0),X1),k3_relat_1(sK2)) | r1_tarski(sK12(sK2,X0),X1)) ) | ~spl14_6),
% 3.70/0.84    inference(resolution,[],[f172,f106])).
% 3.70/0.84  fof(f106,plain,(
% 3.70/0.84    ( ! [X0,X1] : (r2_hidden(sK13(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 3.70/0.84    inference(cnf_transformation,[],[f64])).
% 3.70/0.84  fof(f172,plain,(
% 3.70/0.84    ( ! [X0,X1] : (~r2_hidden(X0,sK12(sK2,X1)) | r2_hidden(X0,k3_relat_1(sK2))) ) | ~spl14_6),
% 3.70/0.84    inference(resolution,[],[f99,f141])).
% 3.70/0.84  fof(f141,plain,(
% 3.70/0.84    v1_relat_1(sK2) | ~spl14_6),
% 3.70/0.84    inference(avatar_component_clause,[],[f140])).
% 3.70/0.84  fof(f99,plain,(
% 3.70/0.84    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | ~r2_hidden(X3,sK12(X0,X1)) | r2_hidden(X3,k3_relat_1(X0))) )),
% 3.70/0.84    inference(cnf_transformation,[],[f58])).
% 3.70/0.84  fof(f58,plain,(
% 3.70/0.84    ! [X0,X1] : (! [X3] : ((r2_hidden(X3,sK12(X0,X1)) | r2_hidden(k4_tarski(X3,X1),X0) | ~r2_hidden(X3,k3_relat_1(X0))) & ((~r2_hidden(k4_tarski(X3,X1),X0) & r2_hidden(X3,k3_relat_1(X0))) | ~r2_hidden(X3,sK12(X0,X1)))) | ~v1_relat_1(X0))),
% 3.70/0.84    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f56,f57])).
% 3.70/0.84  fof(f57,plain,(
% 3.70/0.84    ! [X1,X0] : (? [X2] : ! [X3] : ((r2_hidden(X3,X2) | r2_hidden(k4_tarski(X3,X1),X0) | ~r2_hidden(X3,k3_relat_1(X0))) & ((~r2_hidden(k4_tarski(X3,X1),X0) & r2_hidden(X3,k3_relat_1(X0))) | ~r2_hidden(X3,X2))) => ! [X3] : ((r2_hidden(X3,sK12(X0,X1)) | r2_hidden(k4_tarski(X3,X1),X0) | ~r2_hidden(X3,k3_relat_1(X0))) & ((~r2_hidden(k4_tarski(X3,X1),X0) & r2_hidden(X3,k3_relat_1(X0))) | ~r2_hidden(X3,sK12(X0,X1)))))),
% 3.70/0.84    introduced(choice_axiom,[])).
% 3.70/0.84  fof(f56,plain,(
% 3.70/0.84    ! [X0,X1] : (? [X2] : ! [X3] : ((r2_hidden(X3,X2) | r2_hidden(k4_tarski(X3,X1),X0) | ~r2_hidden(X3,k3_relat_1(X0))) & ((~r2_hidden(k4_tarski(X3,X1),X0) & r2_hidden(X3,k3_relat_1(X0))) | ~r2_hidden(X3,X2))) | ~v1_relat_1(X0))),
% 3.70/0.84    inference(flattening,[],[f55])).
% 3.70/0.84  fof(f55,plain,(
% 3.70/0.84    ! [X0,X1] : (? [X2] : ! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(k4_tarski(X3,X1),X0) | ~r2_hidden(X3,k3_relat_1(X0)))) & ((~r2_hidden(k4_tarski(X3,X1),X0) & r2_hidden(X3,k3_relat_1(X0))) | ~r2_hidden(X3,X2))) | ~v1_relat_1(X0))),
% 3.70/0.84    inference(nnf_transformation,[],[f25])).
% 3.70/0.84  fof(f25,plain,(
% 3.70/0.84    ! [X0,X1] : (? [X2] : ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(k4_tarski(X3,X1),X0) & r2_hidden(X3,k3_relat_1(X0)))) | ~v1_relat_1(X0))),
% 3.70/0.84    inference(ennf_transformation,[],[f10])).
% 3.70/0.84  fof(f10,axiom,(
% 3.70/0.84    ! [X0,X1] : (v1_relat_1(X0) => ? [X2] : ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(k4_tarski(X3,X1),X0) & r2_hidden(X3,k3_relat_1(X0)))))),
% 3.70/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s1_xboole_0__e7_18__wellord1)).
% 3.70/0.84  fof(f347,plain,(
% 3.70/0.84    ( ! [X0] : (~r1_tarski(X0,k3_relat_1(sK2)) | r2_hidden(sK3(sK2,X0),X0) | k1_xboole_0 = X0) ) | ~spl14_28),
% 3.70/0.84    inference(avatar_component_clause,[],[f346])).
% 3.70/0.84  fof(f3064,plain,(
% 3.70/0.84    ( ! [X5] : (~r2_hidden(sK3(sK2,sK12(sK2,X5)),sK12(sK2,sK1)) | k1_xboole_0 = sK12(sK2,X5) | r2_hidden(k4_tarski(sK1,X5),sK2)) ) | ~spl14_296),
% 3.70/0.84    inference(avatar_component_clause,[],[f3063])).
% 3.70/0.84  fof(f4144,plain,(
% 3.70/0.84    sK0 != sK1 | r2_hidden(k4_tarski(sK0,sK1),sK2) | ~r2_hidden(k4_tarski(sK1,sK1),sK2)),
% 3.70/0.84    introduced(theory_tautology_sat_conflict,[])).
% 3.70/0.84  fof(f4139,plain,(
% 3.70/0.84    ~spl14_6 | ~spl14_395),
% 3.70/0.84    inference(avatar_split_clause,[],[f4137,f3991,f140])).
% 3.70/0.84  fof(f3991,plain,(
% 3.70/0.84    spl14_395 <=> r2_hidden(sK1,k1_wellord1(sK2,sK1))),
% 3.70/0.84    introduced(avatar_definition,[new_symbols(naming,[spl14_395])])).
% 3.70/0.84  fof(f4137,plain,(
% 3.70/0.84    ~v1_relat_1(sK2) | ~spl14_395),
% 3.70/0.84    inference(resolution,[],[f4133,f114])).
% 3.70/0.84  fof(f114,plain,(
% 3.70/0.84    ( ! [X4,X0] : (~r2_hidden(X4,k1_wellord1(X0,X4)) | ~v1_relat_1(X0)) )),
% 3.70/0.84    inference(equality_resolution,[],[f113])).
% 3.70/0.84  fof(f113,plain,(
% 3.70/0.84    ( ! [X4,X2,X0] : (~r2_hidden(X4,X2) | k1_wellord1(X0,X4) != X2 | ~v1_relat_1(X0)) )),
% 3.70/0.84    inference(equality_resolution,[],[f93])).
% 3.70/0.84  fof(f93,plain,(
% 3.70/0.84    ( ! [X4,X2,X0,X1] : (X1 != X4 | ~r2_hidden(X4,X2) | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 3.70/0.84    inference(cnf_transformation,[],[f54])).
% 3.70/0.84  fof(f54,plain,(
% 3.70/0.84    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK11(X0,X1,X2),X1),X0) | sK11(X0,X1,X2) = X1 | ~r2_hidden(sK11(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK11(X0,X1,X2),X1),X0) & sK11(X0,X1,X2) != X1) | r2_hidden(sK11(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 3.70/0.84    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f52,f53])).
% 3.70/0.84  fof(f53,plain,(
% 3.70/0.84    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2))) => ((~r2_hidden(k4_tarski(sK11(X0,X1,X2),X1),X0) | sK11(X0,X1,X2) = X1 | ~r2_hidden(sK11(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK11(X0,X1,X2),X1),X0) & sK11(X0,X1,X2) != X1) | r2_hidden(sK11(X0,X1,X2),X2))))),
% 3.70/0.84    introduced(choice_axiom,[])).
% 3.70/0.84  fof(f52,plain,(
% 3.70/0.84    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 3.70/0.84    inference(rectify,[],[f51])).
% 3.70/0.84  fof(f51,plain,(
% 3.70/0.84    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 3.70/0.84    inference(flattening,[],[f50])).
% 3.70/0.84  fof(f50,plain,(
% 3.70/0.84    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 3.70/0.84    inference(nnf_transformation,[],[f24])).
% 3.70/0.84  fof(f24,plain,(
% 3.70/0.84    ! [X0] : (! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))) | ~v1_relat_1(X0))),
% 3.70/0.84    inference(ennf_transformation,[],[f5])).
% 3.70/0.84  fof(f5,axiom,(
% 3.70/0.84    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))))),
% 3.70/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord1)).
% 3.70/0.84  fof(f4133,plain,(
% 3.70/0.84    r2_hidden(sK1,k1_wellord1(sK2,sK1)) | ~spl14_395),
% 3.70/0.84    inference(avatar_component_clause,[],[f3991])).
% 3.70/0.84  fof(f4134,plain,(
% 3.70/0.84    spl14_395 | ~spl14_2 | ~spl14_219),
% 3.70/0.84    inference(avatar_split_clause,[],[f4124,f2064,f121,f3991])).
% 3.70/0.84  fof(f121,plain,(
% 3.70/0.84    spl14_2 <=> r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))),
% 3.70/0.84    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).
% 3.70/0.84  fof(f2064,plain,(
% 3.70/0.84    spl14_219 <=> r2_hidden(sK1,k1_wellord1(sK2,sK0))),
% 3.70/0.84    introduced(avatar_definition,[new_symbols(naming,[spl14_219])])).
% 3.70/0.84  fof(f4124,plain,(
% 3.70/0.84    r2_hidden(sK1,k1_wellord1(sK2,sK1)) | (~spl14_2 | ~spl14_219)),
% 3.70/0.84    inference(resolution,[],[f4119,f2065])).
% 3.70/0.84  fof(f2065,plain,(
% 3.70/0.84    r2_hidden(sK1,k1_wellord1(sK2,sK0)) | ~spl14_219),
% 3.70/0.84    inference(avatar_component_clause,[],[f2064])).
% 3.70/0.84  fof(f4119,plain,(
% 3.70/0.84    ( ! [X0] : (~r2_hidden(X0,k1_wellord1(sK2,sK0)) | r2_hidden(X0,k1_wellord1(sK2,sK1))) ) | ~spl14_2),
% 3.70/0.84    inference(resolution,[],[f125,f105])).
% 3.70/0.84  fof(f105,plain,(
% 3.70/0.84    ( ! [X0,X3,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,X1)) )),
% 3.70/0.84    inference(cnf_transformation,[],[f64])).
% 3.70/0.84  fof(f125,plain,(
% 3.70/0.84    r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | ~spl14_2),
% 3.70/0.84    inference(avatar_component_clause,[],[f121])).
% 3.70/0.84  fof(f4111,plain,(
% 3.70/0.84    spl14_219 | spl14_136 | ~spl14_6 | ~spl14_106),
% 3.70/0.84    inference(avatar_split_clause,[],[f4106,f990,f140,f1176,f2064])).
% 3.70/0.84  fof(f1176,plain,(
% 3.70/0.84    spl14_136 <=> sK0 = sK1),
% 3.70/0.84    introduced(avatar_definition,[new_symbols(naming,[spl14_136])])).
% 3.70/0.84  fof(f990,plain,(
% 3.70/0.84    spl14_106 <=> r2_hidden(k4_tarski(sK1,sK0),sK2)),
% 3.70/0.84    introduced(avatar_definition,[new_symbols(naming,[spl14_106])])).
% 3.70/0.84  fof(f4106,plain,(
% 3.70/0.84    sK0 = sK1 | r2_hidden(sK1,k1_wellord1(sK2,sK0)) | (~spl14_6 | ~spl14_106)),
% 3.70/0.84    inference(resolution,[],[f991,f292])).
% 3.70/0.84  fof(f292,plain,(
% 3.70/0.84    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | X0 = X1 | r2_hidden(X0,k1_wellord1(sK2,X1))) ) | ~spl14_6),
% 3.70/0.84    inference(resolution,[],[f111,f141])).
% 3.70/0.84  fof(f111,plain,(
% 3.70/0.84    ( ! [X4,X0,X1] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4 | r2_hidden(X4,k1_wellord1(X0,X1))) )),
% 3.70/0.84    inference(equality_resolution,[],[f95])).
% 3.70/0.84  fof(f95,plain,(
% 3.70/0.84    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4 | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 3.70/0.84    inference(cnf_transformation,[],[f54])).
% 3.70/0.84  fof(f991,plain,(
% 3.70/0.84    r2_hidden(k4_tarski(sK1,sK0),sK2) | ~spl14_106),
% 3.70/0.84    inference(avatar_component_clause,[],[f990])).
% 3.70/0.84  fof(f3998,plain,(
% 3.70/0.84    spl14_1 | ~spl14_4 | ~spl14_6 | spl14_21),
% 3.70/0.84    inference(avatar_split_clause,[],[f1195,f256,f140,f132,f118])).
% 3.70/0.84  fof(f118,plain,(
% 3.70/0.84    spl14_1 <=> r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 3.70/0.84    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).
% 3.70/0.84  fof(f132,plain,(
% 3.70/0.84    spl14_4 <=> r2_hidden(sK0,k3_relat_1(sK2))),
% 3.70/0.84    introduced(avatar_definition,[new_symbols(naming,[spl14_4])])).
% 3.70/0.84  fof(f256,plain,(
% 3.70/0.84    spl14_21 <=> r2_hidden(sK0,sK12(sK2,sK1))),
% 3.70/0.84    introduced(avatar_definition,[new_symbols(naming,[spl14_21])])).
% 3.70/0.84  fof(f1195,plain,(
% 3.70/0.84    r2_hidden(k4_tarski(sK0,sK1),sK2) | (~spl14_4 | ~spl14_6 | spl14_21)),
% 3.70/0.84    inference(resolution,[],[f257,f436])).
% 3.70/0.84  fof(f436,plain,(
% 3.70/0.84    ( ! [X0] : (r2_hidden(sK0,sK12(sK2,X0)) | r2_hidden(k4_tarski(sK0,X0),sK2)) ) | (~spl14_4 | ~spl14_6)),
% 3.70/0.84    inference(resolution,[],[f434,f133])).
% 3.70/0.84  fof(f133,plain,(
% 3.70/0.84    r2_hidden(sK0,k3_relat_1(sK2)) | ~spl14_4),
% 3.70/0.84    inference(avatar_component_clause,[],[f132])).
% 3.70/0.84  fof(f434,plain,(
% 3.70/0.84    ( ! [X0,X1] : (~r2_hidden(X0,k3_relat_1(sK2)) | r2_hidden(k4_tarski(X0,X1),sK2) | r2_hidden(X0,sK12(sK2,X1))) ) | ~spl14_6),
% 3.70/0.84    inference(resolution,[],[f101,f141])).
% 3.70/0.84  fof(f101,plain,(
% 3.70/0.84    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(X3,X1),X0) | ~r2_hidden(X3,k3_relat_1(X0)) | r2_hidden(X3,sK12(X0,X1))) )),
% 3.70/0.84    inference(cnf_transformation,[],[f58])).
% 3.70/0.84  fof(f257,plain,(
% 3.70/0.84    ~r2_hidden(sK0,sK12(sK2,sK1)) | spl14_21),
% 3.70/0.84    inference(avatar_component_clause,[],[f256])).
% 3.70/0.84  fof(f3996,plain,(
% 3.70/0.84    spl14_136 | spl14_106 | spl14_1 | ~spl14_3 | ~spl14_4 | ~spl14_84),
% 3.70/0.84    inference(avatar_split_clause,[],[f1523,f869,f132,f128,f118,f990,f1176])).
% 3.70/0.84  fof(f128,plain,(
% 3.70/0.84    spl14_3 <=> r2_hidden(sK1,k3_relat_1(sK2))),
% 3.70/0.84    introduced(avatar_definition,[new_symbols(naming,[spl14_3])])).
% 3.70/0.84  fof(f869,plain,(
% 3.70/0.84    spl14_84 <=> ! [X1,X0] : (r2_hidden(k4_tarski(X0,X1),sK2) | r2_hidden(k4_tarski(X1,X0),sK2) | ~r2_hidden(X0,k3_relat_1(sK2)) | ~r2_hidden(X1,k3_relat_1(sK2)) | X0 = X1)),
% 3.70/0.84    introduced(avatar_definition,[new_symbols(naming,[spl14_84])])).
% 3.70/0.84  fof(f1523,plain,(
% 3.70/0.84    r2_hidden(k4_tarski(sK0,sK1),sK2) | r2_hidden(k4_tarski(sK1,sK0),sK2) | sK0 = sK1 | (~spl14_3 | ~spl14_4 | ~spl14_84)),
% 3.70/0.84    inference(resolution,[],[f1141,f129])).
% 3.70/0.84  fof(f129,plain,(
% 3.70/0.84    r2_hidden(sK1,k3_relat_1(sK2)) | ~spl14_3),
% 3.70/0.84    inference(avatar_component_clause,[],[f128])).
% 3.70/0.84  fof(f1141,plain,(
% 3.70/0.84    ( ! [X0] : (~r2_hidden(X0,k3_relat_1(sK2)) | r2_hidden(k4_tarski(sK0,X0),sK2) | r2_hidden(k4_tarski(X0,sK0),sK2) | sK0 = X0) ) | (~spl14_4 | ~spl14_84)),
% 3.70/0.84    inference(resolution,[],[f870,f133])).
% 3.70/0.84  fof(f870,plain,(
% 3.70/0.84    ( ! [X0,X1] : (~r2_hidden(X0,k3_relat_1(sK2)) | r2_hidden(k4_tarski(X1,X0),sK2) | r2_hidden(k4_tarski(X0,X1),sK2) | ~r2_hidden(X1,k3_relat_1(sK2)) | X0 = X1) ) | ~spl14_84),
% 3.70/0.84    inference(avatar_component_clause,[],[f869])).
% 3.70/0.84  fof(f3984,plain,(
% 3.70/0.84    spl14_2 | spl14_136 | ~spl14_1 | ~spl14_6 | ~spl14_45 | ~spl14_391),
% 3.70/0.84    inference(avatar_split_clause,[],[f3970,f3954,f500,f140,f118,f1176,f121])).
% 3.70/0.84  fof(f500,plain,(
% 3.70/0.84    spl14_45 <=> ! [X1,X0] : (~r2_hidden(k4_tarski(X0,X1),sK2) | X0 = X1 | ~r2_hidden(k4_tarski(X1,X0),sK2))),
% 3.70/0.84    introduced(avatar_definition,[new_symbols(naming,[spl14_45])])).
% 3.70/0.84  fof(f3954,plain,(
% 3.70/0.84    spl14_391 <=> sK1 = sK13(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))),
% 3.70/0.84    introduced(avatar_definition,[new_symbols(naming,[spl14_391])])).
% 3.70/0.84  fof(f3970,plain,(
% 3.70/0.84    ~r2_hidden(k4_tarski(sK0,sK1),sK2) | sK0 = sK1 | r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | (~spl14_6 | ~spl14_45 | ~spl14_391)),
% 3.70/0.84    inference(superposition,[],[f556,f3955])).
% 3.70/0.84  fof(f3955,plain,(
% 3.70/0.84    sK1 = sK13(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | ~spl14_391),
% 3.70/0.84    inference(avatar_component_clause,[],[f3954])).
% 3.70/0.84  fof(f556,plain,(
% 3.70/0.84    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,sK13(k1_wellord1(sK2,X0),X1)),sK2) | sK13(k1_wellord1(sK2,X0),X1) = X0 | r1_tarski(k1_wellord1(sK2,X0),X1)) ) | (~spl14_6 | ~spl14_45)),
% 3.70/0.84    inference(resolution,[],[f501,f181])).
% 3.70/0.84  fof(f181,plain,(
% 3.70/0.84    ( ! [X2,X1] : (r2_hidden(k4_tarski(sK13(k1_wellord1(sK2,X1),X2),X1),sK2) | r1_tarski(k1_wellord1(sK2,X1),X2)) ) | ~spl14_6),
% 3.70/0.84    inference(resolution,[],[f179,f106])).
% 3.70/0.84  fof(f179,plain,(
% 3.70/0.84    ( ! [X0,X1] : (~r2_hidden(X0,k1_wellord1(sK2,X1)) | r2_hidden(k4_tarski(X0,X1),sK2)) ) | ~spl14_6),
% 3.70/0.84    inference(resolution,[],[f112,f141])).
% 3.70/0.84  fof(f112,plain,(
% 3.70/0.84    ( ! [X4,X0,X1] : (~v1_relat_1(X0) | ~r2_hidden(X4,k1_wellord1(X0,X1)) | r2_hidden(k4_tarski(X4,X1),X0)) )),
% 3.70/0.84    inference(equality_resolution,[],[f94])).
% 3.70/0.84  fof(f94,plain,(
% 3.70/0.84    ( ! [X4,X2,X0,X1] : (r2_hidden(k4_tarski(X4,X1),X0) | ~r2_hidden(X4,X2) | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 3.70/0.84    inference(cnf_transformation,[],[f54])).
% 3.70/0.84  fof(f501,plain,(
% 3.70/0.84    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | X0 = X1 | ~r2_hidden(k4_tarski(X1,X0),sK2)) ) | ~spl14_45),
% 3.70/0.84    inference(avatar_component_clause,[],[f500])).
% 3.70/0.84  fof(f3956,plain,(
% 3.70/0.84    spl14_2 | spl14_391 | ~spl14_1 | ~spl14_6 | ~spl14_51),
% 3.70/0.84    inference(avatar_split_clause,[],[f3952,f577,f140,f118,f3954,f121])).
% 3.70/0.84  fof(f577,plain,(
% 3.70/0.84    spl14_51 <=> ! [X1,X0,X2] : (~r2_hidden(k4_tarski(X0,X1),sK2) | r2_hidden(k4_tarski(X2,X1),sK2) | ~r2_hidden(k4_tarski(X2,X0),sK2))),
% 3.70/0.84    introduced(avatar_definition,[new_symbols(naming,[spl14_51])])).
% 3.70/0.84  fof(f3952,plain,(
% 3.70/0.84    sK1 = sK13(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | (~spl14_1 | ~spl14_6 | ~spl14_51)),
% 3.70/0.84    inference(duplicate_literal_removal,[],[f3948])).
% 3.70/0.84  fof(f3948,plain,(
% 3.70/0.84    sK1 = sK13(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | (~spl14_1 | ~spl14_6 | ~spl14_51)),
% 3.70/0.84    inference(resolution,[],[f1685,f107])).
% 3.70/0.84  fof(f1685,plain,(
% 3.70/0.84    ( ! [X3] : (r2_hidden(sK13(k1_wellord1(sK2,sK0),X3),k1_wellord1(sK2,sK1)) | sK1 = sK13(k1_wellord1(sK2,sK0),X3) | r1_tarski(k1_wellord1(sK2,sK0),X3)) ) | (~spl14_1 | ~spl14_6 | ~spl14_51)),
% 3.70/0.84    inference(resolution,[],[f1404,f292])).
% 3.70/0.84  fof(f1404,plain,(
% 3.70/0.84    ( ! [X1] : (r2_hidden(k4_tarski(sK13(k1_wellord1(sK2,sK0),X1),sK1),sK2) | r1_tarski(k1_wellord1(sK2,sK0),X1)) ) | (~spl14_1 | ~spl14_6 | ~spl14_51)),
% 3.70/0.84    inference(resolution,[],[f1187,f181])).
% 3.70/0.84  fof(f1187,plain,(
% 3.70/0.84    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK0),sK2) | r2_hidden(k4_tarski(X0,sK1),sK2)) ) | (~spl14_1 | ~spl14_51)),
% 3.70/0.84    inference(resolution,[],[f124,f578])).
% 3.70/0.84  fof(f578,plain,(
% 3.70/0.84    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | r2_hidden(k4_tarski(X2,X1),sK2) | ~r2_hidden(k4_tarski(X2,X0),sK2)) ) | ~spl14_51),
% 3.70/0.84    inference(avatar_component_clause,[],[f577])).
% 3.70/0.84  fof(f124,plain,(
% 3.70/0.84    r2_hidden(k4_tarski(sK0,sK1),sK2) | ~spl14_1),
% 3.70/0.84    inference(avatar_component_clause,[],[f118])).
% 3.70/0.84  fof(f3065,plain,(
% 3.70/0.84    ~spl14_6 | spl14_296 | ~spl14_3 | ~spl14_6 | ~spl14_64),
% 3.70/0.84    inference(avatar_split_clause,[],[f3055,f685,f140,f128,f3063,f140])).
% 3.70/0.84  fof(f685,plain,(
% 3.70/0.84    spl14_64 <=> ! [X1,X0] : (~r2_hidden(X0,X1) | r2_hidden(k4_tarski(sK3(sK2,X1),X0),sK2) | ~r1_tarski(X1,k3_relat_1(sK2)) | k1_xboole_0 = X1)),
% 3.70/0.84    introduced(avatar_definition,[new_symbols(naming,[spl14_64])])).
% 3.70/0.84  fof(f3055,plain,(
% 3.70/0.84    ( ! [X5] : (k1_xboole_0 = sK12(sK2,X5) | r2_hidden(k4_tarski(sK1,X5),sK2) | ~r2_hidden(sK3(sK2,sK12(sK2,X5)),sK12(sK2,sK1)) | ~v1_relat_1(sK2)) ) | (~spl14_3 | ~spl14_6 | ~spl14_64)),
% 3.70/0.84    inference(resolution,[],[f2758,f100])).
% 3.70/0.84  fof(f100,plain,(
% 3.70/0.84    ( ! [X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X1),X0) | ~r2_hidden(X3,sK12(X0,X1)) | ~v1_relat_1(X0)) )),
% 3.70/0.84    inference(cnf_transformation,[],[f58])).
% 3.70/0.84  fof(f2758,plain,(
% 3.70/0.84    ( ! [X3] : (r2_hidden(k4_tarski(sK3(sK2,sK12(sK2,X3)),sK1),sK2) | k1_xboole_0 = sK12(sK2,X3) | r2_hidden(k4_tarski(sK1,X3),sK2)) ) | (~spl14_3 | ~spl14_6 | ~spl14_64)),
% 3.70/0.84    inference(resolution,[],[f806,f437])).
% 3.70/0.84  fof(f437,plain,(
% 3.70/0.84    ( ! [X1] : (r2_hidden(sK1,sK12(sK2,X1)) | r2_hidden(k4_tarski(sK1,X1),sK2)) ) | (~spl14_3 | ~spl14_6)),
% 3.70/0.84    inference(resolution,[],[f434,f129])).
% 3.70/0.84  fof(f806,plain,(
% 3.70/0.84    ( ! [X6,X7] : (~r2_hidden(X7,sK12(sK2,X6)) | r2_hidden(k4_tarski(sK3(sK2,sK12(sK2,X6)),X7),sK2) | k1_xboole_0 = sK12(sK2,X6)) ) | (~spl14_6 | ~spl14_64)),
% 3.70/0.84    inference(resolution,[],[f686,f176])).
% 3.70/0.84  fof(f686,plain,(
% 3.70/0.84    ( ! [X0,X1] : (~r1_tarski(X1,k3_relat_1(sK2)) | r2_hidden(k4_tarski(sK3(sK2,X1),X0),sK2) | ~r2_hidden(X0,X1) | k1_xboole_0 = X1) ) | ~spl14_64),
% 3.70/0.84    inference(avatar_component_clause,[],[f685])).
% 3.70/0.84  fof(f1362,plain,(
% 3.70/0.84    spl14_141),
% 3.70/0.84    inference(avatar_contradiction_clause,[],[f1361])).
% 3.70/0.84  fof(f1361,plain,(
% 3.70/0.84    $false | spl14_141),
% 3.70/0.84    inference(resolution,[],[f1358,f115])).
% 3.70/0.84  fof(f115,plain,(
% 3.70/0.84    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.70/0.84    inference(equality_resolution,[],[f103])).
% 3.70/0.84  fof(f103,plain,(
% 3.70/0.84    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.70/0.84    inference(cnf_transformation,[],[f60])).
% 3.70/0.84  fof(f60,plain,(
% 3.70/0.84    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.70/0.84    inference(flattening,[],[f59])).
% 3.70/0.84  fof(f59,plain,(
% 3.70/0.84    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.70/0.84    inference(nnf_transformation,[],[f2])).
% 3.70/0.84  fof(f2,axiom,(
% 3.70/0.84    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.70/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.70/0.84  fof(f1358,plain,(
% 3.70/0.84    ~r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0)) | spl14_141),
% 3.70/0.84    inference(avatar_component_clause,[],[f1357])).
% 3.70/0.84  fof(f1357,plain,(
% 3.70/0.84    spl14_141 <=> r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0))),
% 3.70/0.84    introduced(avatar_definition,[new_symbols(naming,[spl14_141])])).
% 3.70/0.84  fof(f1359,plain,(
% 3.70/0.84    ~spl14_141 | spl14_2 | ~spl14_136),
% 3.70/0.84    inference(avatar_split_clause,[],[f1336,f1176,f121,f1357])).
% 3.70/0.84  fof(f1336,plain,(
% 3.70/0.84    ~r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0)) | (spl14_2 | ~spl14_136)),
% 3.70/0.84    inference(superposition,[],[f122,f1177])).
% 3.70/0.84  fof(f1177,plain,(
% 3.70/0.84    sK0 = sK1 | ~spl14_136),
% 3.70/0.84    inference(avatar_component_clause,[],[f1176])).
% 3.70/0.84  fof(f122,plain,(
% 3.70/0.84    ~r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | spl14_2),
% 3.70/0.84    inference(avatar_component_clause,[],[f121])).
% 3.70/0.84  fof(f893,plain,(
% 3.70/0.84    ~spl14_6 | ~spl14_5 | spl14_83),
% 3.70/0.84    inference(avatar_split_clause,[],[f876,f866,f136,f140])).
% 3.70/0.84  fof(f136,plain,(
% 3.70/0.84    spl14_5 <=> v2_wellord1(sK2)),
% 3.70/0.84    introduced(avatar_definition,[new_symbols(naming,[spl14_5])])).
% 3.70/0.84  fof(f866,plain,(
% 3.70/0.84    spl14_83 <=> v6_relat_2(sK2)),
% 3.70/0.84    introduced(avatar_definition,[new_symbols(naming,[spl14_83])])).
% 3.70/0.84  fof(f876,plain,(
% 3.70/0.84    ~v2_wellord1(sK2) | ~v1_relat_1(sK2) | spl14_83),
% 3.70/0.84    inference(resolution,[],[f867,f90])).
% 3.70/0.84  fof(f90,plain,(
% 3.70/0.84    ( ! [X0] : (v6_relat_2(X0) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 3.70/0.84    inference(cnf_transformation,[],[f49])).
% 3.70/0.84  fof(f49,plain,(
% 3.70/0.84    ! [X0] : (((v2_wellord1(X0) | ~v1_wellord1(X0) | ~v6_relat_2(X0) | ~v4_relat_2(X0) | ~v8_relat_2(X0) | ~v1_relat_2(X0)) & ((v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0)) | ~v2_wellord1(X0))) | ~v1_relat_1(X0))),
% 3.70/0.84    inference(flattening,[],[f48])).
% 3.70/0.84  fof(f48,plain,(
% 3.70/0.84    ! [X0] : (((v2_wellord1(X0) | (~v1_wellord1(X0) | ~v6_relat_2(X0) | ~v4_relat_2(X0) | ~v8_relat_2(X0) | ~v1_relat_2(X0))) & ((v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0)) | ~v2_wellord1(X0))) | ~v1_relat_1(X0))),
% 3.70/0.84    inference(nnf_transformation,[],[f23])).
% 3.70/0.84  fof(f23,plain,(
% 3.70/0.84    ! [X0] : ((v2_wellord1(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0))) | ~v1_relat_1(X0))),
% 3.70/0.84    inference(ennf_transformation,[],[f6])).
% 3.70/0.84  fof(f6,axiom,(
% 3.70/0.84    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0))))),
% 3.70/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_wellord1)).
% 3.70/0.84  fof(f867,plain,(
% 3.70/0.84    ~v6_relat_2(sK2) | spl14_83),
% 3.70/0.84    inference(avatar_component_clause,[],[f866])).
% 3.70/0.84  fof(f871,plain,(
% 3.70/0.84    ~spl14_83 | spl14_84 | ~spl14_6),
% 3.70/0.84    inference(avatar_split_clause,[],[f864,f140,f869,f866])).
% 3.70/0.84  fof(f864,plain,(
% 3.70/0.84    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,X1),sK2) | X0 = X1 | ~r2_hidden(X1,k3_relat_1(sK2)) | ~r2_hidden(X0,k3_relat_1(sK2)) | ~v6_relat_2(sK2) | r2_hidden(k4_tarski(X1,X0),sK2)) ) | ~spl14_6),
% 3.70/0.84    inference(resolution,[],[f77,f141])).
% 3.70/0.84  fof(f77,plain,(
% 3.70/0.84    ( ! [X4,X0,X3] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(X3,X4),X0) | X3 = X4 | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0)) | ~v6_relat_2(X0) | r2_hidden(k4_tarski(X4,X3),X0)) )),
% 3.70/0.84    inference(cnf_transformation,[],[f43])).
% 3.70/0.84  fof(f43,plain,(
% 3.70/0.84    ! [X0] : (((v6_relat_2(X0) | (~r2_hidden(k4_tarski(sK7(X0),sK6(X0)),X0) & ~r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0) & sK6(X0) != sK7(X0) & r2_hidden(sK7(X0),k3_relat_1(X0)) & r2_hidden(sK6(X0),k3_relat_1(X0)))) & (! [X3,X4] : (r2_hidden(k4_tarski(X4,X3),X0) | r2_hidden(k4_tarski(X3,X4),X0) | X3 = X4 | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0))) | ~v6_relat_2(X0))) | ~v1_relat_1(X0))),
% 3.70/0.84    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f41,f42])).
% 3.70/0.84  fof(f42,plain,(
% 3.70/0.84    ! [X0] : (? [X1,X2] : (~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0))) => (~r2_hidden(k4_tarski(sK7(X0),sK6(X0)),X0) & ~r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0) & sK6(X0) != sK7(X0) & r2_hidden(sK7(X0),k3_relat_1(X0)) & r2_hidden(sK6(X0),k3_relat_1(X0))))),
% 3.70/0.84    introduced(choice_axiom,[])).
% 3.70/0.84  fof(f41,plain,(
% 3.70/0.84    ! [X0] : (((v6_relat_2(X0) | ? [X1,X2] : (~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))) & (! [X3,X4] : (r2_hidden(k4_tarski(X4,X3),X0) | r2_hidden(k4_tarski(X3,X4),X0) | X3 = X4 | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0))) | ~v6_relat_2(X0))) | ~v1_relat_1(X0))),
% 3.70/0.84    inference(rectify,[],[f40])).
% 3.70/0.84  fof(f40,plain,(
% 3.70/0.84    ! [X0] : (((v6_relat_2(X0) | ? [X1,X2] : (~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))) & (! [X1,X2] : (r2_hidden(k4_tarski(X2,X1),X0) | r2_hidden(k4_tarski(X1,X2),X0) | X1 = X2 | ~r2_hidden(X2,k3_relat_1(X0)) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v6_relat_2(X0))) | ~v1_relat_1(X0))),
% 3.70/0.84    inference(nnf_transformation,[],[f20])).
% 3.70/0.84  fof(f20,plain,(
% 3.70/0.84    ! [X0] : ((v6_relat_2(X0) <=> ! [X1,X2] : (r2_hidden(k4_tarski(X2,X1),X0) | r2_hidden(k4_tarski(X1,X2),X0) | X1 = X2 | ~r2_hidden(X2,k3_relat_1(X0)) | ~r2_hidden(X1,k3_relat_1(X0)))) | ~v1_relat_1(X0))),
% 3.70/0.84    inference(ennf_transformation,[],[f9])).
% 3.70/0.84  fof(f9,axiom,(
% 3.70/0.84    ! [X0] : (v1_relat_1(X0) => (v6_relat_2(X0) <=> ! [X1,X2] : ~(~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))))),
% 3.70/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l4_wellord1)).
% 3.70/0.84  fof(f861,plain,(
% 3.70/0.84    ~spl14_12 | ~spl14_29 | spl14_37),
% 3.70/0.84    inference(avatar_contradiction_clause,[],[f860])).
% 3.70/0.84  fof(f860,plain,(
% 3.70/0.84    $false | (~spl14_12 | ~spl14_29 | spl14_37)),
% 3.70/0.84    inference(resolution,[],[f393,f399])).
% 3.70/0.84  fof(f399,plain,(
% 3.70/0.84    ( ! [X4] : (r1_tarski(k1_xboole_0,X4)) ) | (~spl14_12 | ~spl14_29)),
% 3.70/0.84    inference(superposition,[],[f219,f355])).
% 3.70/0.84  fof(f355,plain,(
% 3.70/0.84    k1_xboole_0 = k1_wellord1(sK2,k2_relat_1(sK2)) | ~spl14_29),
% 3.70/0.84    inference(avatar_component_clause,[],[f354])).
% 3.70/0.84  fof(f354,plain,(
% 3.70/0.84    spl14_29 <=> k1_xboole_0 = k1_wellord1(sK2,k2_relat_1(sK2))),
% 3.70/0.84    introduced(avatar_definition,[new_symbols(naming,[spl14_29])])).
% 3.70/0.84  fof(f219,plain,(
% 3.70/0.84    ( ! [X0] : (r1_tarski(k1_wellord1(sK2,k2_relat_1(sK2)),X0)) ) | ~spl14_12),
% 3.70/0.84    inference(resolution,[],[f202,f115])).
% 3.70/0.84  fof(f202,plain,(
% 3.70/0.84    ( ! [X10,X9] : (~r1_tarski(k2_relat_1(sK2),X9) | r1_tarski(k1_wellord1(sK2,X9),X10)) ) | ~spl14_12),
% 3.70/0.84    inference(resolution,[],[f193,f108])).
% 3.70/0.84  fof(f193,plain,(
% 3.70/0.84    ( ! [X2,X3] : (r2_hidden(X2,k2_relat_1(sK2)) | r1_tarski(k1_wellord1(sK2,X2),X3)) ) | ~spl14_12),
% 3.70/0.84    inference(avatar_component_clause,[],[f192])).
% 3.70/0.84  fof(f192,plain,(
% 3.70/0.84    spl14_12 <=> ! [X3,X2] : (r1_tarski(k1_wellord1(sK2,X2),X3) | r2_hidden(X2,k2_relat_1(sK2)))),
% 3.70/0.84    introduced(avatar_definition,[new_symbols(naming,[spl14_12])])).
% 3.70/0.84  fof(f393,plain,(
% 3.70/0.84    ~r1_tarski(k1_xboole_0,sK0) | spl14_37),
% 3.70/0.84    inference(avatar_component_clause,[],[f392])).
% 3.70/0.84  fof(f771,plain,(
% 3.70/0.84    ~spl14_12 | spl14_59),
% 3.70/0.84    inference(avatar_contradiction_clause,[],[f769])).
% 3.70/0.84  fof(f769,plain,(
% 3.70/0.84    $false | (~spl14_12 | spl14_59)),
% 3.70/0.84    inference(resolution,[],[f642,f219])).
% 3.70/0.84  fof(f642,plain,(
% 3.70/0.84    ~r1_tarski(k1_wellord1(sK2,k2_relat_1(sK2)),sK3(sK2,k1_wellord1(sK2,k2_relat_1(sK2)))) | spl14_59),
% 3.70/0.84    inference(avatar_component_clause,[],[f641])).
% 3.70/0.84  fof(f641,plain,(
% 3.70/0.84    spl14_59 <=> r1_tarski(k1_wellord1(sK2,k2_relat_1(sK2)),sK3(sK2,k1_wellord1(sK2,k2_relat_1(sK2))))),
% 3.70/0.84    introduced(avatar_definition,[new_symbols(naming,[spl14_59])])).
% 3.70/0.84  fof(f687,plain,(
% 3.70/0.84    ~spl14_5 | spl14_64 | ~spl14_6),
% 3.70/0.84    inference(avatar_split_clause,[],[f683,f140,f685,f136])).
% 3.70/0.84  fof(f683,plain,(
% 3.70/0.84    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_xboole_0 = X1 | ~r1_tarski(X1,k3_relat_1(sK2)) | ~v2_wellord1(sK2) | r2_hidden(k4_tarski(sK3(sK2,X1),X0),sK2)) ) | ~spl14_6),
% 3.70/0.84    inference(resolution,[],[f72,f141])).
% 3.70/0.84  fof(f72,plain,(
% 3.70/0.84    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | ~r2_hidden(X3,X1) | k1_xboole_0 = X1 | ~r1_tarski(X1,k3_relat_1(X0)) | ~v2_wellord1(X0) | r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)) )),
% 3.70/0.84    inference(cnf_transformation,[],[f35])).
% 3.70/0.84  fof(f35,plain,(
% 3.70/0.84    ! [X0] : (! [X1] : ((! [X3] : (r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(X3,X1)) & r2_hidden(sK3(X0,X1),X1)) | k1_xboole_0 = X1 | ~r1_tarski(X1,k3_relat_1(X0))) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 3.70/0.84    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f34])).
% 3.70/0.84  fof(f34,plain,(
% 3.70/0.84    ! [X1,X0] : (? [X2] : (! [X3] : (r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) => (! [X3] : (r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(X3,X1)) & r2_hidden(sK3(X0,X1),X1)))),
% 3.70/0.84    introduced(choice_axiom,[])).
% 3.70/0.84  fof(f17,plain,(
% 3.70/0.84    ! [X0] : (! [X1] : (? [X2] : (! [X3] : (r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | k1_xboole_0 = X1 | ~r1_tarski(X1,k3_relat_1(X0))) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 3.70/0.84    inference(flattening,[],[f16])).
% 3.70/0.84  fof(f16,plain,(
% 3.70/0.84    ! [X0] : ((! [X1] : (? [X2] : (! [X3] : (r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | k1_xboole_0 = X1 | ~r1_tarski(X1,k3_relat_1(X0))) | ~v2_wellord1(X0)) | ~v1_relat_1(X0))),
% 3.70/0.84    inference(ennf_transformation,[],[f11])).
% 3.70/0.84  fof(f11,axiom,(
% 3.70/0.84    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) => ! [X1] : ~(! [X2] : ~(! [X3] : (r2_hidden(X3,X1) => r2_hidden(k4_tarski(X2,X3),X0)) & r2_hidden(X2,X1)) & k1_xboole_0 != X1 & r1_tarski(X1,k3_relat_1(X0)))))),
% 3.70/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_wellord1)).
% 3.70/0.84  fof(f643,plain,(
% 3.70/0.84    ~spl14_59 | ~spl14_30),
% 3.70/0.84    inference(avatar_split_clause,[],[f631,f357,f641])).
% 3.70/0.84  fof(f357,plain,(
% 3.70/0.84    spl14_30 <=> r2_hidden(sK3(sK2,k1_wellord1(sK2,k2_relat_1(sK2))),k1_wellord1(sK2,k2_relat_1(sK2)))),
% 3.70/0.84    introduced(avatar_definition,[new_symbols(naming,[spl14_30])])).
% 3.70/0.84  fof(f631,plain,(
% 3.70/0.84    ~r1_tarski(k1_wellord1(sK2,k2_relat_1(sK2)),sK3(sK2,k1_wellord1(sK2,k2_relat_1(sK2)))) | ~spl14_30),
% 3.70/0.84    inference(resolution,[],[f358,f108])).
% 3.70/0.84  fof(f358,plain,(
% 3.70/0.84    r2_hidden(sK3(sK2,k1_wellord1(sK2,k2_relat_1(sK2))),k1_wellord1(sK2,k2_relat_1(sK2))) | ~spl14_30),
% 3.70/0.84    inference(avatar_component_clause,[],[f357])).
% 3.70/0.84  fof(f596,plain,(
% 3.70/0.84    ~spl14_6 | ~spl14_5 | spl14_50),
% 3.70/0.84    inference(avatar_split_clause,[],[f583,f574,f136,f140])).
% 3.70/0.84  fof(f574,plain,(
% 3.70/0.84    spl14_50 <=> v8_relat_2(sK2)),
% 3.70/0.84    introduced(avatar_definition,[new_symbols(naming,[spl14_50])])).
% 3.70/0.84  fof(f583,plain,(
% 3.70/0.84    ~v2_wellord1(sK2) | ~v1_relat_1(sK2) | spl14_50),
% 3.70/0.84    inference(resolution,[],[f575,f88])).
% 3.70/0.84  fof(f88,plain,(
% 3.70/0.84    ( ! [X0] : (v8_relat_2(X0) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 3.70/0.84    inference(cnf_transformation,[],[f49])).
% 3.70/0.84  fof(f575,plain,(
% 3.70/0.84    ~v8_relat_2(sK2) | spl14_50),
% 3.70/0.84    inference(avatar_component_clause,[],[f574])).
% 3.70/0.84  fof(f579,plain,(
% 3.70/0.84    ~spl14_50 | spl14_51 | ~spl14_6),
% 3.70/0.84    inference(avatar_split_clause,[],[f572,f140,f577,f574])).
% 3.70/0.84  fof(f572,plain,(
% 3.70/0.84    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | ~r2_hidden(k4_tarski(X2,X0),sK2) | ~v8_relat_2(sK2) | r2_hidden(k4_tarski(X2,X1),sK2)) ) | ~spl14_6),
% 3.70/0.84    inference(resolution,[],[f83,f141])).
% 3.70/0.84  fof(f83,plain,(
% 3.70/0.84    ( ! [X6,X4,X0,X5] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(k4_tarski(X4,X5),X0) | ~v8_relat_2(X0) | r2_hidden(k4_tarski(X4,X6),X0)) )),
% 3.70/0.84    inference(cnf_transformation,[],[f47])).
% 3.70/0.84  fof(f47,plain,(
% 3.70/0.84    ! [X0] : (((v8_relat_2(X0) | (~r2_hidden(k4_tarski(sK8(X0),sK10(X0)),X0) & r2_hidden(k4_tarski(sK9(X0),sK10(X0)),X0) & r2_hidden(k4_tarski(sK8(X0),sK9(X0)),X0))) & (! [X4,X5,X6] : (r2_hidden(k4_tarski(X4,X6),X0) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~v8_relat_2(X0))) | ~v1_relat_1(X0))),
% 3.70/0.84    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f45,f46])).
% 3.70/0.86  fof(f46,plain,(
% 3.70/0.86    ! [X0] : (? [X1,X2,X3] : (~r2_hidden(k4_tarski(X1,X3),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(k4_tarski(X1,X2),X0)) => (~r2_hidden(k4_tarski(sK8(X0),sK10(X0)),X0) & r2_hidden(k4_tarski(sK9(X0),sK10(X0)),X0) & r2_hidden(k4_tarski(sK8(X0),sK9(X0)),X0)))),
% 3.70/0.86    introduced(choice_axiom,[])).
% 3.70/0.86  fof(f45,plain,(
% 3.70/0.86    ! [X0] : (((v8_relat_2(X0) | ? [X1,X2,X3] : (~r2_hidden(k4_tarski(X1,X3),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(k4_tarski(X1,X2),X0))) & (! [X4,X5,X6] : (r2_hidden(k4_tarski(X4,X6),X0) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~v8_relat_2(X0))) | ~v1_relat_1(X0))),
% 3.70/0.86    inference(rectify,[],[f44])).
% 3.70/0.86  fof(f44,plain,(
% 3.70/0.86    ! [X0] : (((v8_relat_2(X0) | ? [X1,X2,X3] : (~r2_hidden(k4_tarski(X1,X3),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(k4_tarski(X1,X2),X0))) & (! [X1,X2,X3] : (r2_hidden(k4_tarski(X1,X3),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(k4_tarski(X1,X2),X0)) | ~v8_relat_2(X0))) | ~v1_relat_1(X0))),
% 3.70/0.86    inference(nnf_transformation,[],[f22])).
% 3.70/0.86  fof(f22,plain,(
% 3.70/0.86    ! [X0] : ((v8_relat_2(X0) <=> ! [X1,X2,X3] : (r2_hidden(k4_tarski(X1,X3),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(k4_tarski(X1,X2),X0))) | ~v1_relat_1(X0))),
% 3.70/0.86    inference(flattening,[],[f21])).
% 3.70/0.86  fof(f21,plain,(
% 3.70/0.86    ! [X0] : ((v8_relat_2(X0) <=> ! [X1,X2,X3] : (r2_hidden(k4_tarski(X1,X3),X0) | (~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(k4_tarski(X1,X2),X0)))) | ~v1_relat_1(X0))),
% 3.70/0.86    inference(ennf_transformation,[],[f7])).
% 3.70/0.86  fof(f7,axiom,(
% 3.70/0.86    ! [X0] : (v1_relat_1(X0) => (v8_relat_2(X0) <=> ! [X1,X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(k4_tarski(X1,X2),X0)) => r2_hidden(k4_tarski(X1,X3),X0))))),
% 3.70/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l2_wellord1)).
% 3.70/0.86  fof(f514,plain,(
% 3.70/0.86    ~spl14_6 | ~spl14_5 | spl14_44),
% 3.70/0.86    inference(avatar_split_clause,[],[f505,f497,f136,f140])).
% 3.70/0.86  fof(f497,plain,(
% 3.70/0.86    spl14_44 <=> v4_relat_2(sK2)),
% 3.70/0.86    introduced(avatar_definition,[new_symbols(naming,[spl14_44])])).
% 3.70/0.86  fof(f505,plain,(
% 3.70/0.86    ~v2_wellord1(sK2) | ~v1_relat_1(sK2) | spl14_44),
% 3.70/0.86    inference(resolution,[],[f498,f89])).
% 3.70/0.86  fof(f89,plain,(
% 3.70/0.86    ( ! [X0] : (v4_relat_2(X0) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 3.70/0.86    inference(cnf_transformation,[],[f49])).
% 3.70/0.86  fof(f498,plain,(
% 3.70/0.86    ~v4_relat_2(sK2) | spl14_44),
% 3.70/0.86    inference(avatar_component_clause,[],[f497])).
% 3.70/0.86  fof(f502,plain,(
% 3.70/0.86    ~spl14_44 | spl14_45 | ~spl14_6),
% 3.70/0.86    inference(avatar_split_clause,[],[f495,f140,f500,f497])).
% 3.70/0.86  fof(f495,plain,(
% 3.70/0.86    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | ~r2_hidden(k4_tarski(X1,X0),sK2) | ~v4_relat_2(sK2) | X0 = X1) ) | ~spl14_6),
% 3.70/0.86    inference(resolution,[],[f73,f141])).
% 3.70/0.86  fof(f73,plain,(
% 3.70/0.86    ( ! [X4,X0,X3] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(X4,X3),X0) | ~r2_hidden(k4_tarski(X3,X4),X0) | ~v4_relat_2(X0) | X3 = X4) )),
% 3.70/0.86    inference(cnf_transformation,[],[f39])).
% 3.70/0.86  fof(f39,plain,(
% 3.70/0.86    ! [X0] : (((v4_relat_2(X0) | (sK4(X0) != sK5(X0) & r2_hidden(k4_tarski(sK5(X0),sK4(X0)),X0) & r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0))) & (! [X3,X4] : (X3 = X4 | ~r2_hidden(k4_tarski(X4,X3),X0) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~v4_relat_2(X0))) | ~v1_relat_1(X0))),
% 3.70/0.86    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f37,f38])).
% 3.70/0.86  fof(f38,plain,(
% 3.70/0.86    ! [X0] : (? [X1,X2] : (X1 != X2 & r2_hidden(k4_tarski(X2,X1),X0) & r2_hidden(k4_tarski(X1,X2),X0)) => (sK4(X0) != sK5(X0) & r2_hidden(k4_tarski(sK5(X0),sK4(X0)),X0) & r2_hidden(k4_tarski(sK4(X0),sK5(X0)),X0)))),
% 3.70/0.86    introduced(choice_axiom,[])).
% 3.70/0.86  fof(f37,plain,(
% 3.70/0.86    ! [X0] : (((v4_relat_2(X0) | ? [X1,X2] : (X1 != X2 & r2_hidden(k4_tarski(X2,X1),X0) & r2_hidden(k4_tarski(X1,X2),X0))) & (! [X3,X4] : (X3 = X4 | ~r2_hidden(k4_tarski(X4,X3),X0) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~v4_relat_2(X0))) | ~v1_relat_1(X0))),
% 3.70/0.86    inference(rectify,[],[f36])).
% 3.70/0.86  fof(f36,plain,(
% 3.70/0.86    ! [X0] : (((v4_relat_2(X0) | ? [X1,X2] : (X1 != X2 & r2_hidden(k4_tarski(X2,X1),X0) & r2_hidden(k4_tarski(X1,X2),X0))) & (! [X1,X2] : (X1 = X2 | ~r2_hidden(k4_tarski(X2,X1),X0) | ~r2_hidden(k4_tarski(X1,X2),X0)) | ~v4_relat_2(X0))) | ~v1_relat_1(X0))),
% 3.70/0.86    inference(nnf_transformation,[],[f19])).
% 3.70/0.87  fof(f19,plain,(
% 3.70/0.87    ! [X0] : ((v4_relat_2(X0) <=> ! [X1,X2] : (X1 = X2 | ~r2_hidden(k4_tarski(X2,X1),X0) | ~r2_hidden(k4_tarski(X1,X2),X0))) | ~v1_relat_1(X0))),
% 3.70/0.87    inference(flattening,[],[f18])).
% 3.70/0.87  fof(f18,plain,(
% 3.70/0.87    ! [X0] : ((v4_relat_2(X0) <=> ! [X1,X2] : (X1 = X2 | (~r2_hidden(k4_tarski(X2,X1),X0) | ~r2_hidden(k4_tarski(X1,X2),X0)))) | ~v1_relat_1(X0))),
% 3.70/0.87    inference(ennf_transformation,[],[f8])).
% 3.70/0.87  fof(f8,axiom,(
% 3.70/0.87    ! [X0] : (v1_relat_1(X0) => (v4_relat_2(X0) <=> ! [X1,X2] : ((r2_hidden(k4_tarski(X2,X1),X0) & r2_hidden(k4_tarski(X1,X2),X0)) => X1 = X2)))),
% 3.70/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_wellord1)).
% 3.70/0.87  fof(f359,plain,(
% 3.70/0.87    spl14_29 | spl14_30 | ~spl14_12 | ~spl14_28),
% 3.70/0.87    inference(avatar_split_clause,[],[f349,f346,f192,f357,f354])).
% 3.70/0.87  fof(f349,plain,(
% 3.70/0.87    r2_hidden(sK3(sK2,k1_wellord1(sK2,k2_relat_1(sK2))),k1_wellord1(sK2,k2_relat_1(sK2))) | k1_xboole_0 = k1_wellord1(sK2,k2_relat_1(sK2)) | (~spl14_12 | ~spl14_28)),
% 3.70/0.87    inference(resolution,[],[f347,f219])).
% 3.70/0.87  fof(f348,plain,(
% 3.70/0.87    ~spl14_5 | spl14_28 | ~spl14_6),
% 3.70/0.87    inference(avatar_split_clause,[],[f343,f140,f346,f136])).
% 3.70/0.87  fof(f343,plain,(
% 3.70/0.87    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k3_relat_1(sK2)) | ~v2_wellord1(sK2) | r2_hidden(sK3(sK2,X0),X0)) ) | ~spl14_6),
% 3.70/0.87    inference(resolution,[],[f71,f141])).
% 3.70/0.87  fof(f71,plain,(
% 3.70/0.87    ( ! [X0,X1] : (~v1_relat_1(X0) | k1_xboole_0 = X1 | ~r1_tarski(X1,k3_relat_1(X0)) | ~v2_wellord1(X0) | r2_hidden(sK3(X0,X1),X1)) )),
% 3.70/0.87    inference(cnf_transformation,[],[f35])).
% 3.70/0.87  fof(f258,plain,(
% 3.70/0.87    ~spl14_6 | ~spl14_21 | ~spl14_1),
% 3.70/0.87    inference(avatar_split_clause,[],[f251,f118,f256,f140])).
% 3.70/0.87  fof(f251,plain,(
% 3.70/0.87    ~r2_hidden(sK0,sK12(sK2,sK1)) | ~v1_relat_1(sK2) | ~spl14_1),
% 3.70/0.87    inference(resolution,[],[f124,f100])).
% 3.70/0.87  fof(f194,plain,(
% 3.70/0.87    ~spl14_6 | spl14_12 | ~spl14_6),
% 3.70/0.87    inference(avatar_split_clause,[],[f183,f140,f192,f140])).
% 3.70/0.87  fof(f183,plain,(
% 3.70/0.87    ( ! [X2,X3] : (r1_tarski(k1_wellord1(sK2,X2),X3) | r2_hidden(X2,k2_relat_1(sK2)) | ~v1_relat_1(sK2)) ) | ~spl14_6),
% 3.70/0.87    inference(resolution,[],[f181,f110])).
% 3.70/0.87  fof(f110,plain,(
% 3.70/0.87    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X1,k2_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 3.70/0.87    inference(cnf_transformation,[],[f29])).
% 3.70/0.87  fof(f29,plain,(
% 3.70/0.87    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 3.70/0.87    inference(flattening,[],[f28])).
% 3.70/0.87  fof(f28,plain,(
% 3.70/0.87    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 3.70/0.87    inference(ennf_transformation,[],[f3])).
% 3.70/0.87  fof(f3,axiom,(
% 3.70/0.87    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 3.70/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).
% 3.70/0.87  fof(f142,plain,(
% 3.70/0.87    spl14_6),
% 3.70/0.87    inference(avatar_split_clause,[],[f65,f140])).
% 3.70/0.87  fof(f65,plain,(
% 3.70/0.87    v1_relat_1(sK2)),
% 3.70/0.87    inference(cnf_transformation,[],[f33])).
% 3.70/0.87  fof(f33,plain,(
% 3.70/0.87    (~r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | ~r2_hidden(k4_tarski(sK0,sK1),sK2)) & (r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | r2_hidden(k4_tarski(sK0,sK1),sK2)) & r2_hidden(sK1,k3_relat_1(sK2)) & r2_hidden(sK0,k3_relat_1(sK2)) & v2_wellord1(sK2) & v1_relat_1(sK2)),
% 3.70/0.87    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f32])).
% 3.70/0.87  fof(f32,plain,(
% 3.70/0.87    ? [X0,X1,X2] : ((~r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | ~r2_hidden(k4_tarski(X0,X1),X2)) & (r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | r2_hidden(k4_tarski(X0,X1),X2)) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2)) => ((~r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | ~r2_hidden(k4_tarski(sK0,sK1),sK2)) & (r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | r2_hidden(k4_tarski(sK0,sK1),sK2)) & r2_hidden(sK1,k3_relat_1(sK2)) & r2_hidden(sK0,k3_relat_1(sK2)) & v2_wellord1(sK2) & v1_relat_1(sK2))),
% 3.70/0.87    introduced(choice_axiom,[])).
% 3.70/0.87  fof(f31,plain,(
% 3.70/0.87    ? [X0,X1,X2] : ((~r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | ~r2_hidden(k4_tarski(X0,X1),X2)) & (r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | r2_hidden(k4_tarski(X0,X1),X2)) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2))),
% 3.70/0.87    inference(flattening,[],[f30])).
% 3.70/0.87  fof(f30,plain,(
% 3.70/0.87    ? [X0,X1,X2] : (((~r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | ~r2_hidden(k4_tarski(X0,X1),X2)) & (r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | r2_hidden(k4_tarski(X0,X1),X2))) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2))),
% 3.70/0.87    inference(nnf_transformation,[],[f15])).
% 3.70/0.87  fof(f15,plain,(
% 3.70/0.87    ? [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2))),
% 3.70/0.87    inference(flattening,[],[f14])).
% 3.70/0.87  fof(f14,plain,(
% 3.70/0.87    ? [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) <~> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))) & (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2))) & v1_relat_1(X2))),
% 3.70/0.87    inference(ennf_transformation,[],[f13])).
% 3.70/0.87  fof(f13,negated_conjecture,(
% 3.70/0.87    ~! [X0,X1,X2] : (v1_relat_1(X2) => ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)))))),
% 3.70/0.87    inference(negated_conjecture,[],[f12])).
% 3.70/0.87  fof(f12,conjecture,(
% 3.70/0.87    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)))))),
% 3.70/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_wellord1)).
% 3.70/0.87  fof(f138,plain,(
% 3.70/0.87    spl14_5),
% 3.70/0.87    inference(avatar_split_clause,[],[f66,f136])).
% 3.70/0.87  fof(f66,plain,(
% 3.70/0.87    v2_wellord1(sK2)),
% 3.70/0.87    inference(cnf_transformation,[],[f33])).
% 3.70/0.87  fof(f134,plain,(
% 3.70/0.87    spl14_4),
% 3.70/0.87    inference(avatar_split_clause,[],[f67,f132])).
% 3.70/0.87  fof(f67,plain,(
% 3.70/0.87    r2_hidden(sK0,k3_relat_1(sK2))),
% 3.70/0.87    inference(cnf_transformation,[],[f33])).
% 3.70/0.87  fof(f130,plain,(
% 3.70/0.87    spl14_3),
% 3.70/0.87    inference(avatar_split_clause,[],[f68,f128])).
% 3.70/0.87  fof(f68,plain,(
% 3.70/0.87    r2_hidden(sK1,k3_relat_1(sK2))),
% 3.70/0.87    inference(cnf_transformation,[],[f33])).
% 3.70/0.87  fof(f126,plain,(
% 3.70/0.87    spl14_1 | spl14_2),
% 3.70/0.87    inference(avatar_split_clause,[],[f69,f121,f118])).
% 3.70/0.87  fof(f69,plain,(
% 3.70/0.87    r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 3.70/0.87    inference(cnf_transformation,[],[f33])).
% 3.70/0.87  fof(f123,plain,(
% 3.70/0.87    ~spl14_1 | ~spl14_2),
% 3.70/0.87    inference(avatar_split_clause,[],[f70,f121,f118])).
% 3.70/0.87  fof(f70,plain,(
% 3.70/0.87    ~r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | ~r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 3.70/0.87    inference(cnf_transformation,[],[f33])).
% 3.70/0.87  % SZS output end Proof for theBenchmark
% 3.70/0.87  % (30011)------------------------------
% 3.70/0.87  % (30011)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.70/0.87  % (30011)Termination reason: Refutation
% 3.70/0.87  
% 3.70/0.87  % (30011)Memory used [KB]: 14072
% 3.70/0.87  % (30011)Time elapsed: 0.441 s
% 3.70/0.87  % (30011)------------------------------
% 3.70/0.87  % (30011)------------------------------
% 3.70/0.87  % (29987)Success in time 0.507 s
%------------------------------------------------------------------------------
