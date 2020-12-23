%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:03 EST 2020

% Result     : Theorem 2.07s
% Output     : Refutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :  186 ( 429 expanded)
%              Number of leaves         :   42 ( 169 expanded)
%              Depth                    :   13
%              Number of atoms          :  796 (1969 expanded)
%              Number of equality atoms :   95 ( 319 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1045,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f101,f105,f109,f115,f120,f133,f252,f265,f312,f329,f416,f428,f571,f578,f598,f618,f742,f760,f763,f774,f825,f842,f845,f898,f957,f988,f1036])).

fof(f1036,plain,
    ( ~ spl12_29
    | spl12_41
    | spl12_42
    | ~ spl12_12
    | ~ spl12_28
    | ~ spl12_61 ),
    inference(avatar_split_clause,[],[f1028,f896,f569,f250,f714,f711,f573])).

fof(f573,plain,
    ( spl12_29
  <=> r2_hidden(sK1,k3_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_29])])).

fof(f711,plain,
    ( spl12_41
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_41])])).

fof(f714,plain,
    ( spl12_42
  <=> r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_42])])).

fof(f250,plain,
    ( spl12_12
  <=> ! [X1,X0] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | X0 = X1
        | ~ r2_hidden(k4_tarski(X1,X0),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_12])])).

fof(f569,plain,
    ( spl12_28
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k3_relat_1(sK2))
        | r2_hidden(k4_tarski(X0,sK0),sK2)
        | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),X0),sK2)
        | sK0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_28])])).

fof(f896,plain,
    ( spl12_61
  <=> r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_61])])).

fof(f1028,plain,
    ( r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),sK1),sK2)
    | sK0 = sK1
    | ~ r2_hidden(sK1,k3_relat_1(sK2))
    | ~ spl12_12
    | ~ spl12_28
    | ~ spl12_61 ),
    inference(resolution,[],[f987,f642])).

fof(f642,plain,
    ( ! [X6] :
        ( ~ r2_hidden(k4_tarski(sK0,X6),sK2)
        | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),X6),sK2)
        | sK0 = X6
        | ~ r2_hidden(X6,k3_relat_1(sK2)) )
    | ~ spl12_12
    | ~ spl12_28 ),
    inference(duplicate_literal_removal,[],[f635])).

fof(f635,plain,
    ( ! [X6] :
        ( ~ r2_hidden(X6,k3_relat_1(sK2))
        | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),X6),sK2)
        | sK0 = X6
        | sK0 = X6
        | ~ r2_hidden(k4_tarski(sK0,X6),sK2) )
    | ~ spl12_12
    | ~ spl12_28 ),
    inference(resolution,[],[f570,f251])).

fof(f251,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | X0 = X1
        | ~ r2_hidden(k4_tarski(X1,X0),sK2) )
    | ~ spl12_12 ),
    inference(avatar_component_clause,[],[f250])).

fof(f570,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,sK0),sK2)
        | ~ r2_hidden(X0,k3_relat_1(sK2))
        | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),X0),sK2)
        | sK0 = X0 )
    | ~ spl12_28 ),
    inference(avatar_component_clause,[],[f569])).

fof(f987,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl12_61 ),
    inference(avatar_component_clause,[],[f896])).

fof(f988,plain,
    ( spl12_5
    | spl12_61
    | ~ spl12_3
    | ~ spl12_46 ),
    inference(avatar_split_clause,[],[f976,f736,f107,f896,f118])).

fof(f118,plain,
    ( spl12_5
  <=> r1_tarski(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_5])])).

fof(f107,plain,
    ( spl12_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f736,plain,
    ( spl12_46
  <=> sK0 = sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_46])])).

fof(f976,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | r1_tarski(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0))
    | ~ spl12_3
    | ~ spl12_46 ),
    inference(superposition,[],[f126,f737])).

fof(f737,plain,
    ( sK0 = sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0))
    | ~ spl12_46 ),
    inference(avatar_component_clause,[],[f736])).

fof(f126,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,X0),X1),X0),sK2)
        | r1_tarski(k1_wellord1(sK2,X0),X1) )
    | ~ spl12_3 ),
    inference(resolution,[],[f125,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK11(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK11(X0,X1),X1)
          & r2_hidden(sK11(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f50,f51])).

fof(f51,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK11(X0,X1),X1)
        & r2_hidden(sK11(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f125,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_wellord1(sK2,X1))
        | r2_hidden(k4_tarski(X0,X1),sK2) )
    | ~ spl12_3 ),
    inference(resolution,[],[f93,f108])).

fof(f108,plain,
    ( v1_relat_1(sK2)
    | ~ spl12_3 ),
    inference(avatar_component_clause,[],[f107])).

fof(f93,plain,(
    ! [X4,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X4,k1_wellord1(X0,X1))
      | r2_hidden(k4_tarski(X4,X1),X0) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k4_tarski(X4,X1),X0)
      | ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ( ( ~ r2_hidden(k4_tarski(sK10(X0,X1,X2),X1),X0)
                | sK10(X0,X1,X2) = X1
                | ~ r2_hidden(sK10(X0,X1,X2),X2) )
              & ( ( r2_hidden(k4_tarski(sK10(X0,X1,X2),X1),X0)
                  & sK10(X0,X1,X2) != X1 )
                | r2_hidden(sK10(X0,X1,X2),X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f44,f45])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
            | X1 = X3
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k4_tarski(X3,X1),X0)
              & X1 != X3 )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK10(X0,X1,X2),X1),X0)
          | sK10(X0,X1,X2) = X1
          | ~ r2_hidden(sK10(X0,X1,X2),X2) )
        & ( ( r2_hidden(k4_tarski(sK10(X0,X1,X2),X1),X0)
            & sK10(X0,X1,X2) != X1 )
          | r2_hidden(sK10(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).

fof(f957,plain,
    ( spl12_41
    | spl12_40
    | ~ spl12_27
    | ~ spl12_30
    | spl12_61 ),
    inference(avatar_split_clause,[],[f953,f896,f576,f566,f708,f711])).

fof(f708,plain,
    ( spl12_40
  <=> r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)),sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_40])])).

fof(f566,plain,
    ( spl12_27
  <=> r2_hidden(sK0,k3_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_27])])).

fof(f576,plain,
    ( spl12_30
  <=> ! [X1] :
        ( ~ r2_hidden(X1,k3_relat_1(sK2))
        | r2_hidden(k4_tarski(X1,sK1),sK2)
        | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)),X1),sK2)
        | sK1 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_30])])).

fof(f953,plain,
    ( ~ r2_hidden(sK0,k3_relat_1(sK2))
    | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)),sK0),sK2)
    | sK0 = sK1
    | ~ spl12_30
    | spl12_61 ),
    inference(resolution,[],[f897,f577])).

fof(f577,plain,
    ( ! [X1] :
        ( r2_hidden(k4_tarski(X1,sK1),sK2)
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)),X1),sK2)
        | sK1 = X1 )
    | ~ spl12_30 ),
    inference(avatar_component_clause,[],[f576])).

fof(f897,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),sK2)
    | spl12_61 ),
    inference(avatar_component_clause,[],[f896])).

fof(f898,plain,
    ( spl12_4
    | spl12_41
    | ~ spl12_61
    | ~ spl12_3
    | ~ spl12_12
    | ~ spl12_54 ),
    inference(avatar_split_clause,[],[f878,f794,f250,f107,f896,f711,f113])).

fof(f113,plain,
    ( spl12_4
  <=> r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).

fof(f794,plain,
    ( spl12_54
  <=> sK1 = sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_54])])).

fof(f878,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),sK2)
    | sK0 = sK1
    | r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ spl12_3
    | ~ spl12_12
    | ~ spl12_54 ),
    inference(superposition,[],[f266,f795])).

fof(f795,plain,
    ( sK1 = sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ spl12_54 ),
    inference(avatar_component_clause,[],[f794])).

fof(f266,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,sK11(k1_wellord1(sK2,X0),X1)),sK2)
        | sK11(k1_wellord1(sK2,X0),X1) = X0
        | r1_tarski(k1_wellord1(sK2,X0),X1) )
    | ~ spl12_3
    | ~ spl12_12 ),
    inference(resolution,[],[f251,f126])).

fof(f845,plain,
    ( spl12_55
    | spl12_54
    | ~ spl12_3
    | ~ spl12_42 ),
    inference(avatar_split_clause,[],[f833,f714,f107,f794,f798])).

fof(f798,plain,
    ( spl12_55
  <=> r2_hidden(sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_55])])).

fof(f833,plain,
    ( sK1 = sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | r2_hidden(sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK1))
    | ~ spl12_3
    | ~ spl12_42 ),
    inference(resolution,[],[f715,f164])).

fof(f164,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | X0 = X1
        | r2_hidden(X0,k1_wellord1(sK2,X1)) )
    | ~ spl12_3 ),
    inference(resolution,[],[f92,f108])).

fof(f92,plain,(
    ! [X4,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | r2_hidden(X4,k1_wellord1(X0,X1)) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f715,plain,
    ( r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),sK1),sK2)
    | ~ spl12_42 ),
    inference(avatar_component_clause,[],[f714])).

fof(f842,plain,
    ( spl12_4
    | ~ spl12_55 ),
    inference(avatar_split_clause,[],[f838,f798,f113])).

fof(f838,plain,
    ( r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ spl12_55 ),
    inference(resolution,[],[f799,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK11(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f799,plain,
    ( r2_hidden(sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK1))
    | ~ spl12_55 ),
    inference(avatar_component_clause,[],[f798])).

fof(f825,plain,
    ( spl12_5
    | ~ spl12_47 ),
    inference(avatar_split_clause,[],[f821,f740,f118])).

fof(f740,plain,
    ( spl12_47
  <=> r2_hidden(sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)),k1_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_47])])).

fof(f821,plain,
    ( r1_tarski(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0))
    | ~ spl12_47 ),
    inference(resolution,[],[f741,f87])).

fof(f741,plain,
    ( r2_hidden(sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)),k1_wellord1(sK2,sK0))
    | ~ spl12_47 ),
    inference(avatar_component_clause,[],[f740])).

fof(f774,plain,
    ( ~ spl12_49
    | spl12_50 ),
    inference(avatar_split_clause,[],[f772,f758,f753])).

fof(f753,plain,
    ( spl12_49
  <=> r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_49])])).

fof(f758,plain,
    ( spl12_50
  <=> r3_xboole_0(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_50])])).

fof(f772,plain,
    ( ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0))
    | spl12_50 ),
    inference(resolution,[],[f759,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
      | ( ~ r1_tarski(X1,X0)
        & ~ r1_tarski(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1) )
     => r3_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
    <=> ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_xboole_0)).

fof(f759,plain,
    ( ~ r3_xboole_0(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0))
    | spl12_50 ),
    inference(avatar_component_clause,[],[f758])).

fof(f763,plain,(
    spl12_49 ),
    inference(avatar_contradiction_clause,[],[f762])).

fof(f762,plain,
    ( $false
    | spl12_49 ),
    inference(resolution,[],[f754,f96])).

fof(f96,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f754,plain,
    ( ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0))
    | spl12_49 ),
    inference(avatar_component_clause,[],[f753])).

fof(f760,plain,
    ( ~ spl12_50
    | spl12_1
    | ~ spl12_41 ),
    inference(avatar_split_clause,[],[f751,f711,f99,f758])).

fof(f99,plain,
    ( spl12_1
  <=> r3_xboole_0(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f751,plain,
    ( ~ r3_xboole_0(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0))
    | spl12_1
    | ~ spl12_41 ),
    inference(superposition,[],[f100,f712])).

fof(f712,plain,
    ( sK0 = sK1
    | ~ spl12_41 ),
    inference(avatar_component_clause,[],[f711])).

fof(f100,plain,
    ( ~ r3_xboole_0(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | spl12_1 ),
    inference(avatar_component_clause,[],[f99])).

fof(f742,plain,
    ( spl12_47
    | spl12_46
    | ~ spl12_3
    | ~ spl12_40 ),
    inference(avatar_split_clause,[],[f721,f708,f107,f736,f740])).

fof(f721,plain,
    ( sK0 = sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0))
    | r2_hidden(sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)),k1_wellord1(sK2,sK0))
    | ~ spl12_3
    | ~ spl12_40 ),
    inference(resolution,[],[f709,f164])).

fof(f709,plain,
    ( r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)),sK0),sK2)
    | ~ spl12_40 ),
    inference(avatar_component_clause,[],[f708])).

fof(f618,plain,
    ( spl12_5
    | ~ spl12_6
    | spl12_29 ),
    inference(avatar_contradiction_clause,[],[f617])).

fof(f617,plain,
    ( $false
    | spl12_5
    | ~ spl12_6
    | spl12_29 ),
    inference(subsumption_resolution,[],[f119,f599])).

fof(f599,plain,
    ( ! [X0] : r1_tarski(k1_wellord1(sK2,sK1),X0)
    | ~ spl12_6
    | spl12_29 ),
    inference(resolution,[],[f574,f132])).

fof(f132,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,k3_relat_1(sK2))
        | r1_tarski(k1_wellord1(sK2,X0),X1) )
    | ~ spl12_6 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl12_6
  <=> ! [X1,X0] :
        ( r1_tarski(k1_wellord1(sK2,X0),X1)
        | r2_hidden(X0,k3_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).

fof(f574,plain,
    ( ~ r2_hidden(sK1,k3_relat_1(sK2))
    | spl12_29 ),
    inference(avatar_component_clause,[],[f573])).

fof(f119,plain,
    ( ~ r1_tarski(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0))
    | spl12_5 ),
    inference(avatar_component_clause,[],[f118])).

fof(f598,plain,
    ( spl12_4
    | ~ spl12_6
    | spl12_27 ),
    inference(avatar_contradiction_clause,[],[f597])).

fof(f597,plain,
    ( $false
    | spl12_4
    | ~ spl12_6
    | spl12_27 ),
    inference(subsumption_resolution,[],[f114,f579])).

fof(f579,plain,
    ( ! [X0] : r1_tarski(k1_wellord1(sK2,sK0),X0)
    | ~ spl12_6
    | spl12_27 ),
    inference(resolution,[],[f567,f132])).

fof(f567,plain,
    ( ~ r2_hidden(sK0,k3_relat_1(sK2))
    | spl12_27 ),
    inference(avatar_component_clause,[],[f566])).

fof(f114,plain,
    ( ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | spl12_4 ),
    inference(avatar_component_clause,[],[f113])).

fof(f578,plain,
    ( ~ spl12_29
    | spl12_30
    | ~ spl12_3
    | spl12_5
    | ~ spl12_16
    | ~ spl12_24 ),
    inference(avatar_split_clause,[],[f560,f414,f310,f118,f107,f576,f573])).

fof(f310,plain,
    ( spl12_16
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | r2_hidden(k4_tarski(X2,X1),sK2)
        | ~ r2_hidden(k4_tarski(X2,X0),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_16])])).

fof(f414,plain,
    ( spl12_24
  <=> ! [X1,X0] :
        ( r2_hidden(k4_tarski(X0,X1),sK2)
        | r2_hidden(k4_tarski(X1,X0),sK2)
        | ~ r2_hidden(X0,k3_relat_1(sK2))
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | X0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_24])])).

fof(f560,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k3_relat_1(sK2))
        | sK1 = X1
        | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)),X1),sK2)
        | r2_hidden(k4_tarski(X1,sK1),sK2)
        | ~ r2_hidden(sK1,k3_relat_1(sK2)) )
    | ~ spl12_3
    | spl12_5
    | ~ spl12_16
    | ~ spl12_24 ),
    inference(resolution,[],[f463,f119])).

fof(f463,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k1_wellord1(sK2,X0),X2)
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | X0 = X1
        | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,X0),X2),X1),sK2)
        | r2_hidden(k4_tarski(X1,X0),sK2)
        | ~ r2_hidden(X0,k3_relat_1(sK2)) )
    | ~ spl12_3
    | ~ spl12_16
    | ~ spl12_24 ),
    inference(resolution,[],[f429,f126])).

fof(f429,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(k4_tarski(X2,X1),sK2)
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | ~ r2_hidden(X0,k3_relat_1(sK2))
        | X0 = X1
        | r2_hidden(k4_tarski(X2,X0),sK2)
        | r2_hidden(k4_tarski(X0,X1),sK2) )
    | ~ spl12_16
    | ~ spl12_24 ),
    inference(resolution,[],[f415,f311])).

fof(f311,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | r2_hidden(k4_tarski(X2,X1),sK2)
        | ~ r2_hidden(k4_tarski(X2,X0),sK2) )
    | ~ spl12_16 ),
    inference(avatar_component_clause,[],[f310])).

fof(f415,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,X1),sK2)
        | r2_hidden(k4_tarski(X1,X0),sK2)
        | ~ r2_hidden(X0,k3_relat_1(sK2))
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | X0 = X1 )
    | ~ spl12_24 ),
    inference(avatar_component_clause,[],[f414])).

fof(f571,plain,
    ( ~ spl12_27
    | spl12_28
    | ~ spl12_3
    | spl12_4
    | ~ spl12_16
    | ~ spl12_24 ),
    inference(avatar_split_clause,[],[f559,f414,f310,f113,f107,f569,f566])).

fof(f559,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k3_relat_1(sK2))
        | sK0 = X0
        | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),X0),sK2)
        | r2_hidden(k4_tarski(X0,sK0),sK2)
        | ~ r2_hidden(sK0,k3_relat_1(sK2)) )
    | ~ spl12_3
    | spl12_4
    | ~ spl12_16
    | ~ spl12_24 ),
    inference(resolution,[],[f463,f114])).

fof(f428,plain,
    ( ~ spl12_3
    | ~ spl12_2
    | spl12_23 ),
    inference(avatar_split_clause,[],[f419,f411,f103,f107])).

fof(f103,plain,
    ( spl12_2
  <=> v2_wellord1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f411,plain,
    ( spl12_23
  <=> v6_relat_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_23])])).

fof(f419,plain,
    ( ~ v2_wellord1(sK2)
    | ~ v1_relat_1(sK2)
    | spl12_23 ),
    inference(resolution,[],[f412,f73])).

fof(f73,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_wellord1)).

fof(f412,plain,
    ( ~ v6_relat_2(sK2)
    | spl12_23 ),
    inference(avatar_component_clause,[],[f411])).

fof(f416,plain,
    ( ~ spl12_23
    | spl12_24
    | ~ spl12_3 ),
    inference(avatar_split_clause,[],[f409,f107,f414,f411])).

fof(f409,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,X1),sK2)
        | X0 = X1
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | ~ r2_hidden(X0,k3_relat_1(sK2))
        | ~ v6_relat_2(sK2)
        | r2_hidden(k4_tarski(X1,X0),sK2) )
    | ~ spl12_3 ),
    inference(resolution,[],[f60,f108])).

fof(f60,plain,(
    ! [X4,X0,X3] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X3,X4),X0)
      | X3 = X4
      | ~ r2_hidden(X4,k3_relat_1(X0))
      | ~ r2_hidden(X3,k3_relat_1(X0))
      | ~ v6_relat_2(X0)
      | r2_hidden(k4_tarski(X4,X3),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ( ~ r2_hidden(k4_tarski(sK6(X0),sK5(X0)),X0)
            & ~ r2_hidden(k4_tarski(sK5(X0),sK6(X0)),X0)
            & sK5(X0) != sK6(X0)
            & r2_hidden(sK6(X0),k3_relat_1(X0))
            & r2_hidden(sK5(X0),k3_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( r2_hidden(k4_tarski(X4,X3),X0)
              | r2_hidden(k4_tarski(X3,X4),X0)
              | X3 = X4
              | ~ r2_hidden(X4,k3_relat_1(X0))
              | ~ r2_hidden(X3,k3_relat_1(X0)) )
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f33,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ~ r2_hidden(k4_tarski(X2,X1),X0)
          & ~ r2_hidden(k4_tarski(X1,X2),X0)
          & X1 != X2
          & r2_hidden(X2,k3_relat_1(X0))
          & r2_hidden(X1,k3_relat_1(X0)) )
     => ( ~ r2_hidden(k4_tarski(sK6(X0),sK5(X0)),X0)
        & ~ r2_hidden(k4_tarski(sK5(X0),sK6(X0)),X0)
        & sK5(X0) != sK6(X0)
        & r2_hidden(sK6(X0),k3_relat_1(X0))
        & r2_hidden(sK5(X0),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l4_wellord1)).

fof(f329,plain,
    ( ~ spl12_3
    | ~ spl12_2
    | spl12_15 ),
    inference(avatar_split_clause,[],[f316,f307,f103,f107])).

fof(f307,plain,
    ( spl12_15
  <=> v8_relat_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_15])])).

fof(f316,plain,
    ( ~ v2_wellord1(sK2)
    | ~ v1_relat_1(sK2)
    | spl12_15 ),
    inference(resolution,[],[f308,f71])).

fof(f71,plain,(
    ! [X0] :
      ( v8_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f308,plain,
    ( ~ v8_relat_2(sK2)
    | spl12_15 ),
    inference(avatar_component_clause,[],[f307])).

fof(f312,plain,
    ( ~ spl12_15
    | spl12_16
    | ~ spl12_3 ),
    inference(avatar_split_clause,[],[f305,f107,f310,f307])).

fof(f305,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | ~ r2_hidden(k4_tarski(X2,X0),sK2)
        | ~ v8_relat_2(sK2)
        | r2_hidden(k4_tarski(X2,X1),sK2) )
    | ~ spl12_3 ),
    inference(resolution,[],[f66,f108])).

fof(f66,plain,(
    ! [X6,X4,X0,X5] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X4,X5),X0)
      | ~ v8_relat_2(X0)
      | r2_hidden(k4_tarski(X4,X6),X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( ( v8_relat_2(X0)
          | ( ~ r2_hidden(k4_tarski(sK7(X0),sK9(X0)),X0)
            & r2_hidden(k4_tarski(sK8(X0),sK9(X0)),X0)
            & r2_hidden(k4_tarski(sK7(X0),sK8(X0)),X0) ) )
        & ( ! [X4,X5,X6] :
              ( r2_hidden(k4_tarski(X4,X6),X0)
              | ~ r2_hidden(k4_tarski(X5,X6),X0)
              | ~ r2_hidden(k4_tarski(X4,X5),X0) )
          | ~ v8_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f37,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1,X2,X3] :
          ( ~ r2_hidden(k4_tarski(X1,X3),X0)
          & r2_hidden(k4_tarski(X2,X3),X0)
          & r2_hidden(k4_tarski(X1,X2),X0) )
     => ( ~ r2_hidden(k4_tarski(sK7(X0),sK9(X0)),X0)
        & r2_hidden(k4_tarski(sK8(X0),sK9(X0)),X0)
        & r2_hidden(k4_tarski(sK7(X0),sK8(X0)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v8_relat_2(X0)
      <=> ! [X1,X2,X3] :
            ( r2_hidden(k4_tarski(X1,X3),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l2_wellord1)).

fof(f265,plain,
    ( ~ spl12_3
    | ~ spl12_2
    | spl12_11 ),
    inference(avatar_split_clause,[],[f255,f247,f103,f107])).

fof(f247,plain,
    ( spl12_11
  <=> v4_relat_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_11])])).

fof(f255,plain,
    ( ~ v2_wellord1(sK2)
    | ~ v1_relat_1(sK2)
    | spl12_11 ),
    inference(resolution,[],[f248,f72])).

fof(f72,plain,(
    ! [X0] :
      ( v4_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f248,plain,
    ( ~ v4_relat_2(sK2)
    | spl12_11 ),
    inference(avatar_component_clause,[],[f247])).

fof(f252,plain,
    ( ~ spl12_11
    | spl12_12
    | ~ spl12_3 ),
    inference(avatar_split_clause,[],[f245,f107,f250,f247])).

fof(f245,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | ~ r2_hidden(k4_tarski(X1,X0),sK2)
        | ~ v4_relat_2(sK2)
        | X0 = X1 )
    | ~ spl12_3 ),
    inference(resolution,[],[f56,f108])).

fof(f56,plain,(
    ! [X4,X0,X3] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X4,X3),X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ v4_relat_2(X0)
      | X3 = X4 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( ( v4_relat_2(X0)
          | ( sK3(X0) != sK4(X0)
            & r2_hidden(k4_tarski(sK4(X0),sK3(X0)),X0)
            & r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | ~ r2_hidden(k4_tarski(X4,X3),X0)
              | ~ r2_hidden(k4_tarski(X3,X4),X0) )
          | ~ v4_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f29,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & r2_hidden(k4_tarski(X2,X1),X0)
          & r2_hidden(k4_tarski(X1,X2),X0) )
     => ( sK3(X0) != sK4(X0)
        & r2_hidden(k4_tarski(sK4(X0),sK3(X0)),X0)
        & r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v4_relat_2(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | ~ r2_hidden(k4_tarski(X2,X1),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_wellord1)).

fof(f133,plain,
    ( ~ spl12_3
    | spl12_6
    | ~ spl12_3 ),
    inference(avatar_split_clause,[],[f127,f107,f131,f107])).

fof(f127,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_wellord1(sK2,X0),X1)
        | r2_hidden(X0,k3_relat_1(sK2))
        | ~ v1_relat_1(sK2) )
    | ~ spl12_3 ),
    inference(resolution,[],[f126,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k3_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).

fof(f120,plain,
    ( ~ spl12_5
    | spl12_1 ),
    inference(avatar_split_clause,[],[f116,f99,f118])).

fof(f116,plain,
    ( ~ r1_tarski(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0))
    | spl12_1 ),
    inference(resolution,[],[f89,f100])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f115,plain,
    ( ~ spl12_4
    | spl12_1 ),
    inference(avatar_split_clause,[],[f111,f99,f113])).

fof(f111,plain,
    ( ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | spl12_1 ),
    inference(resolution,[],[f88,f100])).

fof(f109,plain,(
    spl12_3 ),
    inference(avatar_split_clause,[],[f53,f107])).

fof(f53,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ~ r3_xboole_0(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    & v2_wellord1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( ~ r3_xboole_0(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
        & v2_wellord1(X2)
        & v1_relat_1(X2) )
   => ( ~ r3_xboole_0(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
      & v2_wellord1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r3_xboole_0(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r3_xboole_0(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( v2_wellord1(X2)
         => r3_xboole_0(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( v2_wellord1(X2)
       => r3_xboole_0(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_wellord1)).

fof(f105,plain,(
    spl12_2 ),
    inference(avatar_split_clause,[],[f54,f103])).

fof(f54,plain,(
    v2_wellord1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f101,plain,(
    ~ spl12_1 ),
    inference(avatar_split_clause,[],[f55,f99])).

fof(f55,plain,(
    ~ r3_xboole_0(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:47:24 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (10438)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (10460)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (10452)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (10442)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (10443)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (10451)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (10436)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (10440)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (10444)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (10463)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (10437)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (10464)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (10438)Refutation not found, incomplete strategy% (10438)------------------------------
% 0.21/0.54  % (10438)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (10438)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (10438)Memory used [KB]: 10746
% 0.21/0.54  % (10438)Time elapsed: 0.124 s
% 0.21/0.54  % (10438)------------------------------
% 0.21/0.54  % (10438)------------------------------
% 0.21/0.54  % (10459)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (10466)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (10439)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (10441)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (10447)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (10465)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (10447)Refutation not found, incomplete strategy% (10447)------------------------------
% 0.21/0.54  % (10447)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (10447)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (10447)Memory used [KB]: 10618
% 0.21/0.54  % (10447)Time elapsed: 0.127 s
% 0.21/0.54  % (10447)------------------------------
% 0.21/0.54  % (10447)------------------------------
% 0.21/0.54  % (10459)Refutation not found, incomplete strategy% (10459)------------------------------
% 0.21/0.54  % (10459)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (10459)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (10459)Memory used [KB]: 10746
% 0.21/0.54  % (10459)Time elapsed: 0.128 s
% 0.21/0.54  % (10459)------------------------------
% 0.21/0.54  % (10459)------------------------------
% 0.21/0.54  % (10453)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (10448)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (10455)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (10456)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (10458)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (10449)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (10457)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (10450)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (10446)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (10462)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.57  % (10448)Refutation not found, incomplete strategy% (10448)------------------------------
% 0.21/0.57  % (10448)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (10461)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.57  % (10454)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.57  % (10454)Refutation not found, incomplete strategy% (10454)------------------------------
% 0.21/0.57  % (10454)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (10454)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (10454)Memory used [KB]: 10618
% 0.21/0.57  % (10454)Time elapsed: 0.156 s
% 0.21/0.57  % (10454)------------------------------
% 0.21/0.57  % (10454)------------------------------
% 0.21/0.57  % (10448)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (10448)Memory used [KB]: 10746
% 0.21/0.57  % (10448)Time elapsed: 0.158 s
% 0.21/0.57  % (10448)------------------------------
% 0.21/0.57  % (10448)------------------------------
% 2.07/0.65  % (10456)Refutation found. Thanks to Tanya!
% 2.07/0.65  % SZS status Theorem for theBenchmark
% 2.07/0.65  % SZS output start Proof for theBenchmark
% 2.07/0.65  fof(f1045,plain,(
% 2.07/0.65    $false),
% 2.07/0.65    inference(avatar_sat_refutation,[],[f101,f105,f109,f115,f120,f133,f252,f265,f312,f329,f416,f428,f571,f578,f598,f618,f742,f760,f763,f774,f825,f842,f845,f898,f957,f988,f1036])).
% 2.07/0.65  fof(f1036,plain,(
% 2.07/0.65    ~spl12_29 | spl12_41 | spl12_42 | ~spl12_12 | ~spl12_28 | ~spl12_61),
% 2.07/0.65    inference(avatar_split_clause,[],[f1028,f896,f569,f250,f714,f711,f573])).
% 2.07/0.65  fof(f573,plain,(
% 2.07/0.65    spl12_29 <=> r2_hidden(sK1,k3_relat_1(sK2))),
% 2.07/0.65    introduced(avatar_definition,[new_symbols(naming,[spl12_29])])).
% 2.07/0.65  fof(f711,plain,(
% 2.07/0.65    spl12_41 <=> sK0 = sK1),
% 2.07/0.65    introduced(avatar_definition,[new_symbols(naming,[spl12_41])])).
% 2.07/0.65  fof(f714,plain,(
% 2.07/0.65    spl12_42 <=> r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),sK1),sK2)),
% 2.07/0.65    introduced(avatar_definition,[new_symbols(naming,[spl12_42])])).
% 2.07/0.65  fof(f250,plain,(
% 2.07/0.65    spl12_12 <=> ! [X1,X0] : (~r2_hidden(k4_tarski(X0,X1),sK2) | X0 = X1 | ~r2_hidden(k4_tarski(X1,X0),sK2))),
% 2.07/0.65    introduced(avatar_definition,[new_symbols(naming,[spl12_12])])).
% 2.07/0.65  fof(f569,plain,(
% 2.07/0.65    spl12_28 <=> ! [X0] : (~r2_hidden(X0,k3_relat_1(sK2)) | r2_hidden(k4_tarski(X0,sK0),sK2) | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),X0),sK2) | sK0 = X0)),
% 2.07/0.65    introduced(avatar_definition,[new_symbols(naming,[spl12_28])])).
% 2.07/0.65  fof(f896,plain,(
% 2.07/0.65    spl12_61 <=> r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 2.07/0.65    introduced(avatar_definition,[new_symbols(naming,[spl12_61])])).
% 2.07/0.65  fof(f1028,plain,(
% 2.07/0.65    r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),sK1),sK2) | sK0 = sK1 | ~r2_hidden(sK1,k3_relat_1(sK2)) | (~spl12_12 | ~spl12_28 | ~spl12_61)),
% 2.07/0.65    inference(resolution,[],[f987,f642])).
% 2.07/0.65  fof(f642,plain,(
% 2.07/0.65    ( ! [X6] : (~r2_hidden(k4_tarski(sK0,X6),sK2) | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),X6),sK2) | sK0 = X6 | ~r2_hidden(X6,k3_relat_1(sK2))) ) | (~spl12_12 | ~spl12_28)),
% 2.07/0.65    inference(duplicate_literal_removal,[],[f635])).
% 2.07/0.65  fof(f635,plain,(
% 2.07/0.65    ( ! [X6] : (~r2_hidden(X6,k3_relat_1(sK2)) | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),X6),sK2) | sK0 = X6 | sK0 = X6 | ~r2_hidden(k4_tarski(sK0,X6),sK2)) ) | (~spl12_12 | ~spl12_28)),
% 2.07/0.65    inference(resolution,[],[f570,f251])).
% 2.07/0.65  fof(f251,plain,(
% 2.07/0.65    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | X0 = X1 | ~r2_hidden(k4_tarski(X1,X0),sK2)) ) | ~spl12_12),
% 2.07/0.65    inference(avatar_component_clause,[],[f250])).
% 2.07/0.65  fof(f570,plain,(
% 2.07/0.65    ( ! [X0] : (r2_hidden(k4_tarski(X0,sK0),sK2) | ~r2_hidden(X0,k3_relat_1(sK2)) | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),X0),sK2) | sK0 = X0) ) | ~spl12_28),
% 2.07/0.65    inference(avatar_component_clause,[],[f569])).
% 2.07/0.65  fof(f987,plain,(
% 2.07/0.65    r2_hidden(k4_tarski(sK0,sK1),sK2) | ~spl12_61),
% 2.07/0.65    inference(avatar_component_clause,[],[f896])).
% 2.07/0.65  fof(f988,plain,(
% 2.07/0.65    spl12_5 | spl12_61 | ~spl12_3 | ~spl12_46),
% 2.07/0.65    inference(avatar_split_clause,[],[f976,f736,f107,f896,f118])).
% 2.07/0.65  fof(f118,plain,(
% 2.07/0.65    spl12_5 <=> r1_tarski(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0))),
% 2.07/0.65    introduced(avatar_definition,[new_symbols(naming,[spl12_5])])).
% 2.07/0.65  fof(f107,plain,(
% 2.07/0.65    spl12_3 <=> v1_relat_1(sK2)),
% 2.07/0.65    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).
% 2.07/0.65  fof(f736,plain,(
% 2.07/0.65    spl12_46 <=> sK0 = sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0))),
% 2.07/0.65    introduced(avatar_definition,[new_symbols(naming,[spl12_46])])).
% 2.07/0.65  fof(f976,plain,(
% 2.07/0.65    r2_hidden(k4_tarski(sK0,sK1),sK2) | r1_tarski(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)) | (~spl12_3 | ~spl12_46)),
% 2.07/0.65    inference(superposition,[],[f126,f737])).
% 2.07/0.65  fof(f737,plain,(
% 2.07/0.65    sK0 = sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)) | ~spl12_46),
% 2.07/0.65    inference(avatar_component_clause,[],[f736])).
% 2.07/0.65  fof(f126,plain,(
% 2.07/0.65    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,X0),X1),X0),sK2) | r1_tarski(k1_wellord1(sK2,X0),X1)) ) | ~spl12_3),
% 2.07/0.65    inference(resolution,[],[f125,f86])).
% 2.07/0.65  fof(f86,plain,(
% 2.07/0.65    ( ! [X0,X1] : (r2_hidden(sK11(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.07/0.65    inference(cnf_transformation,[],[f52])).
% 2.07/0.65  fof(f52,plain,(
% 2.07/0.65    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK11(X0,X1),X1) & r2_hidden(sK11(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.07/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f50,f51])).
% 2.07/0.65  fof(f51,plain,(
% 2.07/0.65    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK11(X0,X1),X1) & r2_hidden(sK11(X0,X1),X0)))),
% 2.07/0.65    introduced(choice_axiom,[])).
% 2.07/0.65  fof(f50,plain,(
% 2.07/0.65    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.07/0.65    inference(rectify,[],[f49])).
% 2.07/0.65  fof(f49,plain,(
% 2.07/0.65    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.07/0.65    inference(nnf_transformation,[],[f22])).
% 2.07/0.65  fof(f22,plain,(
% 2.07/0.65    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.07/0.65    inference(ennf_transformation,[],[f1])).
% 2.07/0.65  fof(f1,axiom,(
% 2.07/0.65    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.07/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.07/0.65  fof(f125,plain,(
% 2.07/0.65    ( ! [X0,X1] : (~r2_hidden(X0,k1_wellord1(sK2,X1)) | r2_hidden(k4_tarski(X0,X1),sK2)) ) | ~spl12_3),
% 2.07/0.65    inference(resolution,[],[f93,f108])).
% 2.07/0.65  fof(f108,plain,(
% 2.07/0.65    v1_relat_1(sK2) | ~spl12_3),
% 2.07/0.65    inference(avatar_component_clause,[],[f107])).
% 2.07/0.65  fof(f93,plain,(
% 2.07/0.65    ( ! [X4,X0,X1] : (~v1_relat_1(X0) | ~r2_hidden(X4,k1_wellord1(X0,X1)) | r2_hidden(k4_tarski(X4,X1),X0)) )),
% 2.07/0.65    inference(equality_resolution,[],[f77])).
% 2.07/0.65  fof(f77,plain,(
% 2.07/0.65    ( ! [X4,X2,X0,X1] : (r2_hidden(k4_tarski(X4,X1),X0) | ~r2_hidden(X4,X2) | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 2.07/0.65    inference(cnf_transformation,[],[f46])).
% 2.07/0.65  fof(f46,plain,(
% 2.07/0.65    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK10(X0,X1,X2),X1),X0) | sK10(X0,X1,X2) = X1 | ~r2_hidden(sK10(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK10(X0,X1,X2),X1),X0) & sK10(X0,X1,X2) != X1) | r2_hidden(sK10(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 2.07/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f44,f45])).
% 2.07/0.65  fof(f45,plain,(
% 2.07/0.65    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2))) => ((~r2_hidden(k4_tarski(sK10(X0,X1,X2),X1),X0) | sK10(X0,X1,X2) = X1 | ~r2_hidden(sK10(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK10(X0,X1,X2),X1),X0) & sK10(X0,X1,X2) != X1) | r2_hidden(sK10(X0,X1,X2),X2))))),
% 2.07/0.65    introduced(choice_axiom,[])).
% 2.07/0.65  fof(f44,plain,(
% 2.07/0.65    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 2.07/0.65    inference(rectify,[],[f43])).
% 2.07/0.65  fof(f43,plain,(
% 2.07/0.65    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 2.07/0.65    inference(flattening,[],[f42])).
% 2.07/0.65  fof(f42,plain,(
% 2.07/0.65    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 2.07/0.65    inference(nnf_transformation,[],[f21])).
% 2.07/0.65  fof(f21,plain,(
% 2.07/0.65    ! [X0] : (! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))) | ~v1_relat_1(X0))),
% 2.07/0.65    inference(ennf_transformation,[],[f5])).
% 2.07/0.65  fof(f5,axiom,(
% 2.07/0.65    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))))),
% 2.07/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).
% 2.07/0.65  fof(f957,plain,(
% 2.07/0.65    spl12_41 | spl12_40 | ~spl12_27 | ~spl12_30 | spl12_61),
% 2.07/0.65    inference(avatar_split_clause,[],[f953,f896,f576,f566,f708,f711])).
% 2.07/0.65  fof(f708,plain,(
% 2.07/0.65    spl12_40 <=> r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)),sK0),sK2)),
% 2.07/0.65    introduced(avatar_definition,[new_symbols(naming,[spl12_40])])).
% 2.07/0.65  fof(f566,plain,(
% 2.07/0.65    spl12_27 <=> r2_hidden(sK0,k3_relat_1(sK2))),
% 2.07/0.65    introduced(avatar_definition,[new_symbols(naming,[spl12_27])])).
% 2.07/0.65  fof(f576,plain,(
% 2.07/0.65    spl12_30 <=> ! [X1] : (~r2_hidden(X1,k3_relat_1(sK2)) | r2_hidden(k4_tarski(X1,sK1),sK2) | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)),X1),sK2) | sK1 = X1)),
% 2.07/0.65    introduced(avatar_definition,[new_symbols(naming,[spl12_30])])).
% 2.07/0.65  fof(f953,plain,(
% 2.07/0.65    ~r2_hidden(sK0,k3_relat_1(sK2)) | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)),sK0),sK2) | sK0 = sK1 | (~spl12_30 | spl12_61)),
% 2.07/0.65    inference(resolution,[],[f897,f577])).
% 2.07/0.65  fof(f577,plain,(
% 2.07/0.65    ( ! [X1] : (r2_hidden(k4_tarski(X1,sK1),sK2) | ~r2_hidden(X1,k3_relat_1(sK2)) | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)),X1),sK2) | sK1 = X1) ) | ~spl12_30),
% 2.07/0.65    inference(avatar_component_clause,[],[f576])).
% 2.07/0.65  fof(f897,plain,(
% 2.07/0.65    ~r2_hidden(k4_tarski(sK0,sK1),sK2) | spl12_61),
% 2.07/0.65    inference(avatar_component_clause,[],[f896])).
% 2.07/0.65  fof(f898,plain,(
% 2.07/0.65    spl12_4 | spl12_41 | ~spl12_61 | ~spl12_3 | ~spl12_12 | ~spl12_54),
% 2.07/0.65    inference(avatar_split_clause,[],[f878,f794,f250,f107,f896,f711,f113])).
% 2.07/0.65  fof(f113,plain,(
% 2.07/0.65    spl12_4 <=> r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))),
% 2.07/0.65    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).
% 2.07/0.65  fof(f794,plain,(
% 2.07/0.65    spl12_54 <=> sK1 = sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))),
% 2.07/0.65    introduced(avatar_definition,[new_symbols(naming,[spl12_54])])).
% 2.07/0.65  fof(f878,plain,(
% 2.07/0.65    ~r2_hidden(k4_tarski(sK0,sK1),sK2) | sK0 = sK1 | r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | (~spl12_3 | ~spl12_12 | ~spl12_54)),
% 2.07/0.65    inference(superposition,[],[f266,f795])).
% 2.07/0.65  fof(f795,plain,(
% 2.07/0.65    sK1 = sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | ~spl12_54),
% 2.07/0.65    inference(avatar_component_clause,[],[f794])).
% 2.07/0.65  fof(f266,plain,(
% 2.07/0.65    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,sK11(k1_wellord1(sK2,X0),X1)),sK2) | sK11(k1_wellord1(sK2,X0),X1) = X0 | r1_tarski(k1_wellord1(sK2,X0),X1)) ) | (~spl12_3 | ~spl12_12)),
% 2.07/0.65    inference(resolution,[],[f251,f126])).
% 2.07/0.65  fof(f845,plain,(
% 2.07/0.65    spl12_55 | spl12_54 | ~spl12_3 | ~spl12_42),
% 2.07/0.65    inference(avatar_split_clause,[],[f833,f714,f107,f794,f798])).
% 2.07/0.65  fof(f798,plain,(
% 2.07/0.65    spl12_55 <=> r2_hidden(sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK1))),
% 2.07/0.65    introduced(avatar_definition,[new_symbols(naming,[spl12_55])])).
% 2.07/0.65  fof(f833,plain,(
% 2.07/0.65    sK1 = sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | r2_hidden(sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK1)) | (~spl12_3 | ~spl12_42)),
% 2.07/0.65    inference(resolution,[],[f715,f164])).
% 2.07/0.65  fof(f164,plain,(
% 2.07/0.65    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | X0 = X1 | r2_hidden(X0,k1_wellord1(sK2,X1))) ) | ~spl12_3),
% 2.07/0.65    inference(resolution,[],[f92,f108])).
% 2.07/0.65  fof(f92,plain,(
% 2.07/0.65    ( ! [X4,X0,X1] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4 | r2_hidden(X4,k1_wellord1(X0,X1))) )),
% 2.07/0.65    inference(equality_resolution,[],[f78])).
% 2.07/0.65  fof(f78,plain,(
% 2.07/0.65    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4 | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 2.07/0.65    inference(cnf_transformation,[],[f46])).
% 2.07/0.65  fof(f715,plain,(
% 2.07/0.65    r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),sK1),sK2) | ~spl12_42),
% 2.07/0.65    inference(avatar_component_clause,[],[f714])).
% 2.07/0.65  fof(f842,plain,(
% 2.07/0.65    spl12_4 | ~spl12_55),
% 2.07/0.65    inference(avatar_split_clause,[],[f838,f798,f113])).
% 2.07/0.65  fof(f838,plain,(
% 2.07/0.65    r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | ~spl12_55),
% 2.07/0.65    inference(resolution,[],[f799,f87])).
% 2.07/0.65  fof(f87,plain,(
% 2.07/0.65    ( ! [X0,X1] : (~r2_hidden(sK11(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 2.07/0.65    inference(cnf_transformation,[],[f52])).
% 2.07/0.65  fof(f799,plain,(
% 2.07/0.65    r2_hidden(sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK1)) | ~spl12_55),
% 2.07/0.65    inference(avatar_component_clause,[],[f798])).
% 2.07/0.65  fof(f825,plain,(
% 2.07/0.65    spl12_5 | ~spl12_47),
% 2.07/0.65    inference(avatar_split_clause,[],[f821,f740,f118])).
% 2.07/0.65  fof(f740,plain,(
% 2.07/0.65    spl12_47 <=> r2_hidden(sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)),k1_wellord1(sK2,sK0))),
% 2.07/0.65    introduced(avatar_definition,[new_symbols(naming,[spl12_47])])).
% 2.07/0.65  fof(f821,plain,(
% 2.07/0.65    r1_tarski(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)) | ~spl12_47),
% 2.07/0.65    inference(resolution,[],[f741,f87])).
% 2.07/0.65  fof(f741,plain,(
% 2.07/0.65    r2_hidden(sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)),k1_wellord1(sK2,sK0)) | ~spl12_47),
% 2.07/0.65    inference(avatar_component_clause,[],[f740])).
% 2.07/0.65  fof(f774,plain,(
% 2.07/0.65    ~spl12_49 | spl12_50),
% 2.07/0.65    inference(avatar_split_clause,[],[f772,f758,f753])).
% 2.07/0.65  fof(f753,plain,(
% 2.07/0.65    spl12_49 <=> r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0))),
% 2.07/0.65    introduced(avatar_definition,[new_symbols(naming,[spl12_49])])).
% 2.07/0.65  fof(f758,plain,(
% 2.07/0.65    spl12_50 <=> r3_xboole_0(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0))),
% 2.07/0.65    introduced(avatar_definition,[new_symbols(naming,[spl12_50])])).
% 2.07/0.65  fof(f772,plain,(
% 2.07/0.65    ~r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0)) | spl12_50),
% 2.07/0.65    inference(resolution,[],[f759,f88])).
% 2.07/0.65  fof(f88,plain,(
% 2.07/0.65    ( ! [X0,X1] : (r3_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 2.07/0.65    inference(cnf_transformation,[],[f23])).
% 2.07/0.65  fof(f23,plain,(
% 2.07/0.65    ! [X0,X1] : (r3_xboole_0(X0,X1) | (~r1_tarski(X1,X0) & ~r1_tarski(X0,X1)))),
% 2.07/0.65    inference(ennf_transformation,[],[f12])).
% 2.07/0.65  fof(f12,plain,(
% 2.07/0.65    ! [X0,X1] : ((r1_tarski(X1,X0) | r1_tarski(X0,X1)) => r3_xboole_0(X0,X1))),
% 2.07/0.65    inference(unused_predicate_definition_removal,[],[f3])).
% 2.07/0.65  fof(f3,axiom,(
% 2.07/0.65    ! [X0,X1] : (r3_xboole_0(X0,X1) <=> (r1_tarski(X1,X0) | r1_tarski(X0,X1)))),
% 2.07/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_xboole_0)).
% 2.07/0.65  fof(f759,plain,(
% 2.07/0.65    ~r3_xboole_0(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0)) | spl12_50),
% 2.07/0.65    inference(avatar_component_clause,[],[f758])).
% 2.07/0.65  fof(f763,plain,(
% 2.07/0.65    spl12_49),
% 2.07/0.65    inference(avatar_contradiction_clause,[],[f762])).
% 2.07/0.65  fof(f762,plain,(
% 2.07/0.65    $false | spl12_49),
% 2.07/0.65    inference(resolution,[],[f754,f96])).
% 2.07/0.65  fof(f96,plain,(
% 2.07/0.65    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.07/0.65    inference(equality_resolution,[],[f83])).
% 2.07/0.65  fof(f83,plain,(
% 2.07/0.65    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.07/0.65    inference(cnf_transformation,[],[f48])).
% 2.07/0.65  fof(f48,plain,(
% 2.07/0.65    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.07/0.65    inference(flattening,[],[f47])).
% 2.07/0.65  fof(f47,plain,(
% 2.07/0.65    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.07/0.65    inference(nnf_transformation,[],[f2])).
% 2.07/0.65  fof(f2,axiom,(
% 2.07/0.65    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.07/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.07/0.65  fof(f754,plain,(
% 2.07/0.65    ~r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0)) | spl12_49),
% 2.07/0.65    inference(avatar_component_clause,[],[f753])).
% 2.07/0.65  fof(f760,plain,(
% 2.07/0.65    ~spl12_50 | spl12_1 | ~spl12_41),
% 2.07/0.65    inference(avatar_split_clause,[],[f751,f711,f99,f758])).
% 2.07/0.65  fof(f99,plain,(
% 2.07/0.65    spl12_1 <=> r3_xboole_0(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))),
% 2.07/0.65    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).
% 2.07/0.65  fof(f751,plain,(
% 2.07/0.65    ~r3_xboole_0(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0)) | (spl12_1 | ~spl12_41)),
% 2.07/0.65    inference(superposition,[],[f100,f712])).
% 2.07/0.65  fof(f712,plain,(
% 2.07/0.65    sK0 = sK1 | ~spl12_41),
% 2.07/0.65    inference(avatar_component_clause,[],[f711])).
% 2.07/0.65  fof(f100,plain,(
% 2.07/0.65    ~r3_xboole_0(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | spl12_1),
% 2.07/0.65    inference(avatar_component_clause,[],[f99])).
% 2.07/0.65  fof(f742,plain,(
% 2.07/0.65    spl12_47 | spl12_46 | ~spl12_3 | ~spl12_40),
% 2.07/0.65    inference(avatar_split_clause,[],[f721,f708,f107,f736,f740])).
% 2.07/0.65  fof(f721,plain,(
% 2.07/0.65    sK0 = sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)) | r2_hidden(sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)),k1_wellord1(sK2,sK0)) | (~spl12_3 | ~spl12_40)),
% 2.07/0.65    inference(resolution,[],[f709,f164])).
% 2.07/0.65  fof(f709,plain,(
% 2.07/0.65    r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)),sK0),sK2) | ~spl12_40),
% 2.07/0.65    inference(avatar_component_clause,[],[f708])).
% 2.07/0.65  fof(f618,plain,(
% 2.07/0.65    spl12_5 | ~spl12_6 | spl12_29),
% 2.07/0.65    inference(avatar_contradiction_clause,[],[f617])).
% 2.07/0.65  fof(f617,plain,(
% 2.07/0.65    $false | (spl12_5 | ~spl12_6 | spl12_29)),
% 2.07/0.65    inference(subsumption_resolution,[],[f119,f599])).
% 2.07/0.65  fof(f599,plain,(
% 2.07/0.65    ( ! [X0] : (r1_tarski(k1_wellord1(sK2,sK1),X0)) ) | (~spl12_6 | spl12_29)),
% 2.07/0.65    inference(resolution,[],[f574,f132])).
% 2.07/0.65  fof(f132,plain,(
% 2.07/0.65    ( ! [X0,X1] : (r2_hidden(X0,k3_relat_1(sK2)) | r1_tarski(k1_wellord1(sK2,X0),X1)) ) | ~spl12_6),
% 2.07/0.65    inference(avatar_component_clause,[],[f131])).
% 2.07/0.65  fof(f131,plain,(
% 2.07/0.65    spl12_6 <=> ! [X1,X0] : (r1_tarski(k1_wellord1(sK2,X0),X1) | r2_hidden(X0,k3_relat_1(sK2)))),
% 2.07/0.65    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).
% 2.07/0.65  fof(f574,plain,(
% 2.07/0.65    ~r2_hidden(sK1,k3_relat_1(sK2)) | spl12_29),
% 2.07/0.65    inference(avatar_component_clause,[],[f573])).
% 2.07/0.65  fof(f119,plain,(
% 2.07/0.65    ~r1_tarski(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)) | spl12_5),
% 2.07/0.65    inference(avatar_component_clause,[],[f118])).
% 2.07/0.65  fof(f598,plain,(
% 2.07/0.65    spl12_4 | ~spl12_6 | spl12_27),
% 2.07/0.65    inference(avatar_contradiction_clause,[],[f597])).
% 2.07/0.65  fof(f597,plain,(
% 2.07/0.65    $false | (spl12_4 | ~spl12_6 | spl12_27)),
% 2.07/0.65    inference(subsumption_resolution,[],[f114,f579])).
% 2.07/0.65  fof(f579,plain,(
% 2.07/0.65    ( ! [X0] : (r1_tarski(k1_wellord1(sK2,sK0),X0)) ) | (~spl12_6 | spl12_27)),
% 2.07/0.65    inference(resolution,[],[f567,f132])).
% 2.07/0.65  fof(f567,plain,(
% 2.07/0.65    ~r2_hidden(sK0,k3_relat_1(sK2)) | spl12_27),
% 2.07/0.65    inference(avatar_component_clause,[],[f566])).
% 2.07/0.65  fof(f114,plain,(
% 2.07/0.65    ~r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | spl12_4),
% 2.07/0.65    inference(avatar_component_clause,[],[f113])).
% 2.07/0.65  fof(f578,plain,(
% 2.07/0.65    ~spl12_29 | spl12_30 | ~spl12_3 | spl12_5 | ~spl12_16 | ~spl12_24),
% 2.07/0.65    inference(avatar_split_clause,[],[f560,f414,f310,f118,f107,f576,f573])).
% 2.07/0.65  fof(f310,plain,(
% 2.07/0.65    spl12_16 <=> ! [X1,X0,X2] : (~r2_hidden(k4_tarski(X0,X1),sK2) | r2_hidden(k4_tarski(X2,X1),sK2) | ~r2_hidden(k4_tarski(X2,X0),sK2))),
% 2.07/0.65    introduced(avatar_definition,[new_symbols(naming,[spl12_16])])).
% 2.07/0.65  fof(f414,plain,(
% 2.07/0.65    spl12_24 <=> ! [X1,X0] : (r2_hidden(k4_tarski(X0,X1),sK2) | r2_hidden(k4_tarski(X1,X0),sK2) | ~r2_hidden(X0,k3_relat_1(sK2)) | ~r2_hidden(X1,k3_relat_1(sK2)) | X0 = X1)),
% 2.07/0.65    introduced(avatar_definition,[new_symbols(naming,[spl12_24])])).
% 2.07/0.65  fof(f560,plain,(
% 2.07/0.65    ( ! [X1] : (~r2_hidden(X1,k3_relat_1(sK2)) | sK1 = X1 | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)),X1),sK2) | r2_hidden(k4_tarski(X1,sK1),sK2) | ~r2_hidden(sK1,k3_relat_1(sK2))) ) | (~spl12_3 | spl12_5 | ~spl12_16 | ~spl12_24)),
% 2.07/0.65    inference(resolution,[],[f463,f119])).
% 2.07/0.65  fof(f463,plain,(
% 2.07/0.65    ( ! [X2,X0,X1] : (r1_tarski(k1_wellord1(sK2,X0),X2) | ~r2_hidden(X1,k3_relat_1(sK2)) | X0 = X1 | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,X0),X2),X1),sK2) | r2_hidden(k4_tarski(X1,X0),sK2) | ~r2_hidden(X0,k3_relat_1(sK2))) ) | (~spl12_3 | ~spl12_16 | ~spl12_24)),
% 2.07/0.65    inference(resolution,[],[f429,f126])).
% 2.07/0.65  fof(f429,plain,(
% 2.07/0.65    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X2,X1),sK2) | ~r2_hidden(X1,k3_relat_1(sK2)) | ~r2_hidden(X0,k3_relat_1(sK2)) | X0 = X1 | r2_hidden(k4_tarski(X2,X0),sK2) | r2_hidden(k4_tarski(X0,X1),sK2)) ) | (~spl12_16 | ~spl12_24)),
% 2.07/0.65    inference(resolution,[],[f415,f311])).
% 2.07/0.65  fof(f311,plain,(
% 2.07/0.65    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | r2_hidden(k4_tarski(X2,X1),sK2) | ~r2_hidden(k4_tarski(X2,X0),sK2)) ) | ~spl12_16),
% 2.07/0.65    inference(avatar_component_clause,[],[f310])).
% 2.07/0.65  fof(f415,plain,(
% 2.07/0.65    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,X1),sK2) | r2_hidden(k4_tarski(X1,X0),sK2) | ~r2_hidden(X0,k3_relat_1(sK2)) | ~r2_hidden(X1,k3_relat_1(sK2)) | X0 = X1) ) | ~spl12_24),
% 2.07/0.65    inference(avatar_component_clause,[],[f414])).
% 2.07/0.65  fof(f571,plain,(
% 2.07/0.65    ~spl12_27 | spl12_28 | ~spl12_3 | spl12_4 | ~spl12_16 | ~spl12_24),
% 2.07/0.65    inference(avatar_split_clause,[],[f559,f414,f310,f113,f107,f569,f566])).
% 2.07/0.65  fof(f559,plain,(
% 2.07/0.65    ( ! [X0] : (~r2_hidden(X0,k3_relat_1(sK2)) | sK0 = X0 | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),X0),sK2) | r2_hidden(k4_tarski(X0,sK0),sK2) | ~r2_hidden(sK0,k3_relat_1(sK2))) ) | (~spl12_3 | spl12_4 | ~spl12_16 | ~spl12_24)),
% 2.07/0.65    inference(resolution,[],[f463,f114])).
% 2.07/0.65  fof(f428,plain,(
% 2.07/0.65    ~spl12_3 | ~spl12_2 | spl12_23),
% 2.07/0.65    inference(avatar_split_clause,[],[f419,f411,f103,f107])).
% 2.07/0.65  fof(f103,plain,(
% 2.07/0.65    spl12_2 <=> v2_wellord1(sK2)),
% 2.07/0.65    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).
% 2.07/0.65  fof(f411,plain,(
% 2.07/0.65    spl12_23 <=> v6_relat_2(sK2)),
% 2.07/0.65    introduced(avatar_definition,[new_symbols(naming,[spl12_23])])).
% 2.07/0.65  fof(f419,plain,(
% 2.07/0.65    ~v2_wellord1(sK2) | ~v1_relat_1(sK2) | spl12_23),
% 2.07/0.65    inference(resolution,[],[f412,f73])).
% 2.07/0.65  fof(f73,plain,(
% 2.07/0.65    ( ! [X0] : (v6_relat_2(X0) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 2.07/0.65    inference(cnf_transformation,[],[f41])).
% 2.07/0.65  fof(f41,plain,(
% 2.07/0.65    ! [X0] : (((v2_wellord1(X0) | ~v1_wellord1(X0) | ~v6_relat_2(X0) | ~v4_relat_2(X0) | ~v8_relat_2(X0) | ~v1_relat_2(X0)) & ((v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0)) | ~v2_wellord1(X0))) | ~v1_relat_1(X0))),
% 2.07/0.65    inference(flattening,[],[f40])).
% 2.07/0.65  fof(f40,plain,(
% 2.07/0.65    ! [X0] : (((v2_wellord1(X0) | (~v1_wellord1(X0) | ~v6_relat_2(X0) | ~v4_relat_2(X0) | ~v8_relat_2(X0) | ~v1_relat_2(X0))) & ((v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0)) | ~v2_wellord1(X0))) | ~v1_relat_1(X0))),
% 2.07/0.65    inference(nnf_transformation,[],[f20])).
% 2.07/0.65  fof(f20,plain,(
% 2.07/0.65    ! [X0] : ((v2_wellord1(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0))) | ~v1_relat_1(X0))),
% 2.07/0.65    inference(ennf_transformation,[],[f6])).
% 2.07/0.65  fof(f6,axiom,(
% 2.07/0.65    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0))))),
% 2.07/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_wellord1)).
% 2.07/0.65  fof(f412,plain,(
% 2.07/0.65    ~v6_relat_2(sK2) | spl12_23),
% 2.07/0.65    inference(avatar_component_clause,[],[f411])).
% 2.07/0.65  fof(f416,plain,(
% 2.07/0.65    ~spl12_23 | spl12_24 | ~spl12_3),
% 2.07/0.65    inference(avatar_split_clause,[],[f409,f107,f414,f411])).
% 2.07/0.67  fof(f409,plain,(
% 2.07/0.67    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,X1),sK2) | X0 = X1 | ~r2_hidden(X1,k3_relat_1(sK2)) | ~r2_hidden(X0,k3_relat_1(sK2)) | ~v6_relat_2(sK2) | r2_hidden(k4_tarski(X1,X0),sK2)) ) | ~spl12_3),
% 2.07/0.67    inference(resolution,[],[f60,f108])).
% 2.07/0.67  fof(f60,plain,(
% 2.07/0.67    ( ! [X4,X0,X3] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(X3,X4),X0) | X3 = X4 | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0)) | ~v6_relat_2(X0) | r2_hidden(k4_tarski(X4,X3),X0)) )),
% 2.07/0.67    inference(cnf_transformation,[],[f35])).
% 2.07/0.67  fof(f35,plain,(
% 2.07/0.67    ! [X0] : (((v6_relat_2(X0) | (~r2_hidden(k4_tarski(sK6(X0),sK5(X0)),X0) & ~r2_hidden(k4_tarski(sK5(X0),sK6(X0)),X0) & sK5(X0) != sK6(X0) & r2_hidden(sK6(X0),k3_relat_1(X0)) & r2_hidden(sK5(X0),k3_relat_1(X0)))) & (! [X3,X4] : (r2_hidden(k4_tarski(X4,X3),X0) | r2_hidden(k4_tarski(X3,X4),X0) | X3 = X4 | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0))) | ~v6_relat_2(X0))) | ~v1_relat_1(X0))),
% 2.07/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f33,f34])).
% 2.07/0.67  fof(f34,plain,(
% 2.07/0.67    ! [X0] : (? [X1,X2] : (~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0))) => (~r2_hidden(k4_tarski(sK6(X0),sK5(X0)),X0) & ~r2_hidden(k4_tarski(sK5(X0),sK6(X0)),X0) & sK5(X0) != sK6(X0) & r2_hidden(sK6(X0),k3_relat_1(X0)) & r2_hidden(sK5(X0),k3_relat_1(X0))))),
% 2.07/0.67    introduced(choice_axiom,[])).
% 2.07/0.67  fof(f33,plain,(
% 2.07/0.67    ! [X0] : (((v6_relat_2(X0) | ? [X1,X2] : (~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))) & (! [X3,X4] : (r2_hidden(k4_tarski(X4,X3),X0) | r2_hidden(k4_tarski(X3,X4),X0) | X3 = X4 | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0))) | ~v6_relat_2(X0))) | ~v1_relat_1(X0))),
% 2.07/0.67    inference(rectify,[],[f32])).
% 2.07/0.67  fof(f32,plain,(
% 2.07/0.67    ! [X0] : (((v6_relat_2(X0) | ? [X1,X2] : (~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))) & (! [X1,X2] : (r2_hidden(k4_tarski(X2,X1),X0) | r2_hidden(k4_tarski(X1,X2),X0) | X1 = X2 | ~r2_hidden(X2,k3_relat_1(X0)) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v6_relat_2(X0))) | ~v1_relat_1(X0))),
% 2.07/0.67    inference(nnf_transformation,[],[f17])).
% 2.07/0.67  fof(f17,plain,(
% 2.07/0.67    ! [X0] : ((v6_relat_2(X0) <=> ! [X1,X2] : (r2_hidden(k4_tarski(X2,X1),X0) | r2_hidden(k4_tarski(X1,X2),X0) | X1 = X2 | ~r2_hidden(X2,k3_relat_1(X0)) | ~r2_hidden(X1,k3_relat_1(X0)))) | ~v1_relat_1(X0))),
% 2.07/0.67    inference(ennf_transformation,[],[f9])).
% 2.07/0.67  fof(f9,axiom,(
% 2.07/0.67    ! [X0] : (v1_relat_1(X0) => (v6_relat_2(X0) <=> ! [X1,X2] : ~(~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))))),
% 2.07/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l4_wellord1)).
% 2.07/0.67  fof(f329,plain,(
% 2.07/0.67    ~spl12_3 | ~spl12_2 | spl12_15),
% 2.07/0.67    inference(avatar_split_clause,[],[f316,f307,f103,f107])).
% 2.07/0.67  fof(f307,plain,(
% 2.07/0.67    spl12_15 <=> v8_relat_2(sK2)),
% 2.07/0.67    introduced(avatar_definition,[new_symbols(naming,[spl12_15])])).
% 2.07/0.67  fof(f316,plain,(
% 2.07/0.67    ~v2_wellord1(sK2) | ~v1_relat_1(sK2) | spl12_15),
% 2.07/0.67    inference(resolution,[],[f308,f71])).
% 2.07/0.67  fof(f71,plain,(
% 2.07/0.67    ( ! [X0] : (v8_relat_2(X0) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 2.07/0.67    inference(cnf_transformation,[],[f41])).
% 2.07/0.67  fof(f308,plain,(
% 2.07/0.67    ~v8_relat_2(sK2) | spl12_15),
% 2.07/0.67    inference(avatar_component_clause,[],[f307])).
% 2.07/0.67  fof(f312,plain,(
% 2.07/0.67    ~spl12_15 | spl12_16 | ~spl12_3),
% 2.07/0.67    inference(avatar_split_clause,[],[f305,f107,f310,f307])).
% 2.07/0.67  fof(f305,plain,(
% 2.07/0.67    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | ~r2_hidden(k4_tarski(X2,X0),sK2) | ~v8_relat_2(sK2) | r2_hidden(k4_tarski(X2,X1),sK2)) ) | ~spl12_3),
% 2.07/0.67    inference(resolution,[],[f66,f108])).
% 2.07/0.67  fof(f66,plain,(
% 2.07/0.67    ( ! [X6,X4,X0,X5] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(k4_tarski(X4,X5),X0) | ~v8_relat_2(X0) | r2_hidden(k4_tarski(X4,X6),X0)) )),
% 2.07/0.67    inference(cnf_transformation,[],[f39])).
% 2.07/0.67  fof(f39,plain,(
% 2.07/0.67    ! [X0] : (((v8_relat_2(X0) | (~r2_hidden(k4_tarski(sK7(X0),sK9(X0)),X0) & r2_hidden(k4_tarski(sK8(X0),sK9(X0)),X0) & r2_hidden(k4_tarski(sK7(X0),sK8(X0)),X0))) & (! [X4,X5,X6] : (r2_hidden(k4_tarski(X4,X6),X0) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~v8_relat_2(X0))) | ~v1_relat_1(X0))),
% 2.07/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f37,f38])).
% 2.07/0.67  fof(f38,plain,(
% 2.07/0.67    ! [X0] : (? [X1,X2,X3] : (~r2_hidden(k4_tarski(X1,X3),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(k4_tarski(X1,X2),X0)) => (~r2_hidden(k4_tarski(sK7(X0),sK9(X0)),X0) & r2_hidden(k4_tarski(sK8(X0),sK9(X0)),X0) & r2_hidden(k4_tarski(sK7(X0),sK8(X0)),X0)))),
% 2.07/0.67    introduced(choice_axiom,[])).
% 2.07/0.67  fof(f37,plain,(
% 2.07/0.67    ! [X0] : (((v8_relat_2(X0) | ? [X1,X2,X3] : (~r2_hidden(k4_tarski(X1,X3),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(k4_tarski(X1,X2),X0))) & (! [X4,X5,X6] : (r2_hidden(k4_tarski(X4,X6),X0) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~v8_relat_2(X0))) | ~v1_relat_1(X0))),
% 2.07/0.67    inference(rectify,[],[f36])).
% 2.07/0.67  fof(f36,plain,(
% 2.07/0.67    ! [X0] : (((v8_relat_2(X0) | ? [X1,X2,X3] : (~r2_hidden(k4_tarski(X1,X3),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(k4_tarski(X1,X2),X0))) & (! [X1,X2,X3] : (r2_hidden(k4_tarski(X1,X3),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(k4_tarski(X1,X2),X0)) | ~v8_relat_2(X0))) | ~v1_relat_1(X0))),
% 2.07/0.67    inference(nnf_transformation,[],[f19])).
% 2.07/0.67  fof(f19,plain,(
% 2.07/0.67    ! [X0] : ((v8_relat_2(X0) <=> ! [X1,X2,X3] : (r2_hidden(k4_tarski(X1,X3),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(k4_tarski(X1,X2),X0))) | ~v1_relat_1(X0))),
% 2.07/0.67    inference(flattening,[],[f18])).
% 2.07/0.67  fof(f18,plain,(
% 2.07/0.67    ! [X0] : ((v8_relat_2(X0) <=> ! [X1,X2,X3] : (r2_hidden(k4_tarski(X1,X3),X0) | (~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(k4_tarski(X1,X2),X0)))) | ~v1_relat_1(X0))),
% 2.07/0.67    inference(ennf_transformation,[],[f7])).
% 2.07/0.67  fof(f7,axiom,(
% 2.07/0.67    ! [X0] : (v1_relat_1(X0) => (v8_relat_2(X0) <=> ! [X1,X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(k4_tarski(X1,X2),X0)) => r2_hidden(k4_tarski(X1,X3),X0))))),
% 2.07/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l2_wellord1)).
% 2.07/0.67  fof(f265,plain,(
% 2.07/0.67    ~spl12_3 | ~spl12_2 | spl12_11),
% 2.07/0.67    inference(avatar_split_clause,[],[f255,f247,f103,f107])).
% 2.07/0.67  fof(f247,plain,(
% 2.07/0.67    spl12_11 <=> v4_relat_2(sK2)),
% 2.07/0.67    introduced(avatar_definition,[new_symbols(naming,[spl12_11])])).
% 2.07/0.67  fof(f255,plain,(
% 2.07/0.67    ~v2_wellord1(sK2) | ~v1_relat_1(sK2) | spl12_11),
% 2.07/0.67    inference(resolution,[],[f248,f72])).
% 2.07/0.67  fof(f72,plain,(
% 2.07/0.67    ( ! [X0] : (v4_relat_2(X0) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 2.07/0.67    inference(cnf_transformation,[],[f41])).
% 2.07/0.67  fof(f248,plain,(
% 2.07/0.67    ~v4_relat_2(sK2) | spl12_11),
% 2.07/0.67    inference(avatar_component_clause,[],[f247])).
% 2.07/0.67  fof(f252,plain,(
% 2.07/0.67    ~spl12_11 | spl12_12 | ~spl12_3),
% 2.07/0.67    inference(avatar_split_clause,[],[f245,f107,f250,f247])).
% 2.07/0.67  fof(f245,plain,(
% 2.07/0.67    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | ~r2_hidden(k4_tarski(X1,X0),sK2) | ~v4_relat_2(sK2) | X0 = X1) ) | ~spl12_3),
% 2.07/0.67    inference(resolution,[],[f56,f108])).
% 2.07/0.67  fof(f56,plain,(
% 2.07/0.67    ( ! [X4,X0,X3] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(X4,X3),X0) | ~r2_hidden(k4_tarski(X3,X4),X0) | ~v4_relat_2(X0) | X3 = X4) )),
% 2.07/0.67    inference(cnf_transformation,[],[f31])).
% 2.07/0.67  fof(f31,plain,(
% 2.07/0.67    ! [X0] : (((v4_relat_2(X0) | (sK3(X0) != sK4(X0) & r2_hidden(k4_tarski(sK4(X0),sK3(X0)),X0) & r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0))) & (! [X3,X4] : (X3 = X4 | ~r2_hidden(k4_tarski(X4,X3),X0) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~v4_relat_2(X0))) | ~v1_relat_1(X0))),
% 2.07/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f29,f30])).
% 2.07/0.67  fof(f30,plain,(
% 2.07/0.67    ! [X0] : (? [X1,X2] : (X1 != X2 & r2_hidden(k4_tarski(X2,X1),X0) & r2_hidden(k4_tarski(X1,X2),X0)) => (sK3(X0) != sK4(X0) & r2_hidden(k4_tarski(sK4(X0),sK3(X0)),X0) & r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0)))),
% 2.07/0.67    introduced(choice_axiom,[])).
% 2.07/0.67  fof(f29,plain,(
% 2.07/0.67    ! [X0] : (((v4_relat_2(X0) | ? [X1,X2] : (X1 != X2 & r2_hidden(k4_tarski(X2,X1),X0) & r2_hidden(k4_tarski(X1,X2),X0))) & (! [X3,X4] : (X3 = X4 | ~r2_hidden(k4_tarski(X4,X3),X0) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~v4_relat_2(X0))) | ~v1_relat_1(X0))),
% 2.07/0.67    inference(rectify,[],[f28])).
% 2.07/0.67  fof(f28,plain,(
% 2.07/0.67    ! [X0] : (((v4_relat_2(X0) | ? [X1,X2] : (X1 != X2 & r2_hidden(k4_tarski(X2,X1),X0) & r2_hidden(k4_tarski(X1,X2),X0))) & (! [X1,X2] : (X1 = X2 | ~r2_hidden(k4_tarski(X2,X1),X0) | ~r2_hidden(k4_tarski(X1,X2),X0)) | ~v4_relat_2(X0))) | ~v1_relat_1(X0))),
% 2.07/0.67    inference(nnf_transformation,[],[f16])).
% 2.07/0.67  fof(f16,plain,(
% 2.07/0.67    ! [X0] : ((v4_relat_2(X0) <=> ! [X1,X2] : (X1 = X2 | ~r2_hidden(k4_tarski(X2,X1),X0) | ~r2_hidden(k4_tarski(X1,X2),X0))) | ~v1_relat_1(X0))),
% 2.07/0.67    inference(flattening,[],[f15])).
% 2.07/0.67  fof(f15,plain,(
% 2.07/0.67    ! [X0] : ((v4_relat_2(X0) <=> ! [X1,X2] : (X1 = X2 | (~r2_hidden(k4_tarski(X2,X1),X0) | ~r2_hidden(k4_tarski(X1,X2),X0)))) | ~v1_relat_1(X0))),
% 2.07/0.67    inference(ennf_transformation,[],[f8])).
% 2.07/0.67  fof(f8,axiom,(
% 2.07/0.67    ! [X0] : (v1_relat_1(X0) => (v4_relat_2(X0) <=> ! [X1,X2] : ((r2_hidden(k4_tarski(X2,X1),X0) & r2_hidden(k4_tarski(X1,X2),X0)) => X1 = X2)))),
% 2.07/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_wellord1)).
% 2.07/0.67  fof(f133,plain,(
% 2.07/0.67    ~spl12_3 | spl12_6 | ~spl12_3),
% 2.07/0.67    inference(avatar_split_clause,[],[f127,f107,f131,f107])).
% 2.07/0.67  fof(f127,plain,(
% 2.07/0.67    ( ! [X0,X1] : (r1_tarski(k1_wellord1(sK2,X0),X1) | r2_hidden(X0,k3_relat_1(sK2)) | ~v1_relat_1(sK2)) ) | ~spl12_3),
% 2.07/0.67    inference(resolution,[],[f126,f91])).
% 2.07/0.67  fof(f91,plain,(
% 2.07/0.67    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X1,k3_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 2.07/0.67    inference(cnf_transformation,[],[f25])).
% 2.07/0.67  fof(f25,plain,(
% 2.07/0.67    ! [X0,X1,X2] : ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 2.07/0.67    inference(flattening,[],[f24])).
% 2.07/0.67  fof(f24,plain,(
% 2.07/0.67    ! [X0,X1,X2] : (((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 2.07/0.67    inference(ennf_transformation,[],[f4])).
% 2.07/0.67  fof(f4,axiom,(
% 2.07/0.67    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 2.07/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).
% 2.07/0.67  fof(f120,plain,(
% 2.07/0.67    ~spl12_5 | spl12_1),
% 2.07/0.67    inference(avatar_split_clause,[],[f116,f99,f118])).
% 2.07/0.67  fof(f116,plain,(
% 2.07/0.67    ~r1_tarski(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)) | spl12_1),
% 2.07/0.67    inference(resolution,[],[f89,f100])).
% 2.07/0.67  fof(f89,plain,(
% 2.07/0.67    ( ! [X0,X1] : (r3_xboole_0(X0,X1) | ~r1_tarski(X1,X0)) )),
% 2.07/0.67    inference(cnf_transformation,[],[f23])).
% 2.07/0.67  fof(f115,plain,(
% 2.07/0.67    ~spl12_4 | spl12_1),
% 2.07/0.67    inference(avatar_split_clause,[],[f111,f99,f113])).
% 2.07/0.67  fof(f111,plain,(
% 2.07/0.67    ~r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | spl12_1),
% 2.07/0.67    inference(resolution,[],[f88,f100])).
% 2.07/0.67  fof(f109,plain,(
% 2.07/0.67    spl12_3),
% 2.07/0.67    inference(avatar_split_clause,[],[f53,f107])).
% 2.07/0.67  fof(f53,plain,(
% 2.07/0.67    v1_relat_1(sK2)),
% 2.07/0.67    inference(cnf_transformation,[],[f27])).
% 2.07/0.67  fof(f27,plain,(
% 2.07/0.67    ~r3_xboole_0(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) & v2_wellord1(sK2) & v1_relat_1(sK2)),
% 2.07/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f26])).
% 2.07/0.67  fof(f26,plain,(
% 2.07/0.67    ? [X0,X1,X2] : (~r3_xboole_0(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) & v2_wellord1(X2) & v1_relat_1(X2)) => (~r3_xboole_0(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) & v2_wellord1(sK2) & v1_relat_1(sK2))),
% 2.07/0.67    introduced(choice_axiom,[])).
% 2.07/0.67  fof(f14,plain,(
% 2.07/0.67    ? [X0,X1,X2] : (~r3_xboole_0(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) & v2_wellord1(X2) & v1_relat_1(X2))),
% 2.07/0.67    inference(flattening,[],[f13])).
% 2.07/0.67  fof(f13,plain,(
% 2.07/0.67    ? [X0,X1,X2] : ((~r3_xboole_0(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) & v2_wellord1(X2)) & v1_relat_1(X2))),
% 2.07/0.67    inference(ennf_transformation,[],[f11])).
% 2.07/0.67  fof(f11,negated_conjecture,(
% 2.07/0.67    ~! [X0,X1,X2] : (v1_relat_1(X2) => (v2_wellord1(X2) => r3_xboole_0(k1_wellord1(X2,X0),k1_wellord1(X2,X1))))),
% 2.07/0.67    inference(negated_conjecture,[],[f10])).
% 2.07/0.67  fof(f10,conjecture,(
% 2.07/0.67    ! [X0,X1,X2] : (v1_relat_1(X2) => (v2_wellord1(X2) => r3_xboole_0(k1_wellord1(X2,X0),k1_wellord1(X2,X1))))),
% 2.07/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_wellord1)).
% 2.07/0.67  fof(f105,plain,(
% 2.07/0.67    spl12_2),
% 2.07/0.67    inference(avatar_split_clause,[],[f54,f103])).
% 2.07/0.67  fof(f54,plain,(
% 2.07/0.67    v2_wellord1(sK2)),
% 2.07/0.67    inference(cnf_transformation,[],[f27])).
% 2.07/0.67  fof(f101,plain,(
% 2.07/0.67    ~spl12_1),
% 2.07/0.67    inference(avatar_split_clause,[],[f55,f99])).
% 2.07/0.67  fof(f55,plain,(
% 2.07/0.67    ~r3_xboole_0(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))),
% 2.07/0.67    inference(cnf_transformation,[],[f27])).
% 2.07/0.67  % SZS output end Proof for theBenchmark
% 2.07/0.67  % (10456)------------------------------
% 2.07/0.67  % (10456)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.07/0.67  % (10456)Termination reason: Refutation
% 2.07/0.67  
% 2.07/0.67  % (10456)Memory used [KB]: 11513
% 2.07/0.67  % (10456)Time elapsed: 0.236 s
% 2.07/0.67  % (10456)------------------------------
% 2.07/0.67  % (10456)------------------------------
% 2.07/0.67  % (10431)Success in time 0.307 s
%------------------------------------------------------------------------------
