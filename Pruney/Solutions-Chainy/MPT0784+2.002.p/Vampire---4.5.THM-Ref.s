%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:03 EST 2020

% Result     : Theorem 1.52s
% Output     : Refutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :  194 ( 505 expanded)
%              Number of leaves         :   41 ( 189 expanded)
%              Depth                    :   18
%              Number of atoms          :  838 (2366 expanded)
%              Number of equality atoms :   87 ( 376 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1014,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f97,f101,f105,f122,f208,f221,f247,f264,f316,f328,f421,f436,f523,f572,f623,f665,f679,f725,f747,f763,f775,f834,f906,f914,f939,f977,f1013])).

fof(f1013,plain,
    ( spl12_39
    | spl12_1
    | ~ spl12_3
    | ~ spl12_14
    | ~ spl12_55 ),
    inference(avatar_split_clause,[],[f1011,f659,f245,f103,f95,f540])).

fof(f540,plain,
    ( spl12_39
  <=> r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_39])])).

fof(f95,plain,
    ( spl12_1
  <=> r3_xboole_0(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f103,plain,
    ( spl12_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f245,plain,
    ( spl12_14
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | r2_hidden(k4_tarski(X2,X1),sK2)
        | ~ r2_hidden(k4_tarski(X2,X0),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_14])])).

fof(f659,plain,
    ( spl12_55
  <=> r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_55])])).

fof(f1011,plain,
    ( r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),sK1),sK2)
    | spl12_1
    | ~ spl12_3
    | ~ spl12_14
    | ~ spl12_55 ),
    inference(resolution,[],[f1009,f96])).

fof(f96,plain,
    ( ~ r3_xboole_0(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | spl12_1 ),
    inference(avatar_component_clause,[],[f95])).

fof(f1009,plain,
    ( ! [X3] :
        ( r3_xboole_0(k1_wellord1(sK2,sK0),X3)
        | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK0),X3),sK1),sK2) )
    | ~ spl12_3
    | ~ spl12_14
    | ~ spl12_55 ),
    inference(resolution,[],[f1005,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r3_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r3_xboole_0(X0,X1)
        | ( ~ r1_tarski(X1,X0)
          & ~ r1_tarski(X0,X1) ) )
      & ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1)
        | ~ r3_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r3_xboole_0(X0,X1)
        | ( ~ r1_tarski(X1,X0)
          & ~ r1_tarski(X0,X1) ) )
      & ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1)
        | ~ r3_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
    <=> ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_xboole_0)).

fof(f1005,plain,
    ( ! [X3] :
        ( r1_tarski(k1_wellord1(sK2,sK0),X3)
        | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK0),X3),sK1),sK2) )
    | ~ spl12_3
    | ~ spl12_14
    | ~ spl12_55 ),
    inference(resolution,[],[f783,f115])).

fof(f115,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,X0),X1),X0),sK2)
        | r1_tarski(k1_wellord1(sK2,X0),X1) )
    | ~ spl12_3 ),
    inference(resolution,[],[f114,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK11(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK11(X0,X1),X1)
          & r2_hidden(sK11(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f47,f48])).

fof(f48,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK11(X0,X1),X1)
        & r2_hidden(sK11(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
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

fof(f114,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_wellord1(sK2,X1))
        | r2_hidden(k4_tarski(X0,X1),sK2) )
    | ~ spl12_3 ),
    inference(resolution,[],[f91,f104])).

fof(f104,plain,
    ( v1_relat_1(sK2)
    | ~ spl12_3 ),
    inference(avatar_component_clause,[],[f103])).

fof(f91,plain,(
    ! [X4,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X4,k1_wellord1(X0,X1))
      | r2_hidden(k4_tarski(X4,X1),X0) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k4_tarski(X4,X1),X0)
      | ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f43,f44])).

fof(f44,plain,(
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
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f42])).

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
    inference(flattening,[],[f41])).

fof(f41,plain,(
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

fof(f783,plain,
    ( ! [X1] :
        ( ~ r2_hidden(k4_tarski(X1,sK0),sK2)
        | r2_hidden(k4_tarski(X1,sK1),sK2) )
    | ~ spl12_14
    | ~ spl12_55 ),
    inference(resolution,[],[f748,f246])).

fof(f246,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | r2_hidden(k4_tarski(X2,X1),sK2)
        | ~ r2_hidden(k4_tarski(X2,X0),sK2) )
    | ~ spl12_14 ),
    inference(avatar_component_clause,[],[f245])).

fof(f748,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl12_55 ),
    inference(avatar_component_clause,[],[f659])).

fof(f977,plain,(
    spl12_72 ),
    inference(avatar_contradiction_clause,[],[f974])).

fof(f974,plain,
    ( $false
    | spl12_72 ),
    inference(resolution,[],[f938,f81])).

fof(f81,plain,(
    ! [X0] : r3_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] : r3_xboole_0(X0,X0) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r3_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_xboole_0)).

fof(f938,plain,
    ( ~ r3_xboole_0(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0))
    | spl12_72 ),
    inference(avatar_component_clause,[],[f937])).

fof(f937,plain,
    ( spl12_72
  <=> r3_xboole_0(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_72])])).

fof(f939,plain,
    ( ~ spl12_72
    | spl12_1
    | ~ spl12_54 ),
    inference(avatar_split_clause,[],[f916,f656,f95,f937])).

fof(f656,plain,
    ( spl12_54
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_54])])).

fof(f916,plain,
    ( ~ r3_xboole_0(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0))
    | spl12_1
    | ~ spl12_54 ),
    inference(superposition,[],[f96,f657])).

fof(f657,plain,
    ( sK0 = sK1
    | ~ spl12_54 ),
    inference(avatar_component_clause,[],[f656])).

fof(f914,plain,
    ( ~ spl12_37
    | spl12_59
    | spl12_54
    | ~ spl12_10
    | ~ spl12_30
    | ~ spl12_56 ),
    inference(avatar_split_clause,[],[f682,f663,f419,f206,f656,f677,f503])).

fof(f503,plain,
    ( spl12_37
  <=> r2_hidden(sK0,k3_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_37])])).

fof(f677,plain,
    ( spl12_59
  <=> r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)),sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_59])])).

fof(f206,plain,
    ( spl12_10
  <=> ! [X1,X0] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | X0 = X1
        | ~ r2_hidden(k4_tarski(X1,X0),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).

fof(f419,plain,
    ( spl12_30
  <=> ! [X0] :
        ( sK1 = X0
        | ~ r2_hidden(X0,k3_relat_1(sK2))
        | r2_hidden(k4_tarski(X0,sK1),sK2)
        | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)),X0),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_30])])).

fof(f663,plain,
    ( spl12_56
  <=> r2_hidden(k4_tarski(sK1,sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_56])])).

fof(f682,plain,
    ( sK0 = sK1
    | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)),sK0),sK2)
    | ~ r2_hidden(sK0,k3_relat_1(sK2))
    | ~ spl12_10
    | ~ spl12_30
    | ~ spl12_56 ),
    inference(resolution,[],[f664,f449])).

fof(f449,plain,
    ( ! [X4] :
        ( ~ r2_hidden(k4_tarski(sK1,X4),sK2)
        | sK1 = X4
        | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)),X4),sK2)
        | ~ r2_hidden(X4,k3_relat_1(sK2)) )
    | ~ spl12_10
    | ~ spl12_30 ),
    inference(duplicate_literal_removal,[],[f442])).

fof(f442,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k3_relat_1(sK2))
        | sK1 = X4
        | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)),X4),sK2)
        | sK1 = X4
        | ~ r2_hidden(k4_tarski(sK1,X4),sK2) )
    | ~ spl12_10
    | ~ spl12_30 ),
    inference(resolution,[],[f420,f207])).

fof(f207,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | X0 = X1
        | ~ r2_hidden(k4_tarski(X1,X0),sK2) )
    | ~ spl12_10 ),
    inference(avatar_component_clause,[],[f206])).

fof(f420,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,sK1),sK2)
        | ~ r2_hidden(X0,k3_relat_1(sK2))
        | sK1 = X0
        | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)),X0),sK2) )
    | ~ spl12_30 ),
    inference(avatar_component_clause,[],[f419])).

fof(f664,plain,
    ( r2_hidden(k4_tarski(sK1,sK0),sK2)
    | ~ spl12_56 ),
    inference(avatar_component_clause,[],[f663])).

fof(f906,plain,
    ( spl12_39
    | spl12_1
    | ~ spl12_3
    | ~ spl12_14
    | ~ spl12_62 ),
    inference(avatar_split_clause,[],[f904,f719,f245,f103,f95,f540])).

fof(f719,plain,
    ( spl12_62
  <=> sK0 = sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_62])])).

fof(f904,plain,
    ( r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),sK1),sK2)
    | spl12_1
    | ~ spl12_3
    | ~ spl12_14
    | ~ spl12_62 ),
    inference(resolution,[],[f729,f96])).

fof(f729,plain,
    ( ! [X4] :
        ( r3_xboole_0(k1_wellord1(sK2,sK0),X4)
        | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK0),X4),sK1),sK2) )
    | spl12_1
    | ~ spl12_3
    | ~ spl12_14
    | ~ spl12_62 ),
    inference(superposition,[],[f276,f720])).

fof(f720,plain,
    ( sK0 = sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0))
    | ~ spl12_62 ),
    inference(avatar_component_clause,[],[f719])).

fof(f276,plain,
    ( ! [X3] :
        ( r3_xboole_0(k1_wellord1(sK2,sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0))),X3)
        | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0))),X3),sK1),sK2) )
    | spl12_1
    | ~ spl12_3
    | ~ spl12_14 ),
    inference(resolution,[],[f270,f86])).

fof(f270,plain,
    ( ! [X0] :
        ( r1_tarski(k1_wellord1(sK2,sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0))),X0)
        | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0))),X0),sK1),sK2) )
    | spl12_1
    | ~ spl12_3
    | ~ spl12_14 ),
    inference(resolution,[],[f268,f96])).

fof(f268,plain,
    ( ! [X6,X4,X5] :
        ( r3_xboole_0(X5,k1_wellord1(sK2,X4))
        | r1_tarski(k1_wellord1(sK2,sK11(k1_wellord1(sK2,X4),X5)),X6)
        | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK11(k1_wellord1(sK2,X4),X5)),X6),X4),sK2) )
    | ~ spl12_3
    | ~ spl12_14 ),
    inference(resolution,[],[f266,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | r3_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f266,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k1_wellord1(sK2,X0),X1)
        | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK11(k1_wellord1(sK2,X0),X1)),X2),X0),sK2)
        | r1_tarski(k1_wellord1(sK2,sK11(k1_wellord1(sK2,X0),X1)),X2) )
    | ~ spl12_3
    | ~ spl12_14 ),
    inference(resolution,[],[f265,f115])).

fof(f265,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,sK11(k1_wellord1(sK2,X1),X2)),sK2)
        | r2_hidden(k4_tarski(X0,X1),sK2)
        | r1_tarski(k1_wellord1(sK2,X1),X2) )
    | ~ spl12_3
    | ~ spl12_14 ),
    inference(resolution,[],[f246,f115])).

fof(f834,plain,
    ( spl12_28
    | ~ spl12_45 ),
    inference(avatar_split_clause,[],[f830,f570,f402])).

fof(f402,plain,
    ( spl12_28
  <=> r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_28])])).

fof(f570,plain,
    ( spl12_45
  <=> r2_hidden(sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_45])])).

fof(f830,plain,
    ( r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ spl12_45 ),
    inference(resolution,[],[f571,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK11(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f571,plain,
    ( r2_hidden(sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK1))
    | ~ spl12_45 ),
    inference(avatar_component_clause,[],[f570])).

fof(f775,plain,
    ( spl12_1
    | ~ spl12_25 ),
    inference(avatar_split_clause,[],[f773,f377,f95])).

fof(f377,plain,
    ( spl12_25
  <=> r1_tarski(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_25])])).

fof(f773,plain,
    ( r3_xboole_0(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ spl12_25 ),
    inference(resolution,[],[f378,f87])).

fof(f378,plain,
    ( r1_tarski(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0))
    | ~ spl12_25 ),
    inference(avatar_component_clause,[],[f377])).

fof(f763,plain,
    ( spl12_25
    | ~ spl12_63 ),
    inference(avatar_split_clause,[],[f759,f723,f377])).

fof(f723,plain,
    ( spl12_63
  <=> r2_hidden(sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)),k1_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_63])])).

fof(f759,plain,
    ( r1_tarski(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0))
    | ~ spl12_63 ),
    inference(resolution,[],[f724,f84])).

fof(f724,plain,
    ( r2_hidden(sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)),k1_wellord1(sK2,sK0))
    | ~ spl12_63 ),
    inference(avatar_component_clause,[],[f723])).

fof(f747,plain,
    ( spl12_25
    | spl12_54
    | ~ spl12_56
    | ~ spl12_3
    | ~ spl12_10
    | ~ spl12_62 ),
    inference(avatar_split_clause,[],[f733,f719,f206,f103,f663,f656,f377])).

fof(f733,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK0),sK2)
    | sK0 = sK1
    | r1_tarski(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0))
    | ~ spl12_3
    | ~ spl12_10
    | ~ spl12_62 ),
    inference(superposition,[],[f222,f720])).

fof(f222,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,sK11(k1_wellord1(sK2,X0),X1)),sK2)
        | sK11(k1_wellord1(sK2,X0),X1) = X0
        | r1_tarski(k1_wellord1(sK2,X0),X1) )
    | ~ spl12_3
    | ~ spl12_10 ),
    inference(resolution,[],[f207,f115])).

fof(f725,plain,
    ( spl12_63
    | spl12_62
    | ~ spl12_3
    | ~ spl12_59 ),
    inference(avatar_split_clause,[],[f712,f677,f103,f719,f723])).

fof(f712,plain,
    ( sK0 = sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0))
    | r2_hidden(sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)),k1_wellord1(sK2,sK0))
    | ~ spl12_3
    | ~ spl12_59 ),
    inference(resolution,[],[f678,f157])).

fof(f157,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | X0 = X1
        | r2_hidden(X0,k1_wellord1(sK2,X1)) )
    | ~ spl12_3 ),
    inference(resolution,[],[f90,f104])).

fof(f90,plain,(
    ! [X4,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | r2_hidden(X4,k1_wellord1(X0,X1)) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f678,plain,
    ( r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)),sK0),sK2)
    | ~ spl12_59 ),
    inference(avatar_component_clause,[],[f677])).

fof(f679,plain,
    ( spl12_59
    | spl12_54
    | ~ spl12_37
    | ~ spl12_30
    | spl12_55 ),
    inference(avatar_split_clause,[],[f674,f659,f419,f503,f656,f677])).

fof(f674,plain,
    ( ~ r2_hidden(sK0,k3_relat_1(sK2))
    | sK0 = sK1
    | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)),sK0),sK2)
    | ~ spl12_30
    | spl12_55 ),
    inference(resolution,[],[f660,f420])).

fof(f660,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),sK2)
    | spl12_55 ),
    inference(avatar_component_clause,[],[f659])).

fof(f665,plain,
    ( spl12_28
    | spl12_56
    | ~ spl12_3
    | ~ spl12_44 ),
    inference(avatar_split_clause,[],[f648,f566,f103,f663,f402])).

fof(f566,plain,
    ( spl12_44
  <=> sK1 = sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_44])])).

fof(f648,plain,
    ( r2_hidden(k4_tarski(sK1,sK0),sK2)
    | r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ spl12_3
    | ~ spl12_44 ),
    inference(superposition,[],[f115,f567])).

fof(f567,plain,
    ( sK1 = sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ spl12_44 ),
    inference(avatar_component_clause,[],[f566])).

fof(f623,plain,
    ( spl12_1
    | ~ spl12_28 ),
    inference(avatar_split_clause,[],[f617,f402,f95])).

fof(f617,plain,
    ( r3_xboole_0(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ spl12_28 ),
    inference(resolution,[],[f403,f86])).

fof(f403,plain,
    ( r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ spl12_28 ),
    inference(avatar_component_clause,[],[f402])).

fof(f572,plain,
    ( spl12_45
    | spl12_44
    | ~ spl12_3
    | ~ spl12_39 ),
    inference(avatar_split_clause,[],[f555,f540,f103,f566,f570])).

fof(f555,plain,
    ( sK1 = sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | r2_hidden(sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK1))
    | ~ spl12_3
    | ~ spl12_39 ),
    inference(resolution,[],[f541,f157])).

fof(f541,plain,
    ( r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),sK1),sK2)
    | ~ spl12_39 ),
    inference(avatar_component_clause,[],[f540])).

fof(f523,plain,
    ( spl12_1
    | ~ spl12_4
    | spl12_37 ),
    inference(avatar_contradiction_clause,[],[f522])).

fof(f522,plain,
    ( $false
    | spl12_1
    | ~ spl12_4
    | spl12_37 ),
    inference(subsumption_resolution,[],[f96,f521])).

fof(f521,plain,
    ( ! [X3] : r3_xboole_0(k1_wellord1(sK2,sK0),X3)
    | ~ spl12_4
    | spl12_37 ),
    inference(resolution,[],[f509,f86])).

fof(f509,plain,
    ( ! [X0] : r1_tarski(k1_wellord1(sK2,sK0),X0)
    | ~ spl12_4
    | spl12_37 ),
    inference(resolution,[],[f504,f121])).

fof(f121,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,k3_relat_1(sK2))
        | r1_tarski(k1_wellord1(sK2,X0),X1) )
    | ~ spl12_4 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl12_4
  <=> ! [X1,X0] :
        ( r1_tarski(k1_wellord1(sK2,X0),X1)
        | r2_hidden(X0,k3_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).

fof(f504,plain,
    ( ~ r2_hidden(sK0,k3_relat_1(sK2))
    | spl12_37 ),
    inference(avatar_component_clause,[],[f503])).

fof(f436,plain,
    ( spl12_1
    | ~ spl12_4
    | spl12_29 ),
    inference(avatar_contradiction_clause,[],[f435])).

fof(f435,plain,
    ( $false
    | spl12_1
    | ~ spl12_4
    | spl12_29 ),
    inference(subsumption_resolution,[],[f96,f433])).

fof(f433,plain,
    ( ! [X2] : r3_xboole_0(X2,k1_wellord1(sK2,sK1))
    | ~ spl12_4
    | spl12_29 ),
    inference(resolution,[],[f422,f87])).

fof(f422,plain,
    ( ! [X0] : r1_tarski(k1_wellord1(sK2,sK1),X0)
    | ~ spl12_4
    | spl12_29 ),
    inference(resolution,[],[f417,f121])).

fof(f417,plain,
    ( ~ r2_hidden(sK1,k3_relat_1(sK2))
    | spl12_29 ),
    inference(avatar_component_clause,[],[f416])).

fof(f416,plain,
    ( spl12_29
  <=> r2_hidden(sK1,k3_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_29])])).

fof(f421,plain,
    ( ~ spl12_29
    | spl12_30
    | spl12_1
    | ~ spl12_3
    | ~ spl12_14
    | ~ spl12_20 ),
    inference(avatar_split_clause,[],[f413,f314,f245,f103,f95,f419,f416])).

fof(f314,plain,
    ( spl12_20
  <=> ! [X1,X0] :
        ( r2_hidden(k4_tarski(X0,X1),sK2)
        | r2_hidden(k4_tarski(X1,X0),sK2)
        | ~ r2_hidden(X0,k3_relat_1(sK2))
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | X0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_20])])).

fof(f413,plain,
    ( ! [X0] :
        ( sK1 = X0
        | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)),X0),sK2)
        | r2_hidden(k4_tarski(X0,sK1),sK2)
        | ~ r2_hidden(sK1,k3_relat_1(sK2))
        | ~ r2_hidden(X0,k3_relat_1(sK2)) )
    | spl12_1
    | ~ spl12_3
    | ~ spl12_14
    | ~ spl12_20 ),
    inference(resolution,[],[f406,f96])).

fof(f406,plain,
    ( ! [X6,X4,X5] :
        ( r3_xboole_0(X6,k1_wellord1(sK2,X5))
        | X4 = X5
        | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,X5),X6),X4),sK2)
        | r2_hidden(k4_tarski(X4,X5),sK2)
        | ~ r2_hidden(X5,k3_relat_1(sK2))
        | ~ r2_hidden(X4,k3_relat_1(sK2)) )
    | ~ spl12_3
    | ~ spl12_14
    | ~ spl12_20 ),
    inference(resolution,[],[f348,f87])).

fof(f348,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k1_wellord1(sK2,X0),X2)
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | X0 = X1
        | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,X0),X2),X1),sK2)
        | r2_hidden(k4_tarski(X1,X0),sK2)
        | ~ r2_hidden(X0,k3_relat_1(sK2)) )
    | ~ spl12_3
    | ~ spl12_14
    | ~ spl12_20 ),
    inference(resolution,[],[f329,f115])).

fof(f329,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(k4_tarski(X2,X1),sK2)
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | ~ r2_hidden(X0,k3_relat_1(sK2))
        | X0 = X1
        | r2_hidden(k4_tarski(X2,X0),sK2)
        | r2_hidden(k4_tarski(X0,X1),sK2) )
    | ~ spl12_14
    | ~ spl12_20 ),
    inference(resolution,[],[f315,f246])).

fof(f315,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,X1),sK2)
        | r2_hidden(k4_tarski(X1,X0),sK2)
        | ~ r2_hidden(X0,k3_relat_1(sK2))
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | X0 = X1 )
    | ~ spl12_20 ),
    inference(avatar_component_clause,[],[f314])).

fof(f328,plain,
    ( ~ spl12_3
    | ~ spl12_2
    | spl12_19 ),
    inference(avatar_split_clause,[],[f319,f311,f99,f103])).

fof(f99,plain,
    ( spl12_2
  <=> v2_wellord1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f311,plain,
    ( spl12_19
  <=> v6_relat_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_19])])).

fof(f319,plain,
    ( ~ v2_wellord1(sK2)
    | ~ v1_relat_1(sK2)
    | spl12_19 ),
    inference(resolution,[],[f312,f72])).

fof(f72,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

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
    inference(flattening,[],[f39])).

fof(f39,plain,(
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

fof(f312,plain,
    ( ~ v6_relat_2(sK2)
    | spl12_19 ),
    inference(avatar_component_clause,[],[f311])).

fof(f316,plain,
    ( ~ spl12_19
    | spl12_20
    | ~ spl12_3 ),
    inference(avatar_split_clause,[],[f309,f103,f314,f311])).

fof(f309,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,X1),sK2)
        | X0 = X1
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | ~ r2_hidden(X0,k3_relat_1(sK2))
        | ~ v6_relat_2(sK2)
        | r2_hidden(k4_tarski(X1,X0),sK2) )
    | ~ spl12_3 ),
    inference(resolution,[],[f59,f104])).

fof(f59,plain,(
    ! [X4,X0,X3] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X3,X4),X0)
      | X3 = X4
      | ~ r2_hidden(X4,k3_relat_1(X0))
      | ~ r2_hidden(X3,k3_relat_1(X0))
      | ~ v6_relat_2(X0)
      | r2_hidden(k4_tarski(X4,X3),X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f32,f33])).

fof(f33,plain,(
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

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f31,plain,(
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

fof(f264,plain,
    ( ~ spl12_3
    | ~ spl12_2
    | spl12_13 ),
    inference(avatar_split_clause,[],[f251,f242,f99,f103])).

fof(f242,plain,
    ( spl12_13
  <=> v8_relat_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_13])])).

fof(f251,plain,
    ( ~ v2_wellord1(sK2)
    | ~ v1_relat_1(sK2)
    | spl12_13 ),
    inference(resolution,[],[f243,f70])).

fof(f70,plain,(
    ! [X0] :
      ( v8_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f243,plain,
    ( ~ v8_relat_2(sK2)
    | spl12_13 ),
    inference(avatar_component_clause,[],[f242])).

fof(f247,plain,
    ( ~ spl12_13
    | spl12_14
    | ~ spl12_3 ),
    inference(avatar_split_clause,[],[f240,f103,f245,f242])).

fof(f240,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | ~ r2_hidden(k4_tarski(X2,X0),sK2)
        | ~ v8_relat_2(sK2)
        | r2_hidden(k4_tarski(X2,X1),sK2) )
    | ~ spl12_3 ),
    inference(resolution,[],[f65,f104])).

fof(f65,plain,(
    ! [X6,X4,X0,X5] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(k4_tarski(X4,X5),X0)
      | ~ v8_relat_2(X0)
      | r2_hidden(k4_tarski(X4,X6),X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f36,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1,X2,X3] :
          ( ~ r2_hidden(k4_tarski(X1,X3),X0)
          & r2_hidden(k4_tarski(X2,X3),X0)
          & r2_hidden(k4_tarski(X1,X2),X0) )
     => ( ~ r2_hidden(k4_tarski(sK7(X0),sK9(X0)),X0)
        & r2_hidden(k4_tarski(sK8(X0),sK9(X0)),X0)
        & r2_hidden(k4_tarski(sK7(X0),sK8(X0)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f35,plain,(
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

fof(f221,plain,
    ( ~ spl12_3
    | ~ spl12_2
    | spl12_9 ),
    inference(avatar_split_clause,[],[f211,f203,f99,f103])).

fof(f203,plain,
    ( spl12_9
  <=> v4_relat_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_9])])).

fof(f211,plain,
    ( ~ v2_wellord1(sK2)
    | ~ v1_relat_1(sK2)
    | spl12_9 ),
    inference(resolution,[],[f204,f71])).

fof(f71,plain,(
    ! [X0] :
      ( v4_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f204,plain,
    ( ~ v4_relat_2(sK2)
    | spl12_9 ),
    inference(avatar_component_clause,[],[f203])).

fof(f208,plain,
    ( ~ spl12_9
    | spl12_10
    | ~ spl12_3 ),
    inference(avatar_split_clause,[],[f201,f103,f206,f203])).

fof(f201,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | ~ r2_hidden(k4_tarski(X1,X0),sK2)
        | ~ v4_relat_2(sK2)
        | X0 = X1 )
    | ~ spl12_3 ),
    inference(resolution,[],[f55,f104])).

fof(f55,plain,(
    ! [X4,X0,X3] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X4,X3),X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ v4_relat_2(X0)
      | X3 = X4 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f28,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & r2_hidden(k4_tarski(X2,X1),X0)
          & r2_hidden(k4_tarski(X1,X2),X0) )
     => ( sK3(X0) != sK4(X0)
        & r2_hidden(k4_tarski(sK4(X0),sK3(X0)),X0)
        & r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f27,plain,(
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

fof(f122,plain,
    ( ~ spl12_3
    | spl12_4
    | ~ spl12_3 ),
    inference(avatar_split_clause,[],[f116,f103,f120,f103])).

fof(f116,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_wellord1(sK2,X0),X1)
        | r2_hidden(X0,k3_relat_1(sK2))
        | ~ v1_relat_1(sK2) )
    | ~ spl12_3 ),
    inference(resolution,[],[f115,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k3_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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

fof(f105,plain,(
    spl12_3 ),
    inference(avatar_split_clause,[],[f52,f103])).

fof(f52,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ r3_xboole_0(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    & v2_wellord1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f25])).

fof(f25,plain,
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

fof(f101,plain,(
    spl12_2 ),
    inference(avatar_split_clause,[],[f53,f99])).

fof(f53,plain,(
    v2_wellord1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f97,plain,(
    ~ spl12_1 ),
    inference(avatar_split_clause,[],[f54,f95])).

fof(f54,plain,(
    ~ r3_xboole_0(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:26:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.49  % (8069)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.49  % (8077)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.51  % (8061)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.51  % (8053)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.51  % (8061)Refutation not found, incomplete strategy% (8061)------------------------------
% 0.22/0.51  % (8061)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (8061)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (8061)Memory used [KB]: 10746
% 0.22/0.51  % (8061)Time elapsed: 0.107 s
% 0.22/0.51  % (8061)------------------------------
% 0.22/0.51  % (8061)------------------------------
% 0.22/0.52  % (8063)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.52  % (8059)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.52  % (8064)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (8060)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.53  % (8073)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.53  % (8078)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.53  % (8051)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (8074)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.53  % (8057)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.53  % (8055)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (8052)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.36/0.53  % (8065)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.36/0.53  % (8054)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.36/0.53  % (8052)Refutation not found, incomplete strategy% (8052)------------------------------
% 1.36/0.53  % (8052)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.53  % (8052)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.53  
% 1.36/0.53  % (8052)Memory used [KB]: 10746
% 1.36/0.53  % (8052)Time elapsed: 0.126 s
% 1.36/0.53  % (8052)------------------------------
% 1.36/0.53  % (8052)------------------------------
% 1.36/0.54  % (8068)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.36/0.54  % (8072)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.36/0.54  % (8066)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.36/0.54  % (8072)Refutation not found, incomplete strategy% (8072)------------------------------
% 1.36/0.54  % (8072)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (8072)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (8072)Memory used [KB]: 10746
% 1.36/0.54  % (8072)Time elapsed: 0.092 s
% 1.36/0.54  % (8072)------------------------------
% 1.36/0.54  % (8072)------------------------------
% 1.36/0.54  % (8058)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.36/0.54  % (8070)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.36/0.54  % (8062)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.36/0.54  % (8050)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.36/0.54  % (8060)Refutation not found, incomplete strategy% (8060)------------------------------
% 1.36/0.54  % (8060)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (8060)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (8060)Memory used [KB]: 10618
% 1.36/0.54  % (8060)Time elapsed: 0.139 s
% 1.36/0.54  % (8060)------------------------------
% 1.36/0.54  % (8060)------------------------------
% 1.36/0.54  % (8076)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.36/0.55  % (8079)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.36/0.55  % (8075)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.36/0.55  % (8067)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.52/0.55  % (8056)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.52/0.55  % (8071)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.52/0.56  % (8067)Refutation not found, incomplete strategy% (8067)------------------------------
% 1.52/0.56  % (8067)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.56  % (8067)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.56  
% 1.52/0.56  % (8067)Memory used [KB]: 10618
% 1.52/0.56  % (8067)Time elapsed: 0.152 s
% 1.52/0.56  % (8067)------------------------------
% 1.52/0.56  % (8067)------------------------------
% 1.52/0.57  % (8069)Refutation found. Thanks to Tanya!
% 1.52/0.57  % SZS status Theorem for theBenchmark
% 1.52/0.58  % SZS output start Proof for theBenchmark
% 1.52/0.58  fof(f1014,plain,(
% 1.52/0.58    $false),
% 1.52/0.58    inference(avatar_sat_refutation,[],[f97,f101,f105,f122,f208,f221,f247,f264,f316,f328,f421,f436,f523,f572,f623,f665,f679,f725,f747,f763,f775,f834,f906,f914,f939,f977,f1013])).
% 1.52/0.58  fof(f1013,plain,(
% 1.52/0.58    spl12_39 | spl12_1 | ~spl12_3 | ~spl12_14 | ~spl12_55),
% 1.52/0.58    inference(avatar_split_clause,[],[f1011,f659,f245,f103,f95,f540])).
% 1.52/0.58  fof(f540,plain,(
% 1.52/0.58    spl12_39 <=> r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),sK1),sK2)),
% 1.52/0.58    introduced(avatar_definition,[new_symbols(naming,[spl12_39])])).
% 1.52/0.58  fof(f95,plain,(
% 1.52/0.58    spl12_1 <=> r3_xboole_0(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))),
% 1.52/0.58    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).
% 1.52/0.58  fof(f103,plain,(
% 1.52/0.58    spl12_3 <=> v1_relat_1(sK2)),
% 1.52/0.58    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).
% 1.52/0.58  fof(f245,plain,(
% 1.52/0.58    spl12_14 <=> ! [X1,X0,X2] : (~r2_hidden(k4_tarski(X0,X1),sK2) | r2_hidden(k4_tarski(X2,X1),sK2) | ~r2_hidden(k4_tarski(X2,X0),sK2))),
% 1.52/0.58    introduced(avatar_definition,[new_symbols(naming,[spl12_14])])).
% 1.52/0.58  fof(f659,plain,(
% 1.52/0.58    spl12_55 <=> r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 1.52/0.58    introduced(avatar_definition,[new_symbols(naming,[spl12_55])])).
% 1.52/0.58  fof(f1011,plain,(
% 1.52/0.58    r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),sK1),sK2) | (spl12_1 | ~spl12_3 | ~spl12_14 | ~spl12_55)),
% 1.52/0.58    inference(resolution,[],[f1009,f96])).
% 1.52/0.58  fof(f96,plain,(
% 1.52/0.58    ~r3_xboole_0(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | spl12_1),
% 1.52/0.58    inference(avatar_component_clause,[],[f95])).
% 1.52/0.58  fof(f1009,plain,(
% 1.52/0.58    ( ! [X3] : (r3_xboole_0(k1_wellord1(sK2,sK0),X3) | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK0),X3),sK1),sK2)) ) | (~spl12_3 | ~spl12_14 | ~spl12_55)),
% 1.52/0.58    inference(resolution,[],[f1005,f86])).
% 1.52/0.58  fof(f86,plain,(
% 1.52/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r3_xboole_0(X0,X1)) )),
% 1.52/0.58    inference(cnf_transformation,[],[f51])).
% 1.52/0.58  fof(f51,plain,(
% 1.52/0.58    ! [X0,X1] : ((r3_xboole_0(X0,X1) | (~r1_tarski(X1,X0) & ~r1_tarski(X0,X1))) & (r1_tarski(X1,X0) | r1_tarski(X0,X1) | ~r3_xboole_0(X0,X1)))),
% 1.52/0.58    inference(flattening,[],[f50])).
% 1.52/0.58  fof(f50,plain,(
% 1.52/0.58    ! [X0,X1] : ((r3_xboole_0(X0,X1) | (~r1_tarski(X1,X0) & ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) | r1_tarski(X0,X1)) | ~r3_xboole_0(X0,X1)))),
% 1.52/0.58    inference(nnf_transformation,[],[f2])).
% 1.52/0.58  fof(f2,axiom,(
% 1.52/0.58    ! [X0,X1] : (r3_xboole_0(X0,X1) <=> (r1_tarski(X1,X0) | r1_tarski(X0,X1)))),
% 1.52/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_xboole_0)).
% 1.52/0.58  fof(f1005,plain,(
% 1.52/0.58    ( ! [X3] : (r1_tarski(k1_wellord1(sK2,sK0),X3) | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK0),X3),sK1),sK2)) ) | (~spl12_3 | ~spl12_14 | ~spl12_55)),
% 1.52/0.58    inference(resolution,[],[f783,f115])).
% 1.52/0.58  fof(f115,plain,(
% 1.52/0.58    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,X0),X1),X0),sK2) | r1_tarski(k1_wellord1(sK2,X0),X1)) ) | ~spl12_3),
% 1.52/0.58    inference(resolution,[],[f114,f83])).
% 1.52/0.58  fof(f83,plain,(
% 1.52/0.58    ( ! [X0,X1] : (r2_hidden(sK11(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.52/0.58    inference(cnf_transformation,[],[f49])).
% 1.52/0.58  fof(f49,plain,(
% 1.52/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK11(X0,X1),X1) & r2_hidden(sK11(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.52/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f47,f48])).
% 1.52/0.58  fof(f48,plain,(
% 1.52/0.58    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK11(X0,X1),X1) & r2_hidden(sK11(X0,X1),X0)))),
% 1.52/0.58    introduced(choice_axiom,[])).
% 1.52/0.58  fof(f47,plain,(
% 1.52/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.52/0.58    inference(rectify,[],[f46])).
% 1.52/0.58  fof(f46,plain,(
% 1.52/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.52/0.58    inference(nnf_transformation,[],[f22])).
% 1.52/0.58  fof(f22,plain,(
% 1.52/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.52/0.58    inference(ennf_transformation,[],[f1])).
% 1.52/0.58  fof(f1,axiom,(
% 1.52/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.52/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.52/0.58  fof(f114,plain,(
% 1.52/0.58    ( ! [X0,X1] : (~r2_hidden(X0,k1_wellord1(sK2,X1)) | r2_hidden(k4_tarski(X0,X1),sK2)) ) | ~spl12_3),
% 1.52/0.58    inference(resolution,[],[f91,f104])).
% 1.52/0.58  fof(f104,plain,(
% 1.52/0.58    v1_relat_1(sK2) | ~spl12_3),
% 1.52/0.58    inference(avatar_component_clause,[],[f103])).
% 1.52/0.58  fof(f91,plain,(
% 1.52/0.58    ( ! [X4,X0,X1] : (~v1_relat_1(X0) | ~r2_hidden(X4,k1_wellord1(X0,X1)) | r2_hidden(k4_tarski(X4,X1),X0)) )),
% 1.52/0.58    inference(equality_resolution,[],[f76])).
% 1.52/0.58  fof(f76,plain,(
% 1.52/0.58    ( ! [X4,X2,X0,X1] : (r2_hidden(k4_tarski(X4,X1),X0) | ~r2_hidden(X4,X2) | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 1.52/0.58    inference(cnf_transformation,[],[f45])).
% 1.52/0.58  fof(f45,plain,(
% 1.52/0.58    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK10(X0,X1,X2),X1),X0) | sK10(X0,X1,X2) = X1 | ~r2_hidden(sK10(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK10(X0,X1,X2),X1),X0) & sK10(X0,X1,X2) != X1) | r2_hidden(sK10(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 1.52/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f43,f44])).
% 1.52/0.58  fof(f44,plain,(
% 1.52/0.58    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2))) => ((~r2_hidden(k4_tarski(sK10(X0,X1,X2),X1),X0) | sK10(X0,X1,X2) = X1 | ~r2_hidden(sK10(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK10(X0,X1,X2),X1),X0) & sK10(X0,X1,X2) != X1) | r2_hidden(sK10(X0,X1,X2),X2))))),
% 1.52/0.58    introduced(choice_axiom,[])).
% 1.52/0.58  fof(f43,plain,(
% 1.52/0.58    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 1.52/0.58    inference(rectify,[],[f42])).
% 1.52/0.58  fof(f42,plain,(
% 1.52/0.58    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 1.52/0.58    inference(flattening,[],[f41])).
% 1.52/0.58  fof(f41,plain,(
% 1.52/0.58    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 1.52/0.58    inference(nnf_transformation,[],[f21])).
% 1.52/0.58  fof(f21,plain,(
% 1.52/0.58    ! [X0] : (! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))) | ~v1_relat_1(X0))),
% 1.52/0.58    inference(ennf_transformation,[],[f5])).
% 1.52/0.58  fof(f5,axiom,(
% 1.52/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))))),
% 1.52/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).
% 1.52/0.58  fof(f783,plain,(
% 1.52/0.58    ( ! [X1] : (~r2_hidden(k4_tarski(X1,sK0),sK2) | r2_hidden(k4_tarski(X1,sK1),sK2)) ) | (~spl12_14 | ~spl12_55)),
% 1.52/0.58    inference(resolution,[],[f748,f246])).
% 1.52/0.58  fof(f246,plain,(
% 1.52/0.58    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | r2_hidden(k4_tarski(X2,X1),sK2) | ~r2_hidden(k4_tarski(X2,X0),sK2)) ) | ~spl12_14),
% 1.52/0.58    inference(avatar_component_clause,[],[f245])).
% 1.52/0.58  fof(f748,plain,(
% 1.52/0.58    r2_hidden(k4_tarski(sK0,sK1),sK2) | ~spl12_55),
% 1.52/0.58    inference(avatar_component_clause,[],[f659])).
% 1.52/0.58  fof(f977,plain,(
% 1.52/0.58    spl12_72),
% 1.52/0.58    inference(avatar_contradiction_clause,[],[f974])).
% 1.52/0.58  fof(f974,plain,(
% 1.52/0.58    $false | spl12_72),
% 1.52/0.58    inference(resolution,[],[f938,f81])).
% 1.52/0.58  fof(f81,plain,(
% 1.52/0.58    ( ! [X0] : (r3_xboole_0(X0,X0)) )),
% 1.52/0.58    inference(cnf_transformation,[],[f12])).
% 1.52/0.58  fof(f12,plain,(
% 1.52/0.58    ! [X0] : r3_xboole_0(X0,X0)),
% 1.52/0.58    inference(rectify,[],[f3])).
% 1.52/0.58  fof(f3,axiom,(
% 1.52/0.58    ! [X0,X1] : r3_xboole_0(X0,X0)),
% 1.52/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_xboole_0)).
% 1.52/0.58  fof(f938,plain,(
% 1.52/0.58    ~r3_xboole_0(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0)) | spl12_72),
% 1.52/0.58    inference(avatar_component_clause,[],[f937])).
% 1.52/0.58  fof(f937,plain,(
% 1.52/0.58    spl12_72 <=> r3_xboole_0(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0))),
% 1.52/0.58    introduced(avatar_definition,[new_symbols(naming,[spl12_72])])).
% 1.52/0.58  fof(f939,plain,(
% 1.52/0.58    ~spl12_72 | spl12_1 | ~spl12_54),
% 1.52/0.58    inference(avatar_split_clause,[],[f916,f656,f95,f937])).
% 1.52/0.58  fof(f656,plain,(
% 1.52/0.58    spl12_54 <=> sK0 = sK1),
% 1.52/0.58    introduced(avatar_definition,[new_symbols(naming,[spl12_54])])).
% 1.52/0.58  fof(f916,plain,(
% 1.52/0.58    ~r3_xboole_0(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0)) | (spl12_1 | ~spl12_54)),
% 1.52/0.58    inference(superposition,[],[f96,f657])).
% 1.52/0.58  fof(f657,plain,(
% 1.52/0.58    sK0 = sK1 | ~spl12_54),
% 1.52/0.58    inference(avatar_component_clause,[],[f656])).
% 1.52/0.58  fof(f914,plain,(
% 1.52/0.58    ~spl12_37 | spl12_59 | spl12_54 | ~spl12_10 | ~spl12_30 | ~spl12_56),
% 1.52/0.58    inference(avatar_split_clause,[],[f682,f663,f419,f206,f656,f677,f503])).
% 1.52/0.58  fof(f503,plain,(
% 1.52/0.58    spl12_37 <=> r2_hidden(sK0,k3_relat_1(sK2))),
% 1.52/0.58    introduced(avatar_definition,[new_symbols(naming,[spl12_37])])).
% 1.52/0.58  fof(f677,plain,(
% 1.52/0.58    spl12_59 <=> r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)),sK0),sK2)),
% 1.52/0.58    introduced(avatar_definition,[new_symbols(naming,[spl12_59])])).
% 1.52/0.58  fof(f206,plain,(
% 1.52/0.58    spl12_10 <=> ! [X1,X0] : (~r2_hidden(k4_tarski(X0,X1),sK2) | X0 = X1 | ~r2_hidden(k4_tarski(X1,X0),sK2))),
% 1.52/0.58    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).
% 1.52/0.58  fof(f419,plain,(
% 1.52/0.58    spl12_30 <=> ! [X0] : (sK1 = X0 | ~r2_hidden(X0,k3_relat_1(sK2)) | r2_hidden(k4_tarski(X0,sK1),sK2) | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)),X0),sK2))),
% 1.52/0.58    introduced(avatar_definition,[new_symbols(naming,[spl12_30])])).
% 1.52/0.58  fof(f663,plain,(
% 1.52/0.58    spl12_56 <=> r2_hidden(k4_tarski(sK1,sK0),sK2)),
% 1.52/0.58    introduced(avatar_definition,[new_symbols(naming,[spl12_56])])).
% 1.52/0.58  fof(f682,plain,(
% 1.52/0.58    sK0 = sK1 | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)),sK0),sK2) | ~r2_hidden(sK0,k3_relat_1(sK2)) | (~spl12_10 | ~spl12_30 | ~spl12_56)),
% 1.52/0.58    inference(resolution,[],[f664,f449])).
% 1.52/0.58  fof(f449,plain,(
% 1.52/0.58    ( ! [X4] : (~r2_hidden(k4_tarski(sK1,X4),sK2) | sK1 = X4 | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)),X4),sK2) | ~r2_hidden(X4,k3_relat_1(sK2))) ) | (~spl12_10 | ~spl12_30)),
% 1.52/0.58    inference(duplicate_literal_removal,[],[f442])).
% 1.52/0.58  fof(f442,plain,(
% 1.52/0.58    ( ! [X4] : (~r2_hidden(X4,k3_relat_1(sK2)) | sK1 = X4 | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)),X4),sK2) | sK1 = X4 | ~r2_hidden(k4_tarski(sK1,X4),sK2)) ) | (~spl12_10 | ~spl12_30)),
% 1.52/0.58    inference(resolution,[],[f420,f207])).
% 1.52/0.58  fof(f207,plain,(
% 1.52/0.58    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | X0 = X1 | ~r2_hidden(k4_tarski(X1,X0),sK2)) ) | ~spl12_10),
% 1.52/0.58    inference(avatar_component_clause,[],[f206])).
% 1.52/0.58  fof(f420,plain,(
% 1.52/0.58    ( ! [X0] : (r2_hidden(k4_tarski(X0,sK1),sK2) | ~r2_hidden(X0,k3_relat_1(sK2)) | sK1 = X0 | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)),X0),sK2)) ) | ~spl12_30),
% 1.52/0.58    inference(avatar_component_clause,[],[f419])).
% 1.52/0.58  fof(f664,plain,(
% 1.52/0.58    r2_hidden(k4_tarski(sK1,sK0),sK2) | ~spl12_56),
% 1.52/0.58    inference(avatar_component_clause,[],[f663])).
% 1.52/0.58  fof(f906,plain,(
% 1.52/0.58    spl12_39 | spl12_1 | ~spl12_3 | ~spl12_14 | ~spl12_62),
% 1.52/0.58    inference(avatar_split_clause,[],[f904,f719,f245,f103,f95,f540])).
% 1.52/0.58  fof(f719,plain,(
% 1.52/0.58    spl12_62 <=> sK0 = sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0))),
% 1.52/0.58    introduced(avatar_definition,[new_symbols(naming,[spl12_62])])).
% 1.52/0.58  fof(f904,plain,(
% 1.52/0.58    r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),sK1),sK2) | (spl12_1 | ~spl12_3 | ~spl12_14 | ~spl12_62)),
% 1.52/0.58    inference(resolution,[],[f729,f96])).
% 1.52/0.58  fof(f729,plain,(
% 1.52/0.58    ( ! [X4] : (r3_xboole_0(k1_wellord1(sK2,sK0),X4) | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK0),X4),sK1),sK2)) ) | (spl12_1 | ~spl12_3 | ~spl12_14 | ~spl12_62)),
% 1.52/0.58    inference(superposition,[],[f276,f720])).
% 1.52/0.58  fof(f720,plain,(
% 1.52/0.58    sK0 = sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)) | ~spl12_62),
% 1.52/0.58    inference(avatar_component_clause,[],[f719])).
% 1.52/0.58  fof(f276,plain,(
% 1.52/0.58    ( ! [X3] : (r3_xboole_0(k1_wellord1(sK2,sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0))),X3) | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0))),X3),sK1),sK2)) ) | (spl12_1 | ~spl12_3 | ~spl12_14)),
% 1.52/0.58    inference(resolution,[],[f270,f86])).
% 1.52/0.58  fof(f270,plain,(
% 1.52/0.58    ( ! [X0] : (r1_tarski(k1_wellord1(sK2,sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0))),X0) | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0))),X0),sK1),sK2)) ) | (spl12_1 | ~spl12_3 | ~spl12_14)),
% 1.52/0.58    inference(resolution,[],[f268,f96])).
% 1.52/0.58  fof(f268,plain,(
% 1.52/0.58    ( ! [X6,X4,X5] : (r3_xboole_0(X5,k1_wellord1(sK2,X4)) | r1_tarski(k1_wellord1(sK2,sK11(k1_wellord1(sK2,X4),X5)),X6) | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK11(k1_wellord1(sK2,X4),X5)),X6),X4),sK2)) ) | (~spl12_3 | ~spl12_14)),
% 1.52/0.58    inference(resolution,[],[f266,f87])).
% 1.52/0.58  fof(f87,plain,(
% 1.52/0.58    ( ! [X0,X1] : (~r1_tarski(X1,X0) | r3_xboole_0(X0,X1)) )),
% 1.52/0.58    inference(cnf_transformation,[],[f51])).
% 1.52/0.58  fof(f266,plain,(
% 1.52/0.58    ( ! [X2,X0,X1] : (r1_tarski(k1_wellord1(sK2,X0),X1) | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK11(k1_wellord1(sK2,X0),X1)),X2),X0),sK2) | r1_tarski(k1_wellord1(sK2,sK11(k1_wellord1(sK2,X0),X1)),X2)) ) | (~spl12_3 | ~spl12_14)),
% 1.52/0.58    inference(resolution,[],[f265,f115])).
% 1.52/0.58  fof(f265,plain,(
% 1.52/0.58    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,sK11(k1_wellord1(sK2,X1),X2)),sK2) | r2_hidden(k4_tarski(X0,X1),sK2) | r1_tarski(k1_wellord1(sK2,X1),X2)) ) | (~spl12_3 | ~spl12_14)),
% 1.52/0.58    inference(resolution,[],[f246,f115])).
% 1.52/0.58  fof(f834,plain,(
% 1.52/0.58    spl12_28 | ~spl12_45),
% 1.52/0.58    inference(avatar_split_clause,[],[f830,f570,f402])).
% 1.52/0.58  fof(f402,plain,(
% 1.52/0.58    spl12_28 <=> r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))),
% 1.52/0.58    introduced(avatar_definition,[new_symbols(naming,[spl12_28])])).
% 1.52/0.58  fof(f570,plain,(
% 1.52/0.58    spl12_45 <=> r2_hidden(sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK1))),
% 1.52/0.58    introduced(avatar_definition,[new_symbols(naming,[spl12_45])])).
% 1.52/0.58  fof(f830,plain,(
% 1.52/0.58    r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | ~spl12_45),
% 1.52/0.58    inference(resolution,[],[f571,f84])).
% 1.52/0.58  fof(f84,plain,(
% 1.52/0.58    ( ! [X0,X1] : (~r2_hidden(sK11(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.52/0.58    inference(cnf_transformation,[],[f49])).
% 1.52/0.58  fof(f571,plain,(
% 1.52/0.58    r2_hidden(sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK1)) | ~spl12_45),
% 1.52/0.58    inference(avatar_component_clause,[],[f570])).
% 1.52/0.58  fof(f775,plain,(
% 1.52/0.58    spl12_1 | ~spl12_25),
% 1.52/0.58    inference(avatar_split_clause,[],[f773,f377,f95])).
% 1.52/0.58  fof(f377,plain,(
% 1.52/0.58    spl12_25 <=> r1_tarski(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0))),
% 1.52/0.58    introduced(avatar_definition,[new_symbols(naming,[spl12_25])])).
% 1.52/0.58  fof(f773,plain,(
% 1.52/0.58    r3_xboole_0(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | ~spl12_25),
% 1.52/0.58    inference(resolution,[],[f378,f87])).
% 1.52/0.58  fof(f378,plain,(
% 1.52/0.58    r1_tarski(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)) | ~spl12_25),
% 1.52/0.58    inference(avatar_component_clause,[],[f377])).
% 1.52/0.58  fof(f763,plain,(
% 1.52/0.58    spl12_25 | ~spl12_63),
% 1.52/0.58    inference(avatar_split_clause,[],[f759,f723,f377])).
% 1.52/0.58  fof(f723,plain,(
% 1.52/0.58    spl12_63 <=> r2_hidden(sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)),k1_wellord1(sK2,sK0))),
% 1.52/0.58    introduced(avatar_definition,[new_symbols(naming,[spl12_63])])).
% 1.52/0.58  fof(f759,plain,(
% 1.52/0.58    r1_tarski(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)) | ~spl12_63),
% 1.52/0.58    inference(resolution,[],[f724,f84])).
% 1.52/0.58  fof(f724,plain,(
% 1.52/0.58    r2_hidden(sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)),k1_wellord1(sK2,sK0)) | ~spl12_63),
% 1.52/0.58    inference(avatar_component_clause,[],[f723])).
% 1.52/0.58  fof(f747,plain,(
% 1.52/0.58    spl12_25 | spl12_54 | ~spl12_56 | ~spl12_3 | ~spl12_10 | ~spl12_62),
% 1.52/0.58    inference(avatar_split_clause,[],[f733,f719,f206,f103,f663,f656,f377])).
% 1.52/0.58  fof(f733,plain,(
% 1.52/0.58    ~r2_hidden(k4_tarski(sK1,sK0),sK2) | sK0 = sK1 | r1_tarski(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)) | (~spl12_3 | ~spl12_10 | ~spl12_62)),
% 1.52/0.58    inference(superposition,[],[f222,f720])).
% 1.52/0.58  fof(f222,plain,(
% 1.52/0.58    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,sK11(k1_wellord1(sK2,X0),X1)),sK2) | sK11(k1_wellord1(sK2,X0),X1) = X0 | r1_tarski(k1_wellord1(sK2,X0),X1)) ) | (~spl12_3 | ~spl12_10)),
% 1.52/0.58    inference(resolution,[],[f207,f115])).
% 1.52/0.58  fof(f725,plain,(
% 1.52/0.58    spl12_63 | spl12_62 | ~spl12_3 | ~spl12_59),
% 1.52/0.58    inference(avatar_split_clause,[],[f712,f677,f103,f719,f723])).
% 1.52/0.58  fof(f712,plain,(
% 1.52/0.58    sK0 = sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)) | r2_hidden(sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)),k1_wellord1(sK2,sK0)) | (~spl12_3 | ~spl12_59)),
% 1.52/0.58    inference(resolution,[],[f678,f157])).
% 1.52/0.58  fof(f157,plain,(
% 1.52/0.58    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | X0 = X1 | r2_hidden(X0,k1_wellord1(sK2,X1))) ) | ~spl12_3),
% 1.52/0.58    inference(resolution,[],[f90,f104])).
% 1.52/0.58  fof(f90,plain,(
% 1.52/0.58    ( ! [X4,X0,X1] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4 | r2_hidden(X4,k1_wellord1(X0,X1))) )),
% 1.52/0.58    inference(equality_resolution,[],[f77])).
% 1.52/0.58  fof(f77,plain,(
% 1.52/0.58    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4 | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 1.52/0.58    inference(cnf_transformation,[],[f45])).
% 1.52/0.58  fof(f678,plain,(
% 1.52/0.58    r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)),sK0),sK2) | ~spl12_59),
% 1.52/0.58    inference(avatar_component_clause,[],[f677])).
% 1.52/0.58  fof(f679,plain,(
% 1.52/0.58    spl12_59 | spl12_54 | ~spl12_37 | ~spl12_30 | spl12_55),
% 1.52/0.58    inference(avatar_split_clause,[],[f674,f659,f419,f503,f656,f677])).
% 1.52/0.58  fof(f674,plain,(
% 1.52/0.58    ~r2_hidden(sK0,k3_relat_1(sK2)) | sK0 = sK1 | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)),sK0),sK2) | (~spl12_30 | spl12_55)),
% 1.52/0.58    inference(resolution,[],[f660,f420])).
% 1.52/0.58  fof(f660,plain,(
% 1.52/0.58    ~r2_hidden(k4_tarski(sK0,sK1),sK2) | spl12_55),
% 1.52/0.58    inference(avatar_component_clause,[],[f659])).
% 1.52/0.58  fof(f665,plain,(
% 1.52/0.58    spl12_28 | spl12_56 | ~spl12_3 | ~spl12_44),
% 1.52/0.58    inference(avatar_split_clause,[],[f648,f566,f103,f663,f402])).
% 1.52/0.58  fof(f566,plain,(
% 1.52/0.58    spl12_44 <=> sK1 = sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))),
% 1.52/0.58    introduced(avatar_definition,[new_symbols(naming,[spl12_44])])).
% 1.52/0.58  fof(f648,plain,(
% 1.52/0.58    r2_hidden(k4_tarski(sK1,sK0),sK2) | r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | (~spl12_3 | ~spl12_44)),
% 1.52/0.58    inference(superposition,[],[f115,f567])).
% 1.52/0.58  fof(f567,plain,(
% 1.52/0.58    sK1 = sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | ~spl12_44),
% 1.52/0.58    inference(avatar_component_clause,[],[f566])).
% 1.52/0.58  fof(f623,plain,(
% 1.52/0.58    spl12_1 | ~spl12_28),
% 1.52/0.58    inference(avatar_split_clause,[],[f617,f402,f95])).
% 1.52/0.58  fof(f617,plain,(
% 1.52/0.58    r3_xboole_0(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | ~spl12_28),
% 1.52/0.58    inference(resolution,[],[f403,f86])).
% 1.52/0.58  fof(f403,plain,(
% 1.52/0.58    r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | ~spl12_28),
% 1.52/0.58    inference(avatar_component_clause,[],[f402])).
% 1.52/0.58  fof(f572,plain,(
% 1.52/0.58    spl12_45 | spl12_44 | ~spl12_3 | ~spl12_39),
% 1.52/0.58    inference(avatar_split_clause,[],[f555,f540,f103,f566,f570])).
% 1.52/0.58  fof(f555,plain,(
% 1.52/0.58    sK1 = sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | r2_hidden(sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK1)) | (~spl12_3 | ~spl12_39)),
% 1.52/0.58    inference(resolution,[],[f541,f157])).
% 1.52/0.58  fof(f541,plain,(
% 1.52/0.58    r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),sK1),sK2) | ~spl12_39),
% 1.52/0.58    inference(avatar_component_clause,[],[f540])).
% 1.52/0.58  fof(f523,plain,(
% 1.52/0.58    spl12_1 | ~spl12_4 | spl12_37),
% 1.52/0.58    inference(avatar_contradiction_clause,[],[f522])).
% 1.52/0.58  fof(f522,plain,(
% 1.52/0.58    $false | (spl12_1 | ~spl12_4 | spl12_37)),
% 1.52/0.58    inference(subsumption_resolution,[],[f96,f521])).
% 1.52/0.58  fof(f521,plain,(
% 1.52/0.58    ( ! [X3] : (r3_xboole_0(k1_wellord1(sK2,sK0),X3)) ) | (~spl12_4 | spl12_37)),
% 1.52/0.58    inference(resolution,[],[f509,f86])).
% 1.52/0.58  fof(f509,plain,(
% 1.52/0.58    ( ! [X0] : (r1_tarski(k1_wellord1(sK2,sK0),X0)) ) | (~spl12_4 | spl12_37)),
% 1.52/0.58    inference(resolution,[],[f504,f121])).
% 1.52/0.58  fof(f121,plain,(
% 1.52/0.58    ( ! [X0,X1] : (r2_hidden(X0,k3_relat_1(sK2)) | r1_tarski(k1_wellord1(sK2,X0),X1)) ) | ~spl12_4),
% 1.52/0.58    inference(avatar_component_clause,[],[f120])).
% 1.52/0.58  fof(f120,plain,(
% 1.52/0.58    spl12_4 <=> ! [X1,X0] : (r1_tarski(k1_wellord1(sK2,X0),X1) | r2_hidden(X0,k3_relat_1(sK2)))),
% 1.52/0.58    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).
% 1.52/0.58  fof(f504,plain,(
% 1.52/0.58    ~r2_hidden(sK0,k3_relat_1(sK2)) | spl12_37),
% 1.52/0.58    inference(avatar_component_clause,[],[f503])).
% 1.52/0.58  fof(f436,plain,(
% 1.52/0.58    spl12_1 | ~spl12_4 | spl12_29),
% 1.52/0.58    inference(avatar_contradiction_clause,[],[f435])).
% 1.52/0.58  fof(f435,plain,(
% 1.52/0.58    $false | (spl12_1 | ~spl12_4 | spl12_29)),
% 1.52/0.58    inference(subsumption_resolution,[],[f96,f433])).
% 1.52/0.58  fof(f433,plain,(
% 1.52/0.58    ( ! [X2] : (r3_xboole_0(X2,k1_wellord1(sK2,sK1))) ) | (~spl12_4 | spl12_29)),
% 1.52/0.58    inference(resolution,[],[f422,f87])).
% 1.52/0.58  fof(f422,plain,(
% 1.52/0.58    ( ! [X0] : (r1_tarski(k1_wellord1(sK2,sK1),X0)) ) | (~spl12_4 | spl12_29)),
% 1.52/0.58    inference(resolution,[],[f417,f121])).
% 1.52/0.58  fof(f417,plain,(
% 1.52/0.58    ~r2_hidden(sK1,k3_relat_1(sK2)) | spl12_29),
% 1.52/0.58    inference(avatar_component_clause,[],[f416])).
% 1.52/0.58  fof(f416,plain,(
% 1.52/0.58    spl12_29 <=> r2_hidden(sK1,k3_relat_1(sK2))),
% 1.52/0.58    introduced(avatar_definition,[new_symbols(naming,[spl12_29])])).
% 1.52/0.58  fof(f421,plain,(
% 1.52/0.58    ~spl12_29 | spl12_30 | spl12_1 | ~spl12_3 | ~spl12_14 | ~spl12_20),
% 1.52/0.58    inference(avatar_split_clause,[],[f413,f314,f245,f103,f95,f419,f416])).
% 1.52/0.58  fof(f314,plain,(
% 1.52/0.58    spl12_20 <=> ! [X1,X0] : (r2_hidden(k4_tarski(X0,X1),sK2) | r2_hidden(k4_tarski(X1,X0),sK2) | ~r2_hidden(X0,k3_relat_1(sK2)) | ~r2_hidden(X1,k3_relat_1(sK2)) | X0 = X1)),
% 1.52/0.58    introduced(avatar_definition,[new_symbols(naming,[spl12_20])])).
% 1.52/0.58  fof(f413,plain,(
% 1.52/0.58    ( ! [X0] : (sK1 = X0 | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,sK1),k1_wellord1(sK2,sK0)),X0),sK2) | r2_hidden(k4_tarski(X0,sK1),sK2) | ~r2_hidden(sK1,k3_relat_1(sK2)) | ~r2_hidden(X0,k3_relat_1(sK2))) ) | (spl12_1 | ~spl12_3 | ~spl12_14 | ~spl12_20)),
% 1.52/0.58    inference(resolution,[],[f406,f96])).
% 1.52/0.58  fof(f406,plain,(
% 1.52/0.58    ( ! [X6,X4,X5] : (r3_xboole_0(X6,k1_wellord1(sK2,X5)) | X4 = X5 | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,X5),X6),X4),sK2) | r2_hidden(k4_tarski(X4,X5),sK2) | ~r2_hidden(X5,k3_relat_1(sK2)) | ~r2_hidden(X4,k3_relat_1(sK2))) ) | (~spl12_3 | ~spl12_14 | ~spl12_20)),
% 1.52/0.58    inference(resolution,[],[f348,f87])).
% 1.52/0.58  fof(f348,plain,(
% 1.52/0.58    ( ! [X2,X0,X1] : (r1_tarski(k1_wellord1(sK2,X0),X2) | ~r2_hidden(X1,k3_relat_1(sK2)) | X0 = X1 | r2_hidden(k4_tarski(sK11(k1_wellord1(sK2,X0),X2),X1),sK2) | r2_hidden(k4_tarski(X1,X0),sK2) | ~r2_hidden(X0,k3_relat_1(sK2))) ) | (~spl12_3 | ~spl12_14 | ~spl12_20)),
% 1.52/0.58    inference(resolution,[],[f329,f115])).
% 1.52/0.58  fof(f329,plain,(
% 1.52/0.58    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X2,X1),sK2) | ~r2_hidden(X1,k3_relat_1(sK2)) | ~r2_hidden(X0,k3_relat_1(sK2)) | X0 = X1 | r2_hidden(k4_tarski(X2,X0),sK2) | r2_hidden(k4_tarski(X0,X1),sK2)) ) | (~spl12_14 | ~spl12_20)),
% 1.52/0.58    inference(resolution,[],[f315,f246])).
% 1.52/0.58  fof(f315,plain,(
% 1.52/0.58    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,X1),sK2) | r2_hidden(k4_tarski(X1,X0),sK2) | ~r2_hidden(X0,k3_relat_1(sK2)) | ~r2_hidden(X1,k3_relat_1(sK2)) | X0 = X1) ) | ~spl12_20),
% 1.52/0.58    inference(avatar_component_clause,[],[f314])).
% 1.52/0.58  fof(f328,plain,(
% 1.52/0.58    ~spl12_3 | ~spl12_2 | spl12_19),
% 1.52/0.58    inference(avatar_split_clause,[],[f319,f311,f99,f103])).
% 1.52/0.58  fof(f99,plain,(
% 1.52/0.58    spl12_2 <=> v2_wellord1(sK2)),
% 1.52/0.58    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).
% 1.52/0.58  fof(f311,plain,(
% 1.52/0.58    spl12_19 <=> v6_relat_2(sK2)),
% 1.52/0.58    introduced(avatar_definition,[new_symbols(naming,[spl12_19])])).
% 1.52/0.58  fof(f319,plain,(
% 1.52/0.58    ~v2_wellord1(sK2) | ~v1_relat_1(sK2) | spl12_19),
% 1.52/0.58    inference(resolution,[],[f312,f72])).
% 1.52/0.58  fof(f72,plain,(
% 1.52/0.58    ( ! [X0] : (v6_relat_2(X0) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 1.52/0.58    inference(cnf_transformation,[],[f40])).
% 1.52/0.59  fof(f40,plain,(
% 1.52/0.59    ! [X0] : (((v2_wellord1(X0) | ~v1_wellord1(X0) | ~v6_relat_2(X0) | ~v4_relat_2(X0) | ~v8_relat_2(X0) | ~v1_relat_2(X0)) & ((v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0)) | ~v2_wellord1(X0))) | ~v1_relat_1(X0))),
% 1.52/0.59    inference(flattening,[],[f39])).
% 1.52/0.59  fof(f39,plain,(
% 1.52/0.59    ! [X0] : (((v2_wellord1(X0) | (~v1_wellord1(X0) | ~v6_relat_2(X0) | ~v4_relat_2(X0) | ~v8_relat_2(X0) | ~v1_relat_2(X0))) & ((v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0)) | ~v2_wellord1(X0))) | ~v1_relat_1(X0))),
% 1.52/0.59    inference(nnf_transformation,[],[f20])).
% 1.52/0.59  fof(f20,plain,(
% 1.52/0.59    ! [X0] : ((v2_wellord1(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0))) | ~v1_relat_1(X0))),
% 1.52/0.59    inference(ennf_transformation,[],[f6])).
% 1.52/0.59  fof(f6,axiom,(
% 1.52/0.59    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0))))),
% 1.52/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_wellord1)).
% 1.52/0.59  fof(f312,plain,(
% 1.52/0.59    ~v6_relat_2(sK2) | spl12_19),
% 1.52/0.59    inference(avatar_component_clause,[],[f311])).
% 1.52/0.59  fof(f316,plain,(
% 1.52/0.59    ~spl12_19 | spl12_20 | ~spl12_3),
% 1.52/0.59    inference(avatar_split_clause,[],[f309,f103,f314,f311])).
% 1.52/0.59  fof(f309,plain,(
% 1.52/0.59    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,X1),sK2) | X0 = X1 | ~r2_hidden(X1,k3_relat_1(sK2)) | ~r2_hidden(X0,k3_relat_1(sK2)) | ~v6_relat_2(sK2) | r2_hidden(k4_tarski(X1,X0),sK2)) ) | ~spl12_3),
% 1.52/0.59    inference(resolution,[],[f59,f104])).
% 1.52/0.59  fof(f59,plain,(
% 1.52/0.59    ( ! [X4,X0,X3] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(X3,X4),X0) | X3 = X4 | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0)) | ~v6_relat_2(X0) | r2_hidden(k4_tarski(X4,X3),X0)) )),
% 1.52/0.59    inference(cnf_transformation,[],[f34])).
% 1.52/0.59  fof(f34,plain,(
% 1.52/0.59    ! [X0] : (((v6_relat_2(X0) | (~r2_hidden(k4_tarski(sK6(X0),sK5(X0)),X0) & ~r2_hidden(k4_tarski(sK5(X0),sK6(X0)),X0) & sK5(X0) != sK6(X0) & r2_hidden(sK6(X0),k3_relat_1(X0)) & r2_hidden(sK5(X0),k3_relat_1(X0)))) & (! [X3,X4] : (r2_hidden(k4_tarski(X4,X3),X0) | r2_hidden(k4_tarski(X3,X4),X0) | X3 = X4 | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0))) | ~v6_relat_2(X0))) | ~v1_relat_1(X0))),
% 1.52/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f32,f33])).
% 1.52/0.59  fof(f33,plain,(
% 1.52/0.59    ! [X0] : (? [X1,X2] : (~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0))) => (~r2_hidden(k4_tarski(sK6(X0),sK5(X0)),X0) & ~r2_hidden(k4_tarski(sK5(X0),sK6(X0)),X0) & sK5(X0) != sK6(X0) & r2_hidden(sK6(X0),k3_relat_1(X0)) & r2_hidden(sK5(X0),k3_relat_1(X0))))),
% 1.52/0.59    introduced(choice_axiom,[])).
% 1.52/0.59  fof(f32,plain,(
% 1.52/0.59    ! [X0] : (((v6_relat_2(X0) | ? [X1,X2] : (~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))) & (! [X3,X4] : (r2_hidden(k4_tarski(X4,X3),X0) | r2_hidden(k4_tarski(X3,X4),X0) | X3 = X4 | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0))) | ~v6_relat_2(X0))) | ~v1_relat_1(X0))),
% 1.52/0.59    inference(rectify,[],[f31])).
% 1.52/0.59  fof(f31,plain,(
% 1.52/0.59    ! [X0] : (((v6_relat_2(X0) | ? [X1,X2] : (~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))) & (! [X1,X2] : (r2_hidden(k4_tarski(X2,X1),X0) | r2_hidden(k4_tarski(X1,X2),X0) | X1 = X2 | ~r2_hidden(X2,k3_relat_1(X0)) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v6_relat_2(X0))) | ~v1_relat_1(X0))),
% 1.52/0.59    inference(nnf_transformation,[],[f17])).
% 1.52/0.59  fof(f17,plain,(
% 1.52/0.59    ! [X0] : ((v6_relat_2(X0) <=> ! [X1,X2] : (r2_hidden(k4_tarski(X2,X1),X0) | r2_hidden(k4_tarski(X1,X2),X0) | X1 = X2 | ~r2_hidden(X2,k3_relat_1(X0)) | ~r2_hidden(X1,k3_relat_1(X0)))) | ~v1_relat_1(X0))),
% 1.52/0.59    inference(ennf_transformation,[],[f9])).
% 1.52/0.59  fof(f9,axiom,(
% 1.52/0.59    ! [X0] : (v1_relat_1(X0) => (v6_relat_2(X0) <=> ! [X1,X2] : ~(~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))))),
% 1.52/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l4_wellord1)).
% 1.52/0.59  fof(f264,plain,(
% 1.52/0.59    ~spl12_3 | ~spl12_2 | spl12_13),
% 1.52/0.59    inference(avatar_split_clause,[],[f251,f242,f99,f103])).
% 1.52/0.59  fof(f242,plain,(
% 1.52/0.59    spl12_13 <=> v8_relat_2(sK2)),
% 1.52/0.59    introduced(avatar_definition,[new_symbols(naming,[spl12_13])])).
% 1.52/0.59  fof(f251,plain,(
% 1.52/0.59    ~v2_wellord1(sK2) | ~v1_relat_1(sK2) | spl12_13),
% 1.52/0.59    inference(resolution,[],[f243,f70])).
% 1.52/0.59  fof(f70,plain,(
% 1.52/0.59    ( ! [X0] : (v8_relat_2(X0) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 1.52/0.59    inference(cnf_transformation,[],[f40])).
% 1.52/0.59  fof(f243,plain,(
% 1.52/0.59    ~v8_relat_2(sK2) | spl12_13),
% 1.52/0.59    inference(avatar_component_clause,[],[f242])).
% 1.52/0.59  fof(f247,plain,(
% 1.52/0.59    ~spl12_13 | spl12_14 | ~spl12_3),
% 1.52/0.59    inference(avatar_split_clause,[],[f240,f103,f245,f242])).
% 1.52/0.59  fof(f240,plain,(
% 1.52/0.59    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | ~r2_hidden(k4_tarski(X2,X0),sK2) | ~v8_relat_2(sK2) | r2_hidden(k4_tarski(X2,X1),sK2)) ) | ~spl12_3),
% 1.52/0.59    inference(resolution,[],[f65,f104])).
% 1.52/0.59  fof(f65,plain,(
% 1.52/0.59    ( ! [X6,X4,X0,X5] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(k4_tarski(X4,X5),X0) | ~v8_relat_2(X0) | r2_hidden(k4_tarski(X4,X6),X0)) )),
% 1.52/0.59    inference(cnf_transformation,[],[f38])).
% 1.52/0.59  fof(f38,plain,(
% 1.52/0.59    ! [X0] : (((v8_relat_2(X0) | (~r2_hidden(k4_tarski(sK7(X0),sK9(X0)),X0) & r2_hidden(k4_tarski(sK8(X0),sK9(X0)),X0) & r2_hidden(k4_tarski(sK7(X0),sK8(X0)),X0))) & (! [X4,X5,X6] : (r2_hidden(k4_tarski(X4,X6),X0) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~v8_relat_2(X0))) | ~v1_relat_1(X0))),
% 1.52/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f36,f37])).
% 1.52/0.59  fof(f37,plain,(
% 1.52/0.59    ! [X0] : (? [X1,X2,X3] : (~r2_hidden(k4_tarski(X1,X3),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(k4_tarski(X1,X2),X0)) => (~r2_hidden(k4_tarski(sK7(X0),sK9(X0)),X0) & r2_hidden(k4_tarski(sK8(X0),sK9(X0)),X0) & r2_hidden(k4_tarski(sK7(X0),sK8(X0)),X0)))),
% 1.52/0.59    introduced(choice_axiom,[])).
% 1.52/0.59  fof(f36,plain,(
% 1.52/0.59    ! [X0] : (((v8_relat_2(X0) | ? [X1,X2,X3] : (~r2_hidden(k4_tarski(X1,X3),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(k4_tarski(X1,X2),X0))) & (! [X4,X5,X6] : (r2_hidden(k4_tarski(X4,X6),X0) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~v8_relat_2(X0))) | ~v1_relat_1(X0))),
% 1.52/0.59    inference(rectify,[],[f35])).
% 1.52/0.59  fof(f35,plain,(
% 1.52/0.59    ! [X0] : (((v8_relat_2(X0) | ? [X1,X2,X3] : (~r2_hidden(k4_tarski(X1,X3),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(k4_tarski(X1,X2),X0))) & (! [X1,X2,X3] : (r2_hidden(k4_tarski(X1,X3),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(k4_tarski(X1,X2),X0)) | ~v8_relat_2(X0))) | ~v1_relat_1(X0))),
% 1.52/0.59    inference(nnf_transformation,[],[f19])).
% 1.52/0.59  fof(f19,plain,(
% 1.52/0.59    ! [X0] : ((v8_relat_2(X0) <=> ! [X1,X2,X3] : (r2_hidden(k4_tarski(X1,X3),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(k4_tarski(X1,X2),X0))) | ~v1_relat_1(X0))),
% 1.52/0.59    inference(flattening,[],[f18])).
% 1.52/0.59  fof(f18,plain,(
% 1.52/0.59    ! [X0] : ((v8_relat_2(X0) <=> ! [X1,X2,X3] : (r2_hidden(k4_tarski(X1,X3),X0) | (~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(k4_tarski(X1,X2),X0)))) | ~v1_relat_1(X0))),
% 1.52/0.59    inference(ennf_transformation,[],[f7])).
% 1.52/0.59  fof(f7,axiom,(
% 1.52/0.59    ! [X0] : (v1_relat_1(X0) => (v8_relat_2(X0) <=> ! [X1,X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(k4_tarski(X1,X2),X0)) => r2_hidden(k4_tarski(X1,X3),X0))))),
% 1.52/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l2_wellord1)).
% 1.52/0.59  fof(f221,plain,(
% 1.52/0.59    ~spl12_3 | ~spl12_2 | spl12_9),
% 1.52/0.59    inference(avatar_split_clause,[],[f211,f203,f99,f103])).
% 1.52/0.59  fof(f203,plain,(
% 1.52/0.59    spl12_9 <=> v4_relat_2(sK2)),
% 1.52/0.59    introduced(avatar_definition,[new_symbols(naming,[spl12_9])])).
% 1.52/0.59  fof(f211,plain,(
% 1.52/0.59    ~v2_wellord1(sK2) | ~v1_relat_1(sK2) | spl12_9),
% 1.52/0.59    inference(resolution,[],[f204,f71])).
% 1.52/0.59  fof(f71,plain,(
% 1.52/0.59    ( ! [X0] : (v4_relat_2(X0) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 1.52/0.59    inference(cnf_transformation,[],[f40])).
% 1.52/0.59  fof(f204,plain,(
% 1.52/0.59    ~v4_relat_2(sK2) | spl12_9),
% 1.52/0.59    inference(avatar_component_clause,[],[f203])).
% 1.52/0.59  fof(f208,plain,(
% 1.52/0.59    ~spl12_9 | spl12_10 | ~spl12_3),
% 1.52/0.59    inference(avatar_split_clause,[],[f201,f103,f206,f203])).
% 1.52/0.59  fof(f201,plain,(
% 1.52/0.59    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | ~r2_hidden(k4_tarski(X1,X0),sK2) | ~v4_relat_2(sK2) | X0 = X1) ) | ~spl12_3),
% 1.52/0.59    inference(resolution,[],[f55,f104])).
% 1.52/0.59  fof(f55,plain,(
% 1.52/0.59    ( ! [X4,X0,X3] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(X4,X3),X0) | ~r2_hidden(k4_tarski(X3,X4),X0) | ~v4_relat_2(X0) | X3 = X4) )),
% 1.52/0.59    inference(cnf_transformation,[],[f30])).
% 1.52/0.59  fof(f30,plain,(
% 1.52/0.59    ! [X0] : (((v4_relat_2(X0) | (sK3(X0) != sK4(X0) & r2_hidden(k4_tarski(sK4(X0),sK3(X0)),X0) & r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0))) & (! [X3,X4] : (X3 = X4 | ~r2_hidden(k4_tarski(X4,X3),X0) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~v4_relat_2(X0))) | ~v1_relat_1(X0))),
% 1.52/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f28,f29])).
% 1.52/0.59  fof(f29,plain,(
% 1.52/0.59    ! [X0] : (? [X1,X2] : (X1 != X2 & r2_hidden(k4_tarski(X2,X1),X0) & r2_hidden(k4_tarski(X1,X2),X0)) => (sK3(X0) != sK4(X0) & r2_hidden(k4_tarski(sK4(X0),sK3(X0)),X0) & r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0)))),
% 1.52/0.59    introduced(choice_axiom,[])).
% 1.52/0.59  fof(f28,plain,(
% 1.52/0.59    ! [X0] : (((v4_relat_2(X0) | ? [X1,X2] : (X1 != X2 & r2_hidden(k4_tarski(X2,X1),X0) & r2_hidden(k4_tarski(X1,X2),X0))) & (! [X3,X4] : (X3 = X4 | ~r2_hidden(k4_tarski(X4,X3),X0) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~v4_relat_2(X0))) | ~v1_relat_1(X0))),
% 1.52/0.59    inference(rectify,[],[f27])).
% 1.52/0.59  fof(f27,plain,(
% 1.52/0.59    ! [X0] : (((v4_relat_2(X0) | ? [X1,X2] : (X1 != X2 & r2_hidden(k4_tarski(X2,X1),X0) & r2_hidden(k4_tarski(X1,X2),X0))) & (! [X1,X2] : (X1 = X2 | ~r2_hidden(k4_tarski(X2,X1),X0) | ~r2_hidden(k4_tarski(X1,X2),X0)) | ~v4_relat_2(X0))) | ~v1_relat_1(X0))),
% 1.52/0.59    inference(nnf_transformation,[],[f16])).
% 1.52/0.59  fof(f16,plain,(
% 1.52/0.59    ! [X0] : ((v4_relat_2(X0) <=> ! [X1,X2] : (X1 = X2 | ~r2_hidden(k4_tarski(X2,X1),X0) | ~r2_hidden(k4_tarski(X1,X2),X0))) | ~v1_relat_1(X0))),
% 1.52/0.59    inference(flattening,[],[f15])).
% 1.52/0.59  fof(f15,plain,(
% 1.52/0.59    ! [X0] : ((v4_relat_2(X0) <=> ! [X1,X2] : (X1 = X2 | (~r2_hidden(k4_tarski(X2,X1),X0) | ~r2_hidden(k4_tarski(X1,X2),X0)))) | ~v1_relat_1(X0))),
% 1.52/0.59    inference(ennf_transformation,[],[f8])).
% 1.52/0.59  fof(f8,axiom,(
% 1.52/0.59    ! [X0] : (v1_relat_1(X0) => (v4_relat_2(X0) <=> ! [X1,X2] : ((r2_hidden(k4_tarski(X2,X1),X0) & r2_hidden(k4_tarski(X1,X2),X0)) => X1 = X2)))),
% 1.52/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_wellord1)).
% 1.52/0.59  fof(f122,plain,(
% 1.52/0.59    ~spl12_3 | spl12_4 | ~spl12_3),
% 1.52/0.59    inference(avatar_split_clause,[],[f116,f103,f120,f103])).
% 1.52/0.59  fof(f116,plain,(
% 1.52/0.59    ( ! [X0,X1] : (r1_tarski(k1_wellord1(sK2,X0),X1) | r2_hidden(X0,k3_relat_1(sK2)) | ~v1_relat_1(sK2)) ) | ~spl12_3),
% 1.52/0.59    inference(resolution,[],[f115,f89])).
% 1.52/0.59  fof(f89,plain,(
% 1.52/0.59    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X1,k3_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 1.52/0.59    inference(cnf_transformation,[],[f24])).
% 1.52/0.59  fof(f24,plain,(
% 1.52/0.59    ! [X0,X1,X2] : ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 1.52/0.59    inference(flattening,[],[f23])).
% 1.52/0.59  fof(f23,plain,(
% 1.52/0.59    ! [X0,X1,X2] : (((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 1.52/0.59    inference(ennf_transformation,[],[f4])).
% 1.52/0.59  fof(f4,axiom,(
% 1.52/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 1.52/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).
% 1.52/0.59  fof(f105,plain,(
% 1.52/0.59    spl12_3),
% 1.52/0.59    inference(avatar_split_clause,[],[f52,f103])).
% 1.52/0.59  fof(f52,plain,(
% 1.52/0.59    v1_relat_1(sK2)),
% 1.52/0.59    inference(cnf_transformation,[],[f26])).
% 1.52/0.59  fof(f26,plain,(
% 1.52/0.59    ~r3_xboole_0(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) & v2_wellord1(sK2) & v1_relat_1(sK2)),
% 1.52/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f25])).
% 1.52/0.59  fof(f25,plain,(
% 1.52/0.59    ? [X0,X1,X2] : (~r3_xboole_0(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) & v2_wellord1(X2) & v1_relat_1(X2)) => (~r3_xboole_0(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) & v2_wellord1(sK2) & v1_relat_1(sK2))),
% 1.52/0.59    introduced(choice_axiom,[])).
% 1.52/0.59  fof(f14,plain,(
% 1.52/0.59    ? [X0,X1,X2] : (~r3_xboole_0(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) & v2_wellord1(X2) & v1_relat_1(X2))),
% 1.52/0.59    inference(flattening,[],[f13])).
% 1.52/0.59  fof(f13,plain,(
% 1.52/0.59    ? [X0,X1,X2] : ((~r3_xboole_0(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) & v2_wellord1(X2)) & v1_relat_1(X2))),
% 1.52/0.59    inference(ennf_transformation,[],[f11])).
% 1.52/0.59  fof(f11,negated_conjecture,(
% 1.52/0.59    ~! [X0,X1,X2] : (v1_relat_1(X2) => (v2_wellord1(X2) => r3_xboole_0(k1_wellord1(X2,X0),k1_wellord1(X2,X1))))),
% 1.52/0.59    inference(negated_conjecture,[],[f10])).
% 1.52/0.59  fof(f10,conjecture,(
% 1.52/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) => (v2_wellord1(X2) => r3_xboole_0(k1_wellord1(X2,X0),k1_wellord1(X2,X1))))),
% 1.52/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_wellord1)).
% 1.52/0.59  fof(f101,plain,(
% 1.52/0.59    spl12_2),
% 1.52/0.59    inference(avatar_split_clause,[],[f53,f99])).
% 1.52/0.59  fof(f53,plain,(
% 1.52/0.59    v2_wellord1(sK2)),
% 1.52/0.59    inference(cnf_transformation,[],[f26])).
% 1.52/0.59  fof(f97,plain,(
% 1.52/0.59    ~spl12_1),
% 1.52/0.59    inference(avatar_split_clause,[],[f54,f95])).
% 1.52/0.59  fof(f54,plain,(
% 1.52/0.59    ~r3_xboole_0(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))),
% 1.52/0.59    inference(cnf_transformation,[],[f26])).
% 1.52/0.59  % SZS output end Proof for theBenchmark
% 1.52/0.59  % (8069)------------------------------
% 1.52/0.59  % (8069)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.59  % (8069)Termination reason: Refutation
% 1.52/0.59  
% 1.52/0.59  % (8069)Memory used [KB]: 11385
% 1.52/0.59  % (8069)Time elapsed: 0.166 s
% 1.52/0.59  % (8069)------------------------------
% 1.52/0.59  % (8069)------------------------------
% 1.52/0.59  % (8049)Success in time 0.228 s
%------------------------------------------------------------------------------
