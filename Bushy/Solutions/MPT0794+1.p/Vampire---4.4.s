%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : wellord1__t45_wellord1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:14 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 319 expanded)
%              Number of leaves         :   33 ( 142 expanded)
%              Depth                    :   12
%              Number of atoms          :  663 (2246 expanded)
%              Number of equality atoms :   86 ( 366 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f471,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f103,f110,f117,f124,f138,f145,f152,f204,f231,f252,f265,f277,f282,f373,f401,f418,f423,f439,f445,f470])).

fof(f470,plain,
    ( ~ spl14_4
    | ~ spl14_6
    | spl14_11
    | ~ spl14_38
    | ~ spl14_58
    | ~ spl14_74
    | ~ spl14_80 ),
    inference(avatar_contradiction_clause,[],[f467])).

fof(f467,plain,
    ( $false
    | ~ spl14_4
    | ~ spl14_6
    | ~ spl14_11
    | ~ spl14_38
    | ~ spl14_58
    | ~ spl14_74
    | ~ spl14_80 ),
    inference(unit_resulting_resolution,[],[f116,f123,f346,f137,f400,f251,f438,f76])).

fof(f76,plain,(
    ! [X4,X0,X3] :
      ( k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | X3 = X4
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ( sK7(X0) != sK8(X0)
            & k1_funct_1(X0,sK7(X0)) = k1_funct_1(X0,sK8(X0))
            & r2_hidden(sK8(X0),k1_relat_1(X0))
            & r2_hidden(sK7(X0),k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f49,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK7(X0) != sK8(X0)
        & k1_funct_1(X0,sK7(X0)) = k1_funct_1(X0,sK8(X0))
        & r2_hidden(sK8(X0),k1_relat_1(X0))
        & r2_hidden(sK7(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X1,X2] :
              ( X1 = X2
              | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
              | ~ r2_hidden(X2,k1_relat_1(X0))
              | ~ r2_hidden(X1,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t45_wellord1.p',d8_funct_1)).

fof(f438,plain,
    ( r2_hidden(sK3,k1_relat_1(sK2))
    | ~ spl14_80 ),
    inference(avatar_component_clause,[],[f437])).

fof(f437,plain,
    ( spl14_80
  <=> r2_hidden(sK3,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_80])])).

fof(f251,plain,
    ( k1_funct_1(sK2,sK3) = k1_funct_1(sK2,sK4)
    | ~ spl14_38 ),
    inference(avatar_component_clause,[],[f250])).

fof(f250,plain,
    ( spl14_38
  <=> k1_funct_1(sK2,sK3) = k1_funct_1(sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_38])])).

fof(f400,plain,
    ( r2_hidden(sK4,k1_relat_1(sK2))
    | ~ spl14_74 ),
    inference(avatar_component_clause,[],[f399])).

fof(f399,plain,
    ( spl14_74
  <=> r2_hidden(sK4,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_74])])).

fof(f137,plain,
    ( sK3 != sK4
    | ~ spl14_11 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl14_11
  <=> sK3 != sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_11])])).

fof(f346,plain,
    ( v2_funct_1(sK2)
    | ~ spl14_58 ),
    inference(avatar_component_clause,[],[f345])).

fof(f345,plain,
    ( spl14_58
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_58])])).

fof(f123,plain,
    ( v1_funct_1(sK2)
    | ~ spl14_6 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl14_6
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_6])])).

fof(f116,plain,
    ( v1_relat_1(sK2)
    | ~ spl14_4 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl14_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_4])])).

fof(f445,plain,
    ( ~ spl14_0
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_6
    | ~ spl14_12
    | ~ spl14_30 ),
    inference(avatar_contradiction_clause,[],[f443])).

fof(f443,plain,
    ( $false
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_6
    | ~ spl14_12
    | ~ spl14_30 ),
    inference(unit_resulting_resolution,[],[f116,f123,f109,f144,f102,f224,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ sP13(X0)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | ~ r3_wellord1(X0,X1,X2) ) ),
    inference(general_splitting,[],[f94,f95_D])).

fof(f95,plain,(
    ! [X0,X5] :
      ( ~ sP12(X5,X0)
      | r2_hidden(X5,k3_relat_1(X0))
      | sP13(X0) ) ),
    inference(cnf_transformation,[],[f95_D])).

fof(f95_D,plain,(
    ! [X0] :
      ( ! [X5] :
          ( ~ sP12(X5,X0)
          | r2_hidden(X5,k3_relat_1(X0)) )
    <=> ~ sP13(X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP13])])).

fof(f94,plain,(
    ! [X2,X0,X5,X1] :
      ( r2_hidden(X5,k3_relat_1(X0))
      | ~ r3_wellord1(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | ~ sP12(X5,X0) ) ),
    inference(general_splitting,[],[f68,f93_D])).

fof(f93,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X0)
      | sP12(X5,X0) ) ),
    inference(cnf_transformation,[],[f93_D])).

fof(f93_D,plain,(
    ! [X0,X5] :
      ( ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0)
    <=> ~ sP12(X5,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP12])])).

fof(f68,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(X5,k3_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r3_wellord1(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_wellord1(X0,X1,X2)
                  | ( ( ~ r2_hidden(k4_tarski(k1_funct_1(X2,sK5(X0,X1,X2)),k1_funct_1(X2,sK6(X0,X1,X2))),X1)
                      | ~ r2_hidden(sK6(X0,X1,X2),k3_relat_1(X0))
                      | ~ r2_hidden(sK5(X0,X1,X2),k3_relat_1(X0))
                      | ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X0) )
                    & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,sK5(X0,X1,X2)),k1_funct_1(X2,sK6(X0,X1,X2))),X1)
                        & r2_hidden(sK6(X0,X1,X2),k3_relat_1(X0))
                        & r2_hidden(sK5(X0,X1,X2),k3_relat_1(X0)) )
                      | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X0) ) )
                  | ~ v2_funct_1(X2)
                  | k3_relat_1(X1) != k2_relat_1(X2)
                  | k1_relat_1(X2) != k3_relat_1(X0) )
                & ( ( ! [X5,X6] :
                        ( ( r2_hidden(k4_tarski(X5,X6),X0)
                          | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X5),k1_funct_1(X2,X6)),X1)
                          | ~ r2_hidden(X6,k3_relat_1(X0))
                          | ~ r2_hidden(X5,k3_relat_1(X0)) )
                        & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,X5),k1_funct_1(X2,X6)),X1)
                            & r2_hidden(X6,k3_relat_1(X0))
                            & r2_hidden(X5,k3_relat_1(X0)) )
                          | ~ r2_hidden(k4_tarski(X5,X6),X0) ) )
                    & v2_funct_1(X2)
                    & k3_relat_1(X1) = k2_relat_1(X2)
                    & k1_relat_1(X2) = k3_relat_1(X0) )
                  | ~ r3_wellord1(X0,X1,X2) ) )
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f45,f46])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
            | ~ r2_hidden(X4,k3_relat_1(X0))
            | ~ r2_hidden(X3,k3_relat_1(X0))
            | ~ r2_hidden(k4_tarski(X3,X4),X0) )
          & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
              & r2_hidden(X4,k3_relat_1(X0))
              & r2_hidden(X3,k3_relat_1(X0)) )
            | r2_hidden(k4_tarski(X3,X4),X0) ) )
     => ( ( ~ r2_hidden(k4_tarski(k1_funct_1(X2,sK5(X0,X1,X2)),k1_funct_1(X2,sK6(X0,X1,X2))),X1)
          | ~ r2_hidden(sK6(X0,X1,X2),k3_relat_1(X0))
          | ~ r2_hidden(sK5(X0,X1,X2),k3_relat_1(X0))
          | ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X0) )
        & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,sK5(X0,X1,X2)),k1_funct_1(X2,sK6(X0,X1,X2))),X1)
            & r2_hidden(sK6(X0,X1,X2),k3_relat_1(X0))
            & r2_hidden(sK5(X0,X1,X2),k3_relat_1(X0)) )
          | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_wellord1(X0,X1,X2)
                  | ? [X3,X4] :
                      ( ( ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                        | ~ r2_hidden(X4,k3_relat_1(X0))
                        | ~ r2_hidden(X3,k3_relat_1(X0))
                        | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                      & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                          & r2_hidden(X4,k3_relat_1(X0))
                          & r2_hidden(X3,k3_relat_1(X0)) )
                        | r2_hidden(k4_tarski(X3,X4),X0) ) )
                  | ~ v2_funct_1(X2)
                  | k3_relat_1(X1) != k2_relat_1(X2)
                  | k1_relat_1(X2) != k3_relat_1(X0) )
                & ( ( ! [X5,X6] :
                        ( ( r2_hidden(k4_tarski(X5,X6),X0)
                          | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X5),k1_funct_1(X2,X6)),X1)
                          | ~ r2_hidden(X6,k3_relat_1(X0))
                          | ~ r2_hidden(X5,k3_relat_1(X0)) )
                        & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,X5),k1_funct_1(X2,X6)),X1)
                            & r2_hidden(X6,k3_relat_1(X0))
                            & r2_hidden(X5,k3_relat_1(X0)) )
                          | ~ r2_hidden(k4_tarski(X5,X6),X0) ) )
                    & v2_funct_1(X2)
                    & k3_relat_1(X1) = k2_relat_1(X2)
                    & k1_relat_1(X2) = k3_relat_1(X0) )
                  | ~ r3_wellord1(X0,X1,X2) ) )
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_wellord1(X0,X1,X2)
                  | ? [X3,X4] :
                      ( ( ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                        | ~ r2_hidden(X4,k3_relat_1(X0))
                        | ~ r2_hidden(X3,k3_relat_1(X0))
                        | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                      & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                          & r2_hidden(X4,k3_relat_1(X0))
                          & r2_hidden(X3,k3_relat_1(X0)) )
                        | r2_hidden(k4_tarski(X3,X4),X0) ) )
                  | ~ v2_funct_1(X2)
                  | k3_relat_1(X1) != k2_relat_1(X2)
                  | k1_relat_1(X2) != k3_relat_1(X0) )
                & ( ( ! [X3,X4] :
                        ( ( r2_hidden(k4_tarski(X3,X4),X0)
                          | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                          | ~ r2_hidden(X4,k3_relat_1(X0))
                          | ~ r2_hidden(X3,k3_relat_1(X0)) )
                        & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                            & r2_hidden(X4,k3_relat_1(X0))
                            & r2_hidden(X3,k3_relat_1(X0)) )
                          | ~ r2_hidden(k4_tarski(X3,X4),X0) ) )
                    & v2_funct_1(X2)
                    & k3_relat_1(X1) = k2_relat_1(X2)
                    & k1_relat_1(X2) = k3_relat_1(X0) )
                  | ~ r3_wellord1(X0,X1,X2) ) )
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_wellord1(X0,X1,X2)
                  | ? [X3,X4] :
                      ( ( ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                        | ~ r2_hidden(X4,k3_relat_1(X0))
                        | ~ r2_hidden(X3,k3_relat_1(X0))
                        | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                      & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                          & r2_hidden(X4,k3_relat_1(X0))
                          & r2_hidden(X3,k3_relat_1(X0)) )
                        | r2_hidden(k4_tarski(X3,X4),X0) ) )
                  | ~ v2_funct_1(X2)
                  | k3_relat_1(X1) != k2_relat_1(X2)
                  | k1_relat_1(X2) != k3_relat_1(X0) )
                & ( ( ! [X3,X4] :
                        ( ( r2_hidden(k4_tarski(X3,X4),X0)
                          | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                          | ~ r2_hidden(X4,k3_relat_1(X0))
                          | ~ r2_hidden(X3,k3_relat_1(X0)) )
                        & ( ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                            & r2_hidden(X4,k3_relat_1(X0))
                            & r2_hidden(X3,k3_relat_1(X0)) )
                          | ~ r2_hidden(k4_tarski(X3,X4),X0) ) )
                    & v2_funct_1(X2)
                    & k3_relat_1(X1) = k2_relat_1(X2)
                    & k1_relat_1(X2) = k3_relat_1(X0) )
                  | ~ r3_wellord1(X0,X1,X2) ) )
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_wellord1(X0,X1,X2)
              <=> ( ! [X3,X4] :
                      ( r2_hidden(k4_tarski(X3,X4),X0)
                    <=> ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                        & r2_hidden(X4,k3_relat_1(X0))
                        & r2_hidden(X3,k3_relat_1(X0)) ) )
                  & v2_funct_1(X2)
                  & k3_relat_1(X1) = k2_relat_1(X2)
                  & k1_relat_1(X2) = k3_relat_1(X0) ) )
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_wellord1(X0,X1,X2)
              <=> ( ! [X3,X4] :
                      ( r2_hidden(k4_tarski(X3,X4),X0)
                    <=> ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                        & r2_hidden(X4,k3_relat_1(X0))
                        & r2_hidden(X3,k3_relat_1(X0)) ) )
                  & v2_funct_1(X2)
                  & k3_relat_1(X1) = k2_relat_1(X2)
                  & k1_relat_1(X2) = k3_relat_1(X0) ) )
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( r3_wellord1(X0,X1,X2)
              <=> ( ! [X3,X4] :
                      ( r2_hidden(k4_tarski(X3,X4),X0)
                    <=> ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                        & r2_hidden(X4,k3_relat_1(X0))
                        & r2_hidden(X3,k3_relat_1(X0)) ) )
                  & v2_funct_1(X2)
                  & k3_relat_1(X1) = k2_relat_1(X2)
                  & k1_relat_1(X2) = k3_relat_1(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t45_wellord1.p',d7_wellord1)).

fof(f224,plain,
    ( sP13(sK0)
    | ~ spl14_30 ),
    inference(avatar_component_clause,[],[f223])).

fof(f223,plain,
    ( spl14_30
  <=> sP13(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_30])])).

fof(f102,plain,
    ( v1_relat_1(sK0)
    | ~ spl14_0 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl14_0
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_0])])).

fof(f144,plain,
    ( r3_wellord1(sK0,sK1,sK2)
    | ~ spl14_12 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl14_12
  <=> r3_wellord1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_12])])).

fof(f109,plain,
    ( v1_relat_1(sK1)
    | ~ spl14_2 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl14_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).

fof(f439,plain,
    ( spl14_80
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_12
    | ~ spl14_32
    | ~ spl14_68 ),
    inference(avatar_split_clause,[],[f387,f371,f229,f143,f108,f101,f437])).

fof(f229,plain,
    ( spl14_32
  <=> r2_hidden(sK3,k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_32])])).

fof(f371,plain,
    ( spl14_68
  <=> ! [X1,X0] :
        ( ~ r3_wellord1(X0,X1,sK2)
        | k1_relat_1(sK2) = k3_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_68])])).

fof(f387,plain,
    ( r2_hidden(sK3,k1_relat_1(sK2))
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_12
    | ~ spl14_32
    | ~ spl14_68 ),
    inference(backward_demodulation,[],[f380,f230])).

fof(f230,plain,
    ( r2_hidden(sK3,k3_relat_1(sK0))
    | ~ spl14_32 ),
    inference(avatar_component_clause,[],[f229])).

fof(f380,plain,
    ( k1_relat_1(sK2) = k3_relat_1(sK0)
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_12
    | ~ spl14_68 ),
    inference(subsumption_resolution,[],[f379,f102])).

fof(f379,plain,
    ( k1_relat_1(sK2) = k3_relat_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl14_2
    | ~ spl14_12
    | ~ spl14_68 ),
    inference(subsumption_resolution,[],[f378,f109])).

fof(f378,plain,
    ( k1_relat_1(sK2) = k3_relat_1(sK0)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl14_12
    | ~ spl14_68 ),
    inference(resolution,[],[f372,f144])).

fof(f372,plain,
    ( ! [X0,X1] :
        ( ~ r3_wellord1(X0,X1,sK2)
        | k1_relat_1(sK2) = k3_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl14_68 ),
    inference(avatar_component_clause,[],[f371])).

fof(f423,plain,
    ( ~ spl14_0
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_6
    | ~ spl14_12
    | ~ spl14_44 ),
    inference(avatar_contradiction_clause,[],[f421])).

fof(f421,plain,
    ( $false
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_6
    | ~ spl14_12
    | ~ spl14_44 ),
    inference(unit_resulting_resolution,[],[f116,f123,f109,f144,f102,f276,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ sP11(X0)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | ~ r3_wellord1(X0,X1,X2) ) ),
    inference(general_splitting,[],[f90,f91_D])).

fof(f91,plain,(
    ! [X0,X5] :
      ( ~ sP10(X5,X0)
      | sP11(X0) ) ),
    inference(cnf_transformation,[],[f91_D])).

fof(f91_D,plain,(
    ! [X0] :
      ( ! [X5] : ~ sP10(X5,X0)
    <=> ~ sP11(X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP11])])).

fof(f90,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ r3_wellord1(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | ~ sP10(X5,X0) ) ),
    inference(general_splitting,[],[f69,f89_D])).

fof(f89,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X0)
      | r2_hidden(X6,k3_relat_1(X0))
      | sP10(X5,X0) ) ),
    inference(cnf_transformation,[],[f89_D])).

fof(f89_D,plain,(
    ! [X0,X5] :
      ( ! [X6] :
          ( ~ r2_hidden(k4_tarski(X5,X6),X0)
          | r2_hidden(X6,k3_relat_1(X0)) )
    <=> ~ sP10(X5,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP10])])).

fof(f69,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(X6,k3_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r3_wellord1(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f276,plain,
    ( sP11(sK0)
    | ~ spl14_44 ),
    inference(avatar_component_clause,[],[f275])).

fof(f275,plain,
    ( spl14_44
  <=> sP11(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_44])])).

fof(f418,plain,
    ( ~ spl14_0
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_6
    | ~ spl14_12
    | spl14_59 ),
    inference(avatar_contradiction_clause,[],[f416])).

fof(f416,plain,
    ( $false
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_6
    | ~ spl14_12
    | ~ spl14_59 ),
    inference(unit_resulting_resolution,[],[f102,f109,f116,f123,f144,f343,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r3_wellord1(X0,X1,X2)
      | v2_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f343,plain,
    ( ~ v2_funct_1(sK2)
    | ~ spl14_59 ),
    inference(avatar_component_clause,[],[f342])).

fof(f342,plain,
    ( spl14_59
  <=> ~ v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_59])])).

fof(f401,plain,
    ( spl14_74
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_12
    | ~ spl14_42
    | ~ spl14_68 ),
    inference(avatar_split_clause,[],[f385,f371,f263,f143,f108,f101,f399])).

fof(f263,plain,
    ( spl14_42
  <=> r2_hidden(sK4,k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_42])])).

fof(f385,plain,
    ( r2_hidden(sK4,k1_relat_1(sK2))
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_12
    | ~ spl14_42
    | ~ spl14_68 ),
    inference(backward_demodulation,[],[f380,f264])).

fof(f264,plain,
    ( r2_hidden(sK4,k3_relat_1(sK0))
    | ~ spl14_42 ),
    inference(avatar_component_clause,[],[f263])).

fof(f373,plain,
    ( spl14_68
    | ~ spl14_4
    | ~ spl14_6 ),
    inference(avatar_split_clause,[],[f267,f122,f115,f371])).

fof(f267,plain,
    ( ! [X0,X1] :
        ( ~ r3_wellord1(X0,X1,sK2)
        | k1_relat_1(sK2) = k3_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl14_4
    | ~ spl14_6 ),
    inference(subsumption_resolution,[],[f266,f116])).

fof(f266,plain,
    ( ! [X0,X1] :
        ( ~ r3_wellord1(X0,X1,sK2)
        | k1_relat_1(sK2) = k3_relat_1(X0)
        | ~ v1_relat_1(sK2)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl14_6 ),
    inference(resolution,[],[f65,f123])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r3_wellord1(X0,X1,X2)
      | k1_relat_1(X2) = k3_relat_1(X0)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f282,plain,
    ( ~ spl14_0
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_6
    | ~ spl14_12
    | ~ spl14_14
    | spl14_37 ),
    inference(avatar_contradiction_clause,[],[f280])).

fof(f280,plain,
    ( $false
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_6
    | ~ spl14_12
    | ~ spl14_14
    | ~ spl14_37 ),
    inference(unit_resulting_resolution,[],[f102,f109,f116,f123,f144,f151,f245,f70])).

fof(f70,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r3_wellord1(X0,X1,X2)
      | r2_hidden(k4_tarski(k1_funct_1(X2,X5),k1_funct_1(X2,X6)),X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f245,plain,
    ( ~ r2_hidden(k4_tarski(k1_funct_1(sK2,sK3),k1_funct_1(sK2,sK4)),sK1)
    | ~ spl14_37 ),
    inference(avatar_component_clause,[],[f244])).

fof(f244,plain,
    ( spl14_37
  <=> ~ r2_hidden(k4_tarski(k1_funct_1(sK2,sK3),k1_funct_1(sK2,sK4)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_37])])).

fof(f151,plain,
    ( r2_hidden(k4_tarski(sK3,sK4),sK0)
    | ~ spl14_14 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl14_14
  <=> r2_hidden(k4_tarski(sK3,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_14])])).

fof(f277,plain,
    ( spl14_44
    | ~ spl14_40 ),
    inference(avatar_split_clause,[],[f268,f257,f275])).

fof(f257,plain,
    ( spl14_40
  <=> sP10(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_40])])).

fof(f268,plain,
    ( sP11(sK0)
    | ~ spl14_40 ),
    inference(resolution,[],[f258,f91])).

fof(f258,plain,
    ( sP10(sK3,sK0)
    | ~ spl14_40 ),
    inference(avatar_component_clause,[],[f257])).

fof(f265,plain,
    ( spl14_40
    | spl14_42
    | ~ spl14_14 ),
    inference(avatar_split_clause,[],[f214,f150,f263,f257])).

fof(f214,plain,
    ( r2_hidden(sK4,k3_relat_1(sK0))
    | sP10(sK3,sK0)
    | ~ spl14_14 ),
    inference(resolution,[],[f89,f151])).

fof(f252,plain,
    ( ~ spl14_37
    | spl14_38 ),
    inference(avatar_split_clause,[],[f61,f250,f244])).

fof(f61,plain,
    ( k1_funct_1(sK2,sK3) = k1_funct_1(sK2,sK4)
    | ~ r2_hidden(k4_tarski(k1_funct_1(sK2,sK3),k1_funct_1(sK2,sK4)),sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ( k1_funct_1(sK2,sK3) = k1_funct_1(sK2,sK4)
      | ~ r2_hidden(k4_tarski(k1_funct_1(sK2,sK3),k1_funct_1(sK2,sK4)),sK1) )
    & sK3 != sK4
    & r2_hidden(k4_tarski(sK3,sK4),sK0)
    & r3_wellord1(sK0,sK1,sK2)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f26,f41,f40,f39,f38])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3,X4] :
                    ( ( k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
                      | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) )
                    & X3 != X4
                    & r2_hidden(k4_tarski(X3,X4),X0) )
                & r3_wellord1(X0,X1,X2)
                & v1_funct_1(X2)
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X4,X3] :
                  ( ( k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
                    | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) )
                  & X3 != X4
                  & r2_hidden(k4_tarski(X3,X4),sK0) )
              & r3_wellord1(sK0,X1,X2)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3,X4] :
                  ( ( k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
                    | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) )
                  & X3 != X4
                  & r2_hidden(k4_tarski(X3,X4),X0) )
              & r3_wellord1(X0,X1,X2)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
     => ( ? [X2] :
            ( ? [X4,X3] :
                ( ( k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
                  | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),sK1) )
                & X3 != X4
                & r2_hidden(k4_tarski(X3,X4),X0) )
            & r3_wellord1(X0,sK1,X2)
            & v1_funct_1(X2)
            & v1_relat_1(X2) )
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3,X4] :
              ( ( k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
                | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) )
              & X3 != X4
              & r2_hidden(k4_tarski(X3,X4),X0) )
          & r3_wellord1(X0,X1,X2)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ? [X4,X3] :
            ( ( k1_funct_1(sK2,X3) = k1_funct_1(sK2,X4)
              | ~ r2_hidden(k4_tarski(k1_funct_1(sK2,X3),k1_funct_1(sK2,X4)),X1) )
            & X3 != X4
            & r2_hidden(k4_tarski(X3,X4),X0) )
        & r3_wellord1(X0,X1,sK2)
        & v1_funct_1(sK2)
        & v1_relat_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ? [X3,X4] :
          ( ( k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
            | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) )
          & X3 != X4
          & r2_hidden(k4_tarski(X3,X4),X0) )
     => ( ( k1_funct_1(X2,sK3) = k1_funct_1(X2,sK4)
          | ~ r2_hidden(k4_tarski(k1_funct_1(X2,sK3),k1_funct_1(X2,sK4)),X1) )
        & sK3 != sK4
        & r2_hidden(k4_tarski(sK3,sK4),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3,X4] :
                  ( ( k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
                    | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) )
                  & X3 != X4
                  & r2_hidden(k4_tarski(X3,X4),X0) )
              & r3_wellord1(X0,X1,X2)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3,X4] :
                  ( ( k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
                    | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) )
                  & X3 != X4
                  & r2_hidden(k4_tarski(X3,X4),X0) )
              & r3_wellord1(X0,X1,X2)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( r3_wellord1(X0,X1,X2)
                 => ! [X3,X4] :
                      ( r2_hidden(k4_tarski(X3,X4),X0)
                     => ( ( k1_funct_1(X2,X3) != k1_funct_1(X2,X4)
                          & r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) )
                        | X3 = X4 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( r3_wellord1(X0,X1,X2)
               => ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X0)
                   => ( ( k1_funct_1(X2,X3) != k1_funct_1(X2,X4)
                        & r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1) )
                      | X3 = X4 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t45_wellord1.p',t45_wellord1)).

fof(f231,plain,
    ( spl14_30
    | spl14_32
    | ~ spl14_28 ),
    inference(avatar_split_clause,[],[f205,f202,f229,f223])).

fof(f202,plain,
    ( spl14_28
  <=> sP12(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_28])])).

fof(f205,plain,
    ( r2_hidden(sK3,k3_relat_1(sK0))
    | sP13(sK0)
    | ~ spl14_28 ),
    inference(resolution,[],[f203,f95])).

fof(f203,plain,
    ( sP12(sK3,sK0)
    | ~ spl14_28 ),
    inference(avatar_component_clause,[],[f202])).

fof(f204,plain,
    ( spl14_28
    | ~ spl14_14 ),
    inference(avatar_split_clause,[],[f197,f150,f202])).

fof(f197,plain,
    ( sP12(sK3,sK0)
    | ~ spl14_14 ),
    inference(resolution,[],[f93,f151])).

fof(f152,plain,(
    spl14_14 ),
    inference(avatar_split_clause,[],[f59,f150])).

fof(f59,plain,(
    r2_hidden(k4_tarski(sK3,sK4),sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f145,plain,(
    spl14_12 ),
    inference(avatar_split_clause,[],[f58,f143])).

fof(f58,plain,(
    r3_wellord1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f138,plain,(
    ~ spl14_11 ),
    inference(avatar_split_clause,[],[f60,f136])).

fof(f60,plain,(
    sK3 != sK4 ),
    inference(cnf_transformation,[],[f42])).

fof(f124,plain,(
    spl14_6 ),
    inference(avatar_split_clause,[],[f57,f122])).

fof(f57,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f117,plain,(
    spl14_4 ),
    inference(avatar_split_clause,[],[f56,f115])).

fof(f56,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f110,plain,(
    spl14_2 ),
    inference(avatar_split_clause,[],[f55,f108])).

fof(f55,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f103,plain,(
    spl14_0 ),
    inference(avatar_split_clause,[],[f54,f101])).

fof(f54,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
