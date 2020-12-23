%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t62_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:03 EDT 2019

% Result     : Theorem 0.81s
% Output     : Refutation 0.81s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 149 expanded)
%              Number of leaves         :   22 (  67 expanded)
%              Depth                    :    8
%              Number of atoms          :  320 ( 561 expanded)
%              Number of equality atoms :   46 (  80 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f823,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f89,f105,f141,f382,f487,f535,f564,f651,f685,f739,f787,f800,f822])).

fof(f822,plain,
    ( ~ spl8_2
    | ~ spl8_112 ),
    inference(avatar_contradiction_clause,[],[f821])).

fof(f821,plain,
    ( $false
    | ~ spl8_2
    | ~ spl8_112 ),
    inference(subsumption_resolution,[],[f814,f88])).

fof(f88,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl8_2
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f814,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl8_112 ),
    inference(resolution,[],[f786,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t62_relat_1.p',t7_boole)).

fof(f786,plain,
    ( r2_hidden(k4_tarski(sK3(sK0,k1_xboole_0,k1_xboole_0),sK4(sK0,k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | ~ spl8_112 ),
    inference(avatar_component_clause,[],[f785])).

fof(f785,plain,
    ( spl8_112
  <=> r2_hidden(k4_tarski(sK3(sK0,k1_xboole_0,k1_xboole_0),sK4(sK0,k1_xboole_0,k1_xboole_0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_112])])).

fof(f800,plain,
    ( ~ spl8_2
    | ~ spl8_110 ),
    inference(avatar_contradiction_clause,[],[f799])).

fof(f799,plain,
    ( $false
    | ~ spl8_2
    | ~ spl8_110 ),
    inference(subsumption_resolution,[],[f796,f88])).

fof(f796,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl8_110 ),
    inference(resolution,[],[f780,f68])).

fof(f780,plain,
    ( r2_hidden(k4_tarski(sK5(sK0,k1_xboole_0,k1_xboole_0),sK4(sK0,k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | ~ spl8_110 ),
    inference(avatar_component_clause,[],[f779])).

fof(f779,plain,
    ( spl8_110
  <=> r2_hidden(k4_tarski(sK5(sK0,k1_xboole_0,k1_xboole_0),sK4(sK0,k1_xboole_0,k1_xboole_0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_110])])).

fof(f787,plain,
    ( spl8_110
    | spl8_112
    | ~ spl8_0
    | spl8_15
    | ~ spl8_64 ),
    inference(avatar_split_clause,[],[f752,f485,f139,f80,f785,f779])).

fof(f80,plain,
    ( spl8_0
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_0])])).

fof(f139,plain,
    ( spl8_15
  <=> k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f485,plain,
    ( spl8_64
  <=> ! [X3] :
        ( k1_xboole_0 = k5_relat_1(X3,k1_xboole_0)
        | r2_hidden(k4_tarski(sK3(X3,k1_xboole_0,k1_xboole_0),sK4(X3,k1_xboole_0,k1_xboole_0)),k1_xboole_0)
        | ~ v1_relat_1(X3)
        | r2_hidden(k4_tarski(sK5(X3,k1_xboole_0,k1_xboole_0),sK4(X3,k1_xboole_0,k1_xboole_0)),k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_64])])).

fof(f752,plain,
    ( r2_hidden(k4_tarski(sK3(sK0,k1_xboole_0,k1_xboole_0),sK4(sK0,k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | r2_hidden(k4_tarski(sK5(sK0,k1_xboole_0,k1_xboole_0),sK4(sK0,k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | ~ spl8_0
    | ~ spl8_15
    | ~ spl8_64 ),
    inference(subsumption_resolution,[],[f751,f140])).

fof(f140,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f139])).

fof(f751,plain,
    ( r2_hidden(k4_tarski(sK3(sK0,k1_xboole_0,k1_xboole_0),sK4(sK0,k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
    | r2_hidden(k4_tarski(sK5(sK0,k1_xboole_0,k1_xboole_0),sK4(sK0,k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | ~ spl8_0
    | ~ spl8_64 ),
    inference(resolution,[],[f486,f81])).

fof(f81,plain,
    ( v1_relat_1(sK0)
    | ~ spl8_0 ),
    inference(avatar_component_clause,[],[f80])).

fof(f486,plain,
    ( ! [X3] :
        ( ~ v1_relat_1(X3)
        | r2_hidden(k4_tarski(sK3(X3,k1_xboole_0,k1_xboole_0),sK4(X3,k1_xboole_0,k1_xboole_0)),k1_xboole_0)
        | k1_xboole_0 = k5_relat_1(X3,k1_xboole_0)
        | r2_hidden(k4_tarski(sK5(X3,k1_xboole_0,k1_xboole_0),sK4(X3,k1_xboole_0,k1_xboole_0)),k1_xboole_0) )
    | ~ spl8_64 ),
    inference(avatar_component_clause,[],[f485])).

fof(f739,plain,
    ( spl8_40
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f179,f103,f285])).

fof(f285,plain,
    ( spl8_40
  <=> ! [X1,X0] :
        ( r2_hidden(k4_tarski(sK5(X0,X1,k1_xboole_0),sK4(X0,X1,k1_xboole_0)),X1)
        | k1_xboole_0 = k5_relat_1(X0,X1)
        | r2_hidden(k4_tarski(sK3(X0,X1,k1_xboole_0),sK4(X0,X1,k1_xboole_0)),k1_xboole_0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).

fof(f103,plain,
    ( spl8_6
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f179,plain,
    ( ! [X2,X3] :
        ( r2_hidden(k4_tarski(sK5(X2,X3,k1_xboole_0),sK4(X2,X3,k1_xboole_0)),X3)
        | r2_hidden(k4_tarski(sK3(X2,X3,k1_xboole_0),sK4(X2,X3,k1_xboole_0)),k1_xboole_0)
        | k1_xboole_0 = k5_relat_1(X2,X3)
        | ~ v1_relat_1(X3)
        | ~ v1_relat_1(X2) )
    | ~ spl8_6 ),
    inference(resolution,[],[f60,f104])).

fof(f104,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f103])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK4(X0,X1,X2)),X1)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)
      | k5_relat_1(X0,X1) = X2
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ( ( ! [X5] :
                          ( ~ r2_hidden(k4_tarski(X5,sK4(X0,X1,X2)),X1)
                          | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X0) )
                      | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) )
                    & ( ( r2_hidden(k4_tarski(sK5(X0,X1,X2),sK4(X0,X1,X2)),X1)
                        & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK5(X0,X1,X2)),X0) )
                      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ( r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1)
                          & r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f39,f42,f41,f40])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                | ~ r2_hidden(k4_tarski(X3,X5),X0) )
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ? [X6] :
                ( r2_hidden(k4_tarski(X6,X4),X1)
                & r2_hidden(k4_tarski(X3,X6),X0) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ! [X5] :
              ( ~ r2_hidden(k4_tarski(X5,sK4(X0,X1,X2)),X1)
              | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X0) )
          | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) )
        & ( ? [X6] :
              ( r2_hidden(k4_tarski(X6,sK4(X0,X1,X2)),X1)
              & r2_hidden(k4_tarski(sK3(X0,X1,X2),X6),X0) )
          | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,X4),X1)
          & r2_hidden(k4_tarski(X3,X6),X0) )
     => ( r2_hidden(k4_tarski(sK5(X0,X1,X2),X4),X1)
        & r2_hidden(k4_tarski(X3,sK5(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK6(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK6(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X6] :
                            ( r2_hidden(k4_tarski(X6,X4),X1)
                            & r2_hidden(k4_tarski(X3,X6),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ? [X10] :
                            ( r2_hidden(k4_tarski(X10,X8),X1)
                            & r2_hidden(k4_tarski(X7,X10),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X3,X4] :
                      ( ( r2_hidden(k4_tarski(X3,X4),X2)
                        | ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) ) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) )
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
              ( v1_relat_1(X2)
             => ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t62_relat_1.p',d8_relat_1)).

fof(f685,plain,
    ( ~ spl8_2
    | ~ spl8_72 ),
    inference(avatar_contradiction_clause,[],[f684])).

fof(f684,plain,
    ( $false
    | ~ spl8_2
    | ~ spl8_72 ),
    inference(subsumption_resolution,[],[f677,f88])).

fof(f677,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl8_72 ),
    inference(resolution,[],[f563,f68])).

fof(f563,plain,
    ( r2_hidden(k4_tarski(sK3(k1_xboole_0,sK0,k1_xboole_0),sK4(k1_xboole_0,sK0,k1_xboole_0)),k1_xboole_0)
    | ~ spl8_72 ),
    inference(avatar_component_clause,[],[f562])).

fof(f562,plain,
    ( spl8_72
  <=> r2_hidden(k4_tarski(sK3(k1_xboole_0,sK0,k1_xboole_0),sK4(k1_xboole_0,sK0,k1_xboole_0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_72])])).

fof(f651,plain,
    ( spl8_28
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f157,f103,f207])).

fof(f207,plain,
    ( spl8_28
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k5_relat_1(X0,X1)
        | r2_hidden(k4_tarski(sK3(X0,X1,k1_xboole_0),sK4(X0,X1,k1_xboole_0)),k1_xboole_0)
        | r2_hidden(k4_tarski(sK3(X0,X1,k1_xboole_0),sK5(X0,X1,k1_xboole_0)),X0)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f157,plain,
    ( ! [X2,X3] :
        ( r2_hidden(k4_tarski(sK3(X2,X3,k1_xboole_0),sK5(X2,X3,k1_xboole_0)),X2)
        | r2_hidden(k4_tarski(sK3(X2,X3,k1_xboole_0),sK4(X2,X3,k1_xboole_0)),k1_xboole_0)
        | k1_xboole_0 = k5_relat_1(X2,X3)
        | ~ v1_relat_1(X3)
        | ~ v1_relat_1(X2) )
    | ~ spl8_6 ),
    inference(resolution,[],[f59,f104])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK5(X0,X1,X2)),X0)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)
      | k5_relat_1(X0,X1) = X2
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f564,plain,
    ( spl8_72
    | ~ spl8_0
    | spl8_13
    | ~ spl8_68 ),
    inference(avatar_split_clause,[],[f541,f533,f133,f80,f562])).

fof(f133,plain,
    ( spl8_13
  <=> k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f533,plain,
    ( spl8_68
  <=> ! [X4] :
        ( r2_hidden(k4_tarski(sK3(k1_xboole_0,X4,k1_xboole_0),sK4(k1_xboole_0,X4,k1_xboole_0)),k1_xboole_0)
        | ~ v1_relat_1(X4)
        | k1_xboole_0 = k5_relat_1(k1_xboole_0,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_68])])).

fof(f541,plain,
    ( r2_hidden(k4_tarski(sK3(k1_xboole_0,sK0,k1_xboole_0),sK4(k1_xboole_0,sK0,k1_xboole_0)),k1_xboole_0)
    | ~ spl8_0
    | ~ spl8_13
    | ~ spl8_68 ),
    inference(subsumption_resolution,[],[f539,f134])).

fof(f134,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f133])).

fof(f539,plain,
    ( r2_hidden(k4_tarski(sK3(k1_xboole_0,sK0,k1_xboole_0),sK4(k1_xboole_0,sK0,k1_xboole_0)),k1_xboole_0)
    | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)
    | ~ spl8_0
    | ~ spl8_68 ),
    inference(resolution,[],[f534,f81])).

fof(f534,plain,
    ( ! [X4] :
        ( ~ v1_relat_1(X4)
        | r2_hidden(k4_tarski(sK3(k1_xboole_0,X4,k1_xboole_0),sK4(k1_xboole_0,X4,k1_xboole_0)),k1_xboole_0)
        | k1_xboole_0 = k5_relat_1(k1_xboole_0,X4) )
    | ~ spl8_68 ),
    inference(avatar_component_clause,[],[f533])).

fof(f535,plain,
    ( spl8_68
    | ~ spl8_2
    | ~ spl8_52 ),
    inference(avatar_split_clause,[],[f531,f380,f87,f533])).

fof(f380,plain,
    ( spl8_52
  <=> ! [X3] :
        ( r2_hidden(k4_tarski(sK3(k1_xboole_0,X3,k1_xboole_0),sK4(k1_xboole_0,X3,k1_xboole_0)),k1_xboole_0)
        | r2_hidden(k4_tarski(sK3(k1_xboole_0,X3,k1_xboole_0),sK5(k1_xboole_0,X3,k1_xboole_0)),k1_xboole_0)
        | ~ v1_relat_1(X3)
        | k1_xboole_0 = k5_relat_1(k1_xboole_0,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_52])])).

fof(f531,plain,
    ( ! [X4] :
        ( r2_hidden(k4_tarski(sK3(k1_xboole_0,X4,k1_xboole_0),sK4(k1_xboole_0,X4,k1_xboole_0)),k1_xboole_0)
        | ~ v1_relat_1(X4)
        | k1_xboole_0 = k5_relat_1(k1_xboole_0,X4) )
    | ~ spl8_2
    | ~ spl8_52 ),
    inference(subsumption_resolution,[],[f529,f88])).

fof(f529,plain,
    ( ! [X4] :
        ( r2_hidden(k4_tarski(sK3(k1_xboole_0,X4,k1_xboole_0),sK4(k1_xboole_0,X4,k1_xboole_0)),k1_xboole_0)
        | ~ v1_relat_1(X4)
        | k1_xboole_0 = k5_relat_1(k1_xboole_0,X4)
        | ~ v1_xboole_0(k1_xboole_0) )
    | ~ spl8_52 ),
    inference(resolution,[],[f381,f68])).

fof(f381,plain,
    ( ! [X3] :
        ( r2_hidden(k4_tarski(sK3(k1_xboole_0,X3,k1_xboole_0),sK5(k1_xboole_0,X3,k1_xboole_0)),k1_xboole_0)
        | r2_hidden(k4_tarski(sK3(k1_xboole_0,X3,k1_xboole_0),sK4(k1_xboole_0,X3,k1_xboole_0)),k1_xboole_0)
        | ~ v1_relat_1(X3)
        | k1_xboole_0 = k5_relat_1(k1_xboole_0,X3) )
    | ~ spl8_52 ),
    inference(avatar_component_clause,[],[f380])).

fof(f487,plain,
    ( spl8_64
    | ~ spl8_6
    | ~ spl8_40 ),
    inference(avatar_split_clause,[],[f360,f285,f103,f485])).

fof(f360,plain,
    ( ! [X3] :
        ( k1_xboole_0 = k5_relat_1(X3,k1_xboole_0)
        | r2_hidden(k4_tarski(sK3(X3,k1_xboole_0,k1_xboole_0),sK4(X3,k1_xboole_0,k1_xboole_0)),k1_xboole_0)
        | ~ v1_relat_1(X3)
        | r2_hidden(k4_tarski(sK5(X3,k1_xboole_0,k1_xboole_0),sK4(X3,k1_xboole_0,k1_xboole_0)),k1_xboole_0) )
    | ~ spl8_6
    | ~ spl8_40 ),
    inference(resolution,[],[f286,f104])).

fof(f286,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k1_xboole_0 = k5_relat_1(X0,X1)
        | r2_hidden(k4_tarski(sK3(X0,X1,k1_xboole_0),sK4(X0,X1,k1_xboole_0)),k1_xboole_0)
        | ~ v1_relat_1(X0)
        | r2_hidden(k4_tarski(sK5(X0,X1,k1_xboole_0),sK4(X0,X1,k1_xboole_0)),X1) )
    | ~ spl8_40 ),
    inference(avatar_component_clause,[],[f285])).

fof(f382,plain,
    ( spl8_52
    | ~ spl8_6
    | ~ spl8_28 ),
    inference(avatar_split_clause,[],[f256,f207,f103,f380])).

fof(f256,plain,
    ( ! [X3] :
        ( r2_hidden(k4_tarski(sK3(k1_xboole_0,X3,k1_xboole_0),sK4(k1_xboole_0,X3,k1_xboole_0)),k1_xboole_0)
        | r2_hidden(k4_tarski(sK3(k1_xboole_0,X3,k1_xboole_0),sK5(k1_xboole_0,X3,k1_xboole_0)),k1_xboole_0)
        | ~ v1_relat_1(X3)
        | k1_xboole_0 = k5_relat_1(k1_xboole_0,X3) )
    | ~ spl8_6
    | ~ spl8_28 ),
    inference(resolution,[],[f208,f104])).

fof(f208,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | r2_hidden(k4_tarski(sK3(X0,X1,k1_xboole_0),sK4(X0,X1,k1_xboole_0)),k1_xboole_0)
        | r2_hidden(k4_tarski(sK3(X0,X1,k1_xboole_0),sK5(X0,X1,k1_xboole_0)),X0)
        | ~ v1_relat_1(X1)
        | k1_xboole_0 = k5_relat_1(X0,X1) )
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f207])).

fof(f141,plain,
    ( ~ spl8_13
    | ~ spl8_15 ),
    inference(avatar_split_clause,[],[f47,f139,f133])).

fof(f47,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f32])).

fof(f32,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t62_relat_1.p',t62_relat_1)).

fof(f105,plain,
    ( spl8_6
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f97,f87,f103])).

fof(f97,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl8_2 ),
    inference(resolution,[],[f50,f88])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t62_relat_1.p',cc1_relat_1)).

fof(f89,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f48,f87])).

fof(f48,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t62_relat_1.p',fc1_xboole_0)).

fof(f82,plain,(
    spl8_0 ),
    inference(avatar_split_clause,[],[f46,f80])).

fof(f46,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
