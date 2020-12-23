%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:16 EST 2020

% Result     : Theorem 1.52s
% Output     : Refutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 218 expanded)
%              Number of leaves         :   31 (  90 expanded)
%              Depth                    :   15
%              Number of atoms          :  486 ( 999 expanded)
%              Number of equality atoms :   53 ( 126 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f380,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f80,f84,f88,f92,f100,f128,f136,f140,f153,f294,f364,f366,f371])).

fof(f371,plain,
    ( spl13_1
    | ~ spl13_34 ),
    inference(avatar_split_clause,[],[f367,f362,f78])).

fof(f78,plain,
    ( spl13_1
  <=> r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f362,plain,
    ( spl13_34
  <=> r2_hidden(sK6(k2_relat_1(sK1),k1_relat_1(sK0)),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_34])])).

fof(f367,plain,
    ( r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0))
    | ~ spl13_34 ),
    inference(resolution,[],[f363,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f15,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f363,plain,
    ( r2_hidden(sK6(k2_relat_1(sK1),k1_relat_1(sK0)),k1_relat_1(sK0))
    | ~ spl13_34 ),
    inference(avatar_component_clause,[],[f362])).

fof(f366,plain,
    ( ~ spl13_13
    | ~ spl13_33 ),
    inference(avatar_contradiction_clause,[],[f365])).

fof(f365,plain,
    ( $false
    | ~ spl13_13
    | ~ spl13_33 ),
    inference(subsumption_resolution,[],[f152,f360])).

fof(f360,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),X0),k5_relat_1(sK1,sK0))
    | ~ spl13_33 ),
    inference(avatar_component_clause,[],[f359])).

fof(f359,plain,
    ( spl13_33
  <=> ! [X0] : ~ r2_hidden(k4_tarski(sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),X0),k5_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_33])])).

fof(f152,plain,
    ( r2_hidden(k4_tarski(sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),sK12(k5_relat_1(sK1,sK0),sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))))),k5_relat_1(sK1,sK0))
    | ~ spl13_13 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl13_13
  <=> r2_hidden(k4_tarski(sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),sK12(k5_relat_1(sK1,sK0),sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))))),k5_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_13])])).

fof(f364,plain,
    ( spl13_33
    | spl13_34
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_28 ),
    inference(avatar_split_clause,[],[f357,f292,f134,f98,f90,f362,f359])).

fof(f90,plain,
    ( spl13_4
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).

fof(f98,plain,
    ( spl13_6
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_6])])).

fof(f134,plain,
    ( spl13_10
  <=> sK6(k2_relat_1(sK1),k1_relat_1(sK0)) = k1_funct_1(sK1,sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_10])])).

fof(f292,plain,
    ( spl13_28
  <=> ! [X1,X0] :
        ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(sK1,sK0))
        | k1_funct_1(sK1,X0) = sK5(sK1,sK0,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_28])])).

fof(f357,plain,
    ( ! [X0] :
        ( r2_hidden(sK6(k2_relat_1(sK1),k1_relat_1(sK0)),k1_relat_1(sK0))
        | ~ r2_hidden(k4_tarski(sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),X0),k5_relat_1(sK1,sK0)) )
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_10
    | ~ spl13_28 ),
    inference(superposition,[],[f354,f135])).

fof(f135,plain,
    ( sK6(k2_relat_1(sK1),k1_relat_1(sK0)) = k1_funct_1(sK1,sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))))
    | ~ spl13_10 ),
    inference(avatar_component_clause,[],[f134])).

fof(f354,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k1_funct_1(sK1,X0),k1_relat_1(sK0))
        | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(sK1,sK0)) )
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_28 ),
    inference(duplicate_literal_removal,[],[f353])).

fof(f353,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k1_funct_1(sK1,X0),k1_relat_1(sK0))
        | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(sK1,sK0))
        | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(sK1,sK0)) )
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_28 ),
    inference(superposition,[],[f329,f293])).

fof(f293,plain,
    ( ! [X0,X1] :
        ( k1_funct_1(sK1,X0) = sK5(sK1,sK0,X0,X1)
        | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(sK1,sK0)) )
    | ~ spl13_28 ),
    inference(avatar_component_clause,[],[f292])).

fof(f329,plain,
    ( ! [X2,X3] :
        ( r2_hidden(sK5(sK1,sK0,X2,X3),k1_relat_1(sK0))
        | ~ r2_hidden(k4_tarski(X2,X3),k5_relat_1(sK1,sK0)) )
    | ~ spl13_4
    | ~ spl13_6 ),
    inference(resolution,[],[f325,f74])).

fof(f74,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X0)
      | r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK10(X0,X1),X3),X0)
            | ~ r2_hidden(sK10(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK10(X0,X1),sK11(X0,X1)),X0)
            | r2_hidden(sK10(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK12(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11,sK12])],[f36,f39,f38,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK10(X0,X1),X3),X0)
          | ~ r2_hidden(sK10(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK10(X0,X1),X4),X0)
          | r2_hidden(sK10(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK10(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK10(X0,X1),sK11(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK12(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f35,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f325,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(sK5(sK1,sK0,X0,X1),X1),sK0)
        | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(sK1,sK0)) )
    | ~ spl13_4
    | ~ spl13_6 ),
    inference(resolution,[],[f319,f91])).

fof(f91,plain,
    ( v1_relat_1(sK1)
    | ~ spl13_4 ),
    inference(avatar_component_clause,[],[f90])).

fof(f319,plain,
    ( ! [X4,X5,X3] :
        ( ~ v1_relat_1(X5)
        | r2_hidden(k4_tarski(sK5(X5,sK0,X3,X4),X4),sK0)
        | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X5,sK0)) )
    | ~ spl13_6 ),
    inference(resolution,[],[f102,f99])).

fof(f99,plain,
    ( v1_relat_1(sK0)
    | ~ spl13_6 ),
    inference(avatar_component_clause,[],[f98])).

fof(f102,plain,(
    ! [X0,X8,X7,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f70,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f70,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ( ( ! [X5] :
                          ( ~ r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X1)
                          | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0) )
                      | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) )
                    & ( ( r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X1)
                        & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0) )
                      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ( r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1)
                          & r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f22,f25,f24,f23])).

fof(f23,plain,(
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
              ( ~ r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X1)
              | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0) )
          | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) )
        & ( ? [X6] :
              ( r2_hidden(k4_tarski(X6,sK3(X0,X1,X2)),X1)
              & r2_hidden(k4_tarski(sK2(X0,X1,X2),X6),X0) )
          | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,sK3(X0,X1,X2)),X1)
          & r2_hidden(k4_tarski(sK2(X0,X1,X2),X6),X0) )
     => ( r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X1)
        & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).

fof(f294,plain,
    ( ~ spl13_4
    | ~ spl13_3
    | spl13_28
    | ~ spl13_4
    | ~ spl13_6 ),
    inference(avatar_split_clause,[],[f288,f98,f90,f292,f86,f90])).

fof(f86,plain,
    ( spl13_3
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).

fof(f288,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(sK1,sK0))
        | k1_funct_1(sK1,X0) = sK5(sK1,sK0,X0,X1)
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl13_4
    | ~ spl13_6 ),
    inference(resolution,[],[f285,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f285,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,sK5(sK1,sK0,X0,X1)),sK1)
        | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(sK1,sK0)) )
    | ~ spl13_4
    | ~ spl13_6 ),
    inference(resolution,[],[f283,f91])).

fof(f283,plain,
    ( ! [X4,X5,X3] :
        ( ~ v1_relat_1(X5)
        | r2_hidden(k4_tarski(X3,sK5(X5,sK0,X3,X4)),X5)
        | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X5,sK0)) )
    | ~ spl13_6 ),
    inference(resolution,[],[f101,f99])).

fof(f101,plain,(
    ! [X0,X8,X7,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f71,f55])).

fof(f71,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f153,plain,
    ( spl13_13
    | ~ spl13_2
    | ~ spl13_11 ),
    inference(avatar_split_clause,[],[f147,f138,f82,f151])).

fof(f82,plain,
    ( spl13_2
  <=> k1_relat_1(k5_relat_1(sK1,sK0)) = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f138,plain,
    ( spl13_11
  <=> r2_hidden(sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_11])])).

fof(f147,plain,
    ( r2_hidden(k4_tarski(sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),sK12(k5_relat_1(sK1,sK0),sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))))),k5_relat_1(sK1,sK0))
    | ~ spl13_2
    | ~ spl13_11 ),
    inference(resolution,[],[f139,f108])).

fof(f108,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | r2_hidden(k4_tarski(X0,sK12(k5_relat_1(sK1,sK0),X0)),k5_relat_1(sK1,sK0)) )
    | ~ spl13_2 ),
    inference(superposition,[],[f75,f83])).

fof(f83,plain,
    ( k1_relat_1(k5_relat_1(sK1,sK0)) = k1_relat_1(sK1)
    | ~ spl13_2 ),
    inference(avatar_component_clause,[],[f82])).

fof(f75,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X5,sK12(X0,X5)),X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK12(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f139,plain,
    ( r2_hidden(sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),k1_relat_1(sK1))
    | ~ spl13_11 ),
    inference(avatar_component_clause,[],[f138])).

fof(f140,plain,
    ( spl13_11
    | ~ spl13_9 ),
    inference(avatar_split_clause,[],[f130,f126,f138])).

fof(f126,plain,
    ( spl13_9
  <=> r2_hidden(k4_tarski(sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),sK6(k2_relat_1(sK1),k1_relat_1(sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_9])])).

fof(f130,plain,
    ( r2_hidden(sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),k1_relat_1(sK1))
    | ~ spl13_9 ),
    inference(resolution,[],[f127,f74])).

fof(f127,plain,
    ( r2_hidden(k4_tarski(sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),sK6(k2_relat_1(sK1),k1_relat_1(sK0))),sK1)
    | ~ spl13_9 ),
    inference(avatar_component_clause,[],[f126])).

fof(f136,plain,
    ( ~ spl13_4
    | ~ spl13_3
    | spl13_10
    | ~ spl13_9 ),
    inference(avatar_split_clause,[],[f129,f126,f134,f86,f90])).

fof(f129,plain,
    ( sK6(k2_relat_1(sK1),k1_relat_1(sK0)) = k1_funct_1(sK1,sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl13_9 ),
    inference(resolution,[],[f127,f67])).

fof(f128,plain,
    ( spl13_9
    | spl13_1 ),
    inference(avatar_split_clause,[],[f124,f78,f126])).

fof(f124,plain,
    ( r2_hidden(k4_tarski(sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),sK6(k2_relat_1(sK1),k1_relat_1(sK0))),sK1)
    | spl13_1 ),
    inference(resolution,[],[f106,f79])).

fof(f79,plain,
    ( ~ r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0))
    | spl13_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f106,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),X1)
      | r2_hidden(k4_tarski(sK9(X0,sK6(k2_relat_1(X0),X1)),sK6(k2_relat_1(X0),X1)),X0) ) ),
    inference(resolution,[],[f73,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f73,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,k2_relat_1(X0))
      | r2_hidden(k4_tarski(sK9(X0,X5),X5),X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK9(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK7(X0,X1)),X0)
            | ~ r2_hidden(sK7(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0)
            | r2_hidden(sK7(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK9(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f30,f33,f32,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK7(X0,X1)),X0)
          | ~ r2_hidden(sK7(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK7(X0,X1)),X0)
          | r2_hidden(sK7(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK7(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK9(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f100,plain,(
    spl13_6 ),
    inference(avatar_split_clause,[],[f43,f98])).

fof(f43,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0))
    & k1_relat_1(k5_relat_1(sK1,sK0)) = k1_relat_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f19,f18])).

fof(f18,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
            & k1_relat_1(k5_relat_1(X1,X0)) = k1_relat_1(X1)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k2_relat_1(X1),k1_relat_1(sK0))
          & k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,sK0))
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k2_relat_1(X1),k1_relat_1(sK0))
        & k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,sK0))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0))
      & k1_relat_1(k5_relat_1(sK1,sK0)) = k1_relat_1(sK1)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          & k1_relat_1(k5_relat_1(X1,X0)) = k1_relat_1(X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          & k1_relat_1(k5_relat_1(X1,X0)) = k1_relat_1(X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( k1_relat_1(k5_relat_1(X1,X0)) = k1_relat_1(X1)
             => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( k1_relat_1(k5_relat_1(X1,X0)) = k1_relat_1(X1)
           => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_funct_1)).

fof(f92,plain,(
    spl13_4 ),
    inference(avatar_split_clause,[],[f45,f90])).

fof(f45,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f88,plain,(
    spl13_3 ),
    inference(avatar_split_clause,[],[f46,f86])).

fof(f46,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f84,plain,(
    spl13_2 ),
    inference(avatar_split_clause,[],[f47,f82])).

fof(f47,plain,(
    k1_relat_1(k5_relat_1(sK1,sK0)) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f80,plain,(
    ~ spl13_1 ),
    inference(avatar_split_clause,[],[f48,f78])).

fof(f48,plain,(
    ~ r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 21:03:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.49  % (11665)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.19/0.50  % (11661)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.50  % (11657)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.50  % (11663)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.51  % (11660)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.51  % (11662)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.51  % (11659)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.51  % (11678)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.19/0.51  % (11659)Refutation not found, incomplete strategy% (11659)------------------------------
% 0.19/0.51  % (11659)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (11659)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (11659)Memory used [KB]: 10746
% 0.19/0.51  % (11659)Time elapsed: 0.107 s
% 0.19/0.51  % (11659)------------------------------
% 0.19/0.51  % (11659)------------------------------
% 0.19/0.52  % (11658)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.52  % (11666)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.19/0.52  % (11680)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.19/0.52  % (11672)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.19/0.52  % (11681)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.19/0.53  % (11664)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.53  % (11679)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.53  % (11677)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.19/0.53  % (11675)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.19/0.53  % (11668)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.19/0.53  % (11679)Refutation not found, incomplete strategy% (11679)------------------------------
% 0.19/0.53  % (11679)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (11679)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.53  
% 0.19/0.53  % (11679)Memory used [KB]: 10746
% 0.19/0.53  % (11679)Time elapsed: 0.121 s
% 0.19/0.53  % (11679)------------------------------
% 0.19/0.53  % (11679)------------------------------
% 0.19/0.53  % (11673)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.19/0.53  % (11685)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.19/0.53  % (11669)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.34/0.53  % (11667)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.34/0.54  % (11686)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.34/0.54  % (11684)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.34/0.54  % (11683)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.34/0.54  % (11674)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.34/0.54  % (11670)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.34/0.54  % (11676)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.34/0.55  % (11671)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.52/0.56  % (11682)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.52/0.57  % (11676)Refutation found. Thanks to Tanya!
% 1.52/0.57  % SZS status Theorem for theBenchmark
% 1.52/0.57  % SZS output start Proof for theBenchmark
% 1.52/0.57  fof(f380,plain,(
% 1.52/0.57    $false),
% 1.52/0.57    inference(avatar_sat_refutation,[],[f80,f84,f88,f92,f100,f128,f136,f140,f153,f294,f364,f366,f371])).
% 1.52/0.57  fof(f371,plain,(
% 1.52/0.57    spl13_1 | ~spl13_34),
% 1.52/0.57    inference(avatar_split_clause,[],[f367,f362,f78])).
% 1.52/0.57  fof(f78,plain,(
% 1.52/0.57    spl13_1 <=> r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0))),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).
% 1.52/0.57  fof(f362,plain,(
% 1.52/0.57    spl13_34 <=> r2_hidden(sK6(k2_relat_1(sK1),k1_relat_1(sK0)),k1_relat_1(sK0))),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_34])])).
% 1.52/0.57  fof(f367,plain,(
% 1.52/0.57    r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0)) | ~spl13_34),
% 1.52/0.57    inference(resolution,[],[f363,f57])).
% 1.52/0.57  fof(f57,plain,(
% 1.52/0.57    ( ! [X0,X1] : (~r2_hidden(sK6(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f28])).
% 1.52/0.57  fof(f28,plain,(
% 1.52/0.57    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 1.52/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f15,f27])).
% 1.52/0.57  fof(f27,plain,(
% 1.52/0.57    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 1.52/0.57    introduced(choice_axiom,[])).
% 1.52/0.57  fof(f15,plain,(
% 1.52/0.57    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 1.52/0.57    inference(ennf_transformation,[],[f9])).
% 1.52/0.57  fof(f9,plain,(
% 1.52/0.57    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 1.52/0.57    inference(unused_predicate_definition_removal,[],[f1])).
% 1.52/0.57  fof(f1,axiom,(
% 1.52/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.52/0.57  fof(f363,plain,(
% 1.52/0.57    r2_hidden(sK6(k2_relat_1(sK1),k1_relat_1(sK0)),k1_relat_1(sK0)) | ~spl13_34),
% 1.52/0.57    inference(avatar_component_clause,[],[f362])).
% 1.52/0.57  fof(f366,plain,(
% 1.52/0.57    ~spl13_13 | ~spl13_33),
% 1.52/0.57    inference(avatar_contradiction_clause,[],[f365])).
% 1.52/0.57  fof(f365,plain,(
% 1.52/0.57    $false | (~spl13_13 | ~spl13_33)),
% 1.52/0.57    inference(subsumption_resolution,[],[f152,f360])).
% 1.52/0.57  fof(f360,plain,(
% 1.52/0.57    ( ! [X0] : (~r2_hidden(k4_tarski(sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),X0),k5_relat_1(sK1,sK0))) ) | ~spl13_33),
% 1.52/0.57    inference(avatar_component_clause,[],[f359])).
% 1.52/0.57  fof(f359,plain,(
% 1.52/0.57    spl13_33 <=> ! [X0] : ~r2_hidden(k4_tarski(sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),X0),k5_relat_1(sK1,sK0))),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_33])])).
% 1.52/0.57  fof(f152,plain,(
% 1.52/0.57    r2_hidden(k4_tarski(sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),sK12(k5_relat_1(sK1,sK0),sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))))),k5_relat_1(sK1,sK0)) | ~spl13_13),
% 1.52/0.57    inference(avatar_component_clause,[],[f151])).
% 1.52/0.57  fof(f151,plain,(
% 1.52/0.57    spl13_13 <=> r2_hidden(k4_tarski(sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),sK12(k5_relat_1(sK1,sK0),sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))))),k5_relat_1(sK1,sK0))),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_13])])).
% 1.52/0.57  fof(f364,plain,(
% 1.52/0.57    spl13_33 | spl13_34 | ~spl13_4 | ~spl13_6 | ~spl13_10 | ~spl13_28),
% 1.52/0.57    inference(avatar_split_clause,[],[f357,f292,f134,f98,f90,f362,f359])).
% 1.52/0.57  fof(f90,plain,(
% 1.52/0.57    spl13_4 <=> v1_relat_1(sK1)),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).
% 1.52/0.57  fof(f98,plain,(
% 1.52/0.57    spl13_6 <=> v1_relat_1(sK0)),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_6])])).
% 1.52/0.57  fof(f134,plain,(
% 1.52/0.57    spl13_10 <=> sK6(k2_relat_1(sK1),k1_relat_1(sK0)) = k1_funct_1(sK1,sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))))),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_10])])).
% 1.52/0.57  fof(f292,plain,(
% 1.52/0.57    spl13_28 <=> ! [X1,X0] : (~r2_hidden(k4_tarski(X0,X1),k5_relat_1(sK1,sK0)) | k1_funct_1(sK1,X0) = sK5(sK1,sK0,X0,X1))),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_28])])).
% 1.52/0.57  fof(f357,plain,(
% 1.52/0.57    ( ! [X0] : (r2_hidden(sK6(k2_relat_1(sK1),k1_relat_1(sK0)),k1_relat_1(sK0)) | ~r2_hidden(k4_tarski(sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),X0),k5_relat_1(sK1,sK0))) ) | (~spl13_4 | ~spl13_6 | ~spl13_10 | ~spl13_28)),
% 1.52/0.57    inference(superposition,[],[f354,f135])).
% 1.52/0.57  fof(f135,plain,(
% 1.52/0.57    sK6(k2_relat_1(sK1),k1_relat_1(sK0)) = k1_funct_1(sK1,sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0)))) | ~spl13_10),
% 1.52/0.57    inference(avatar_component_clause,[],[f134])).
% 1.52/0.57  fof(f354,plain,(
% 1.52/0.57    ( ! [X0,X1] : (r2_hidden(k1_funct_1(sK1,X0),k1_relat_1(sK0)) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(sK1,sK0))) ) | (~spl13_4 | ~spl13_6 | ~spl13_28)),
% 1.52/0.57    inference(duplicate_literal_removal,[],[f353])).
% 1.52/0.57  fof(f353,plain,(
% 1.52/0.57    ( ! [X0,X1] : (r2_hidden(k1_funct_1(sK1,X0),k1_relat_1(sK0)) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(sK1,sK0)) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(sK1,sK0))) ) | (~spl13_4 | ~spl13_6 | ~spl13_28)),
% 1.52/0.57    inference(superposition,[],[f329,f293])).
% 1.52/0.57  fof(f293,plain,(
% 1.52/0.57    ( ! [X0,X1] : (k1_funct_1(sK1,X0) = sK5(sK1,sK0,X0,X1) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(sK1,sK0))) ) | ~spl13_28),
% 1.52/0.57    inference(avatar_component_clause,[],[f292])).
% 1.52/0.57  fof(f329,plain,(
% 1.52/0.57    ( ! [X2,X3] : (r2_hidden(sK5(sK1,sK0,X2,X3),k1_relat_1(sK0)) | ~r2_hidden(k4_tarski(X2,X3),k5_relat_1(sK1,sK0))) ) | (~spl13_4 | ~spl13_6)),
% 1.52/0.57    inference(resolution,[],[f325,f74])).
% 1.52/0.57  fof(f74,plain,(
% 1.52/0.57    ( ! [X6,X0,X5] : (~r2_hidden(k4_tarski(X5,X6),X0) | r2_hidden(X5,k1_relat_1(X0))) )),
% 1.52/0.57    inference(equality_resolution,[],[f63])).
% 1.52/0.57  fof(f63,plain,(
% 1.52/0.57    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 1.52/0.57    inference(cnf_transformation,[],[f40])).
% 1.52/0.57  fof(f40,plain,(
% 1.52/0.57    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK10(X0,X1),X3),X0) | ~r2_hidden(sK10(X0,X1),X1)) & (r2_hidden(k4_tarski(sK10(X0,X1),sK11(X0,X1)),X0) | r2_hidden(sK10(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK12(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 1.52/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11,sK12])],[f36,f39,f38,f37])).
% 1.52/0.57  fof(f37,plain,(
% 1.52/0.57    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK10(X0,X1),X3),X0) | ~r2_hidden(sK10(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK10(X0,X1),X4),X0) | r2_hidden(sK10(X0,X1),X1))))),
% 1.52/0.57    introduced(choice_axiom,[])).
% 1.52/0.57  fof(f38,plain,(
% 1.52/0.57    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK10(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK10(X0,X1),sK11(X0,X1)),X0))),
% 1.52/0.57    introduced(choice_axiom,[])).
% 1.52/0.57  fof(f39,plain,(
% 1.52/0.57    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK12(X0,X5)),X0))),
% 1.52/0.57    introduced(choice_axiom,[])).
% 1.52/0.57  fof(f36,plain,(
% 1.52/0.57    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 1.52/0.57    inference(rectify,[],[f35])).
% 1.52/0.57  fof(f35,plain,(
% 1.52/0.57    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 1.52/0.57    inference(nnf_transformation,[],[f2])).
% 1.52/0.57  fof(f2,axiom,(
% 1.52/0.57    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 1.52/0.57  fof(f325,plain,(
% 1.52/0.57    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK5(sK1,sK0,X0,X1),X1),sK0) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(sK1,sK0))) ) | (~spl13_4 | ~spl13_6)),
% 1.52/0.57    inference(resolution,[],[f319,f91])).
% 1.52/0.57  fof(f91,plain,(
% 1.52/0.57    v1_relat_1(sK1) | ~spl13_4),
% 1.52/0.57    inference(avatar_component_clause,[],[f90])).
% 1.52/0.57  fof(f319,plain,(
% 1.52/0.57    ( ! [X4,X5,X3] : (~v1_relat_1(X5) | r2_hidden(k4_tarski(sK5(X5,sK0,X3,X4),X4),sK0) | ~r2_hidden(k4_tarski(X3,X4),k5_relat_1(X5,sK0))) ) | ~spl13_6),
% 1.52/0.57    inference(resolution,[],[f102,f99])).
% 1.52/0.57  fof(f99,plain,(
% 1.52/0.57    v1_relat_1(sK0) | ~spl13_6),
% 1.52/0.57    inference(avatar_component_clause,[],[f98])).
% 1.52/0.57  fof(f102,plain,(
% 1.52/0.57    ( ! [X0,X8,X7,X1] : (~v1_relat_1(X1) | ~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1) | ~v1_relat_1(X0)) )),
% 1.52/0.57    inference(subsumption_resolution,[],[f70,f55])).
% 1.52/0.57  fof(f55,plain,(
% 1.52/0.57    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f14])).
% 1.52/0.57  fof(f14,plain,(
% 1.52/0.57    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.52/0.57    inference(flattening,[],[f13])).
% 1.52/0.57  fof(f13,plain,(
% 1.52/0.57    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.52/0.57    inference(ennf_transformation,[],[f5])).
% 1.52/0.57  fof(f5,axiom,(
% 1.52/0.57    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.52/0.57  fof(f70,plain,(
% 1.52/0.57    ( ! [X0,X8,X7,X1] : (r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1) | ~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.52/0.57    inference(equality_resolution,[],[f50])).
% 1.52/0.57  fof(f50,plain,(
% 1.52/0.57    ( ! [X2,X0,X8,X7,X1] : (r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1) | ~r2_hidden(k4_tarski(X7,X8),X2) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f26])).
% 1.52/0.57  fof(f26,plain,(
% 1.52/0.57    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ((! [X5] : (~r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0)) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & ((r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.52/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f22,f25,f24,f23])).
% 1.52/0.57  fof(f23,plain,(
% 1.52/0.57    ! [X2,X1,X0] : (? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((! [X5] : (~r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,sK3(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X6),X0)) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2))))),
% 1.52/0.57    introduced(choice_axiom,[])).
% 1.52/0.57  fof(f24,plain,(
% 1.52/0.57    ! [X2,X1,X0] : (? [X6] : (r2_hidden(k4_tarski(X6,sK3(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X6),X0)) => (r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK4(X0,X1,X2)),X0)))),
% 1.52/0.57    introduced(choice_axiom,[])).
% 1.52/0.57  fof(f25,plain,(
% 1.52/0.57    ! [X8,X7,X1,X0] : (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) => (r2_hidden(k4_tarski(sK5(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0)))),
% 1.52/0.57    introduced(choice_axiom,[])).
% 1.52/0.57  fof(f22,plain,(
% 1.52/0.57    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.52/0.57    inference(rectify,[],[f21])).
% 1.52/0.57  fof(f21,plain,(
% 1.52/0.57    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0))) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.52/0.57    inference(nnf_transformation,[],[f12])).
% 1.52/0.57  fof(f12,plain,(
% 1.52/0.57    ! [X0] : (! [X1] : (! [X2] : ((k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.52/0.57    inference(ennf_transformation,[],[f4])).
% 1.52/0.57  fof(f4,axiom,(
% 1.52/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))))))),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).
% 1.52/0.57  fof(f294,plain,(
% 1.52/0.57    ~spl13_4 | ~spl13_3 | spl13_28 | ~spl13_4 | ~spl13_6),
% 1.52/0.57    inference(avatar_split_clause,[],[f288,f98,f90,f292,f86,f90])).
% 1.52/0.57  fof(f86,plain,(
% 1.52/0.57    spl13_3 <=> v1_funct_1(sK1)),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).
% 1.52/0.57  fof(f288,plain,(
% 1.52/0.57    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k5_relat_1(sK1,sK0)) | k1_funct_1(sK1,X0) = sK5(sK1,sK0,X0,X1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) ) | (~spl13_4 | ~spl13_6)),
% 1.52/0.57    inference(resolution,[],[f285,f67])).
% 1.52/0.57  fof(f67,plain,(
% 1.52/0.57    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) = X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f42])).
% 1.52/0.57  fof(f42,plain,(
% 1.52/0.57    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.52/0.57    inference(flattening,[],[f41])).
% 1.52/0.57  fof(f41,plain,(
% 1.52/0.57    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.52/0.57    inference(nnf_transformation,[],[f17])).
% 1.52/0.57  fof(f17,plain,(
% 1.52/0.57    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.52/0.57    inference(flattening,[],[f16])).
% 1.52/0.57  fof(f16,plain,(
% 1.52/0.57    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.52/0.57    inference(ennf_transformation,[],[f6])).
% 1.52/0.57  fof(f6,axiom,(
% 1.52/0.57    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 1.52/0.57  fof(f285,plain,(
% 1.52/0.57    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,sK5(sK1,sK0,X0,X1)),sK1) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(sK1,sK0))) ) | (~spl13_4 | ~spl13_6)),
% 1.52/0.57    inference(resolution,[],[f283,f91])).
% 1.52/0.57  fof(f283,plain,(
% 1.52/0.57    ( ! [X4,X5,X3] : (~v1_relat_1(X5) | r2_hidden(k4_tarski(X3,sK5(X5,sK0,X3,X4)),X5) | ~r2_hidden(k4_tarski(X3,X4),k5_relat_1(X5,sK0))) ) | ~spl13_6),
% 1.52/0.57    inference(resolution,[],[f101,f99])).
% 1.52/0.57  fof(f101,plain,(
% 1.52/0.57    ( ! [X0,X8,X7,X1] : (~v1_relat_1(X1) | ~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0) | ~v1_relat_1(X0)) )),
% 1.52/0.57    inference(subsumption_resolution,[],[f71,f55])).
% 1.52/0.57  fof(f71,plain,(
% 1.52/0.57    ( ! [X0,X8,X7,X1] : (r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0) | ~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.52/0.57    inference(equality_resolution,[],[f49])).
% 1.52/0.57  fof(f49,plain,(
% 1.52/0.57    ( ! [X2,X0,X8,X7,X1] : (r2_hidden(k4_tarski(X7,sK5(X0,X1,X7,X8)),X0) | ~r2_hidden(k4_tarski(X7,X8),X2) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f26])).
% 1.52/0.57  fof(f153,plain,(
% 1.52/0.57    spl13_13 | ~spl13_2 | ~spl13_11),
% 1.52/0.57    inference(avatar_split_clause,[],[f147,f138,f82,f151])).
% 1.52/0.57  fof(f82,plain,(
% 1.52/0.57    spl13_2 <=> k1_relat_1(k5_relat_1(sK1,sK0)) = k1_relat_1(sK1)),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).
% 1.52/0.57  fof(f138,plain,(
% 1.52/0.57    spl13_11 <=> r2_hidden(sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),k1_relat_1(sK1))),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_11])])).
% 1.52/0.57  fof(f147,plain,(
% 1.52/0.57    r2_hidden(k4_tarski(sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),sK12(k5_relat_1(sK1,sK0),sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))))),k5_relat_1(sK1,sK0)) | (~spl13_2 | ~spl13_11)),
% 1.52/0.57    inference(resolution,[],[f139,f108])).
% 1.52/0.57  fof(f108,plain,(
% 1.52/0.57    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | r2_hidden(k4_tarski(X0,sK12(k5_relat_1(sK1,sK0),X0)),k5_relat_1(sK1,sK0))) ) | ~spl13_2),
% 1.52/0.57    inference(superposition,[],[f75,f83])).
% 1.52/0.57  fof(f83,plain,(
% 1.52/0.57    k1_relat_1(k5_relat_1(sK1,sK0)) = k1_relat_1(sK1) | ~spl13_2),
% 1.52/0.57    inference(avatar_component_clause,[],[f82])).
% 1.52/0.57  fof(f75,plain,(
% 1.52/0.57    ( ! [X0,X5] : (~r2_hidden(X5,k1_relat_1(X0)) | r2_hidden(k4_tarski(X5,sK12(X0,X5)),X0)) )),
% 1.52/0.57    inference(equality_resolution,[],[f62])).
% 1.52/0.57  fof(f62,plain,(
% 1.52/0.57    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK12(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 1.52/0.57    inference(cnf_transformation,[],[f40])).
% 1.52/0.57  fof(f139,plain,(
% 1.52/0.57    r2_hidden(sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),k1_relat_1(sK1)) | ~spl13_11),
% 1.52/0.57    inference(avatar_component_clause,[],[f138])).
% 1.52/0.57  fof(f140,plain,(
% 1.52/0.57    spl13_11 | ~spl13_9),
% 1.52/0.57    inference(avatar_split_clause,[],[f130,f126,f138])).
% 1.52/0.57  fof(f126,plain,(
% 1.52/0.57    spl13_9 <=> r2_hidden(k4_tarski(sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),sK6(k2_relat_1(sK1),k1_relat_1(sK0))),sK1)),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_9])])).
% 1.52/0.57  fof(f130,plain,(
% 1.52/0.57    r2_hidden(sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),k1_relat_1(sK1)) | ~spl13_9),
% 1.52/0.57    inference(resolution,[],[f127,f74])).
% 1.52/0.57  fof(f127,plain,(
% 1.52/0.57    r2_hidden(k4_tarski(sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),sK6(k2_relat_1(sK1),k1_relat_1(sK0))),sK1) | ~spl13_9),
% 1.52/0.57    inference(avatar_component_clause,[],[f126])).
% 1.52/0.57  fof(f136,plain,(
% 1.52/0.57    ~spl13_4 | ~spl13_3 | spl13_10 | ~spl13_9),
% 1.52/0.57    inference(avatar_split_clause,[],[f129,f126,f134,f86,f90])).
% 1.52/0.57  fof(f129,plain,(
% 1.52/0.57    sK6(k2_relat_1(sK1),k1_relat_1(sK0)) = k1_funct_1(sK1,sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0)))) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl13_9),
% 1.52/0.57    inference(resolution,[],[f127,f67])).
% 1.52/0.58  fof(f128,plain,(
% 1.52/0.58    spl13_9 | spl13_1),
% 1.52/0.58    inference(avatar_split_clause,[],[f124,f78,f126])).
% 1.52/0.58  fof(f124,plain,(
% 1.52/0.58    r2_hidden(k4_tarski(sK9(sK1,sK6(k2_relat_1(sK1),k1_relat_1(sK0))),sK6(k2_relat_1(sK1),k1_relat_1(sK0))),sK1) | spl13_1),
% 1.52/0.58    inference(resolution,[],[f106,f79])).
% 1.52/0.58  fof(f79,plain,(
% 1.52/0.58    ~r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0)) | spl13_1),
% 1.52/0.58    inference(avatar_component_clause,[],[f78])).
% 1.52/0.58  fof(f106,plain,(
% 1.52/0.58    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),X1) | r2_hidden(k4_tarski(sK9(X0,sK6(k2_relat_1(X0),X1)),sK6(k2_relat_1(X0),X1)),X0)) )),
% 1.52/0.58    inference(resolution,[],[f73,f56])).
% 1.52/0.58  fof(f56,plain,(
% 1.52/0.58    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.52/0.58    inference(cnf_transformation,[],[f28])).
% 1.52/0.58  fof(f73,plain,(
% 1.52/0.58    ( ! [X0,X5] : (~r2_hidden(X5,k2_relat_1(X0)) | r2_hidden(k4_tarski(sK9(X0,X5),X5),X0)) )),
% 1.52/0.58    inference(equality_resolution,[],[f58])).
% 1.52/0.58  fof(f58,plain,(
% 1.52/0.58    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK9(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 1.52/0.58    inference(cnf_transformation,[],[f34])).
% 1.52/0.58  fof(f34,plain,(
% 1.52/0.58    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK7(X0,X1)),X0) | ~r2_hidden(sK7(X0,X1),X1)) & (r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0) | r2_hidden(sK7(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK9(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 1.52/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f30,f33,f32,f31])).
% 1.52/0.58  fof(f31,plain,(
% 1.52/0.58    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK7(X0,X1)),X0) | ~r2_hidden(sK7(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK7(X0,X1)),X0) | r2_hidden(sK7(X0,X1),X1))))),
% 1.52/0.58    introduced(choice_axiom,[])).
% 1.52/0.58  fof(f32,plain,(
% 1.52/0.58    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK7(X0,X1)),X0) => r2_hidden(k4_tarski(sK8(X0,X1),sK7(X0,X1)),X0))),
% 1.52/0.58    introduced(choice_axiom,[])).
% 1.52/0.58  fof(f33,plain,(
% 1.52/0.58    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK9(X0,X5),X5),X0))),
% 1.52/0.58    introduced(choice_axiom,[])).
% 1.52/0.58  fof(f30,plain,(
% 1.52/0.58    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 1.52/0.58    inference(rectify,[],[f29])).
% 1.52/0.58  fof(f29,plain,(
% 1.52/0.58    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 1.52/0.58    inference(nnf_transformation,[],[f3])).
% 1.52/0.58  fof(f3,axiom,(
% 1.52/0.58    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 1.52/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 1.52/0.58  fof(f100,plain,(
% 1.52/0.58    spl13_6),
% 1.52/0.58    inference(avatar_split_clause,[],[f43,f98])).
% 1.52/0.58  fof(f43,plain,(
% 1.52/0.58    v1_relat_1(sK0)),
% 1.52/0.58    inference(cnf_transformation,[],[f20])).
% 1.52/0.58  fof(f20,plain,(
% 1.52/0.58    (~r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0)) & k1_relat_1(k5_relat_1(sK1,sK0)) = k1_relat_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 1.52/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f19,f18])).
% 1.52/0.58  fof(f18,plain,(
% 1.52/0.58    ? [X0] : (? [X1] : (~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & k1_relat_1(k5_relat_1(X1,X0)) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k2_relat_1(X1),k1_relat_1(sK0)) & k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,sK0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 1.52/0.58    introduced(choice_axiom,[])).
% 1.52/0.58  fof(f19,plain,(
% 1.52/0.58    ? [X1] : (~r1_tarski(k2_relat_1(X1),k1_relat_1(sK0)) & k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,sK0)) & v1_funct_1(X1) & v1_relat_1(X1)) => (~r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0)) & k1_relat_1(k5_relat_1(sK1,sK0)) = k1_relat_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 1.52/0.58    introduced(choice_axiom,[])).
% 1.52/0.58  fof(f11,plain,(
% 1.52/0.58    ? [X0] : (? [X1] : (~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & k1_relat_1(k5_relat_1(X1,X0)) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.52/0.58    inference(flattening,[],[f10])).
% 1.52/0.58  fof(f10,plain,(
% 1.52/0.58    ? [X0] : (? [X1] : ((~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & k1_relat_1(k5_relat_1(X1,X0)) = k1_relat_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.52/0.58    inference(ennf_transformation,[],[f8])).
% 1.52/0.58  fof(f8,negated_conjecture,(
% 1.52/0.58    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_relat_1(k5_relat_1(X1,X0)) = k1_relat_1(X1) => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)))))),
% 1.52/0.58    inference(negated_conjecture,[],[f7])).
% 1.52/0.58  fof(f7,conjecture,(
% 1.52/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_relat_1(k5_relat_1(X1,X0)) = k1_relat_1(X1) => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)))))),
% 1.52/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_funct_1)).
% 1.52/0.58  fof(f92,plain,(
% 1.52/0.58    spl13_4),
% 1.52/0.58    inference(avatar_split_clause,[],[f45,f90])).
% 1.52/0.58  fof(f45,plain,(
% 1.52/0.58    v1_relat_1(sK1)),
% 1.52/0.58    inference(cnf_transformation,[],[f20])).
% 1.52/0.58  fof(f88,plain,(
% 1.52/0.58    spl13_3),
% 1.52/0.58    inference(avatar_split_clause,[],[f46,f86])).
% 1.52/0.58  fof(f46,plain,(
% 1.52/0.58    v1_funct_1(sK1)),
% 1.52/0.58    inference(cnf_transformation,[],[f20])).
% 1.52/0.58  fof(f84,plain,(
% 1.52/0.58    spl13_2),
% 1.52/0.58    inference(avatar_split_clause,[],[f47,f82])).
% 1.52/0.58  fof(f47,plain,(
% 1.52/0.58    k1_relat_1(k5_relat_1(sK1,sK0)) = k1_relat_1(sK1)),
% 1.52/0.58    inference(cnf_transformation,[],[f20])).
% 1.52/0.58  fof(f80,plain,(
% 1.52/0.58    ~spl13_1),
% 1.52/0.58    inference(avatar_split_clause,[],[f48,f78])).
% 1.52/0.58  fof(f48,plain,(
% 1.52/0.58    ~r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0))),
% 1.52/0.58    inference(cnf_transformation,[],[f20])).
% 1.52/0.58  % SZS output end Proof for theBenchmark
% 1.52/0.58  % (11676)------------------------------
% 1.52/0.58  % (11676)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.58  % (11676)Termination reason: Refutation
% 1.52/0.58  
% 1.52/0.58  % (11676)Memory used [KB]: 11129
% 1.52/0.58  % (11676)Time elapsed: 0.175 s
% 1.52/0.58  % (11676)------------------------------
% 1.52/0.58  % (11676)------------------------------
% 1.52/0.58  % (11656)Success in time 0.221 s
%------------------------------------------------------------------------------
