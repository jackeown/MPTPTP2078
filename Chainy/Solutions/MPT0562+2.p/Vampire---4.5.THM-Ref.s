%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0562+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:37 EST 2020

% Result     : Theorem 1.64s
% Output     : Refutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 130 expanded)
%              Number of leaves         :   14 (  43 expanded)
%              Depth                    :   17
%              Number of atoms          :  293 ( 834 expanded)
%              Number of equality atoms :   19 (  35 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4324,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f4070,f4104,f4154,f4323])).

fof(f4323,plain,
    ( spl168_1
    | ~ spl168_2
    | ~ spl168_6 ),
    inference(avatar_contradiction_clause,[],[f4322])).

fof(f4322,plain,
    ( $false
    | spl168_1
    | ~ spl168_2
    | ~ spl168_6 ),
    inference(subsumption_resolution,[],[f4316,f4069])).

fof(f4069,plain,
    ( r2_hidden(sK13,sK11)
    | ~ spl168_2 ),
    inference(avatar_component_clause,[],[f4067])).

fof(f4067,plain,
    ( spl168_2
  <=> r2_hidden(sK13,sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl168_2])])).

fof(f4316,plain,
    ( ~ r2_hidden(sK13,sK11)
    | spl168_1
    | ~ spl168_6 ),
    inference(resolution,[],[f4176,f4064])).

fof(f4064,plain,
    ( ~ r2_hidden(sK10,k10_relat_1(sK12,sK11))
    | spl168_1 ),
    inference(avatar_component_clause,[],[f4063])).

fof(f4063,plain,
    ( spl168_1
  <=> r2_hidden(sK10,k10_relat_1(sK12,sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl168_1])])).

fof(f4176,plain,
    ( ! [X2] :
        ( r2_hidden(sK10,k10_relat_1(sK12,X2))
        | ~ r2_hidden(sK13,X2) )
    | ~ spl168_6 ),
    inference(subsumption_resolution,[],[f4161,f1922])).

fof(f1922,plain,(
    v1_relat_1(sK12) ),
    inference(cnf_transformation,[],[f1478])).

fof(f1478,plain,
    ( ( ! [X3] :
          ( ~ r2_hidden(X3,sK11)
          | ~ r2_hidden(k4_tarski(sK10,X3),sK12)
          | ~ r2_hidden(X3,k2_relat_1(sK12)) )
      | ~ r2_hidden(sK10,k10_relat_1(sK12,sK11)) )
    & ( ( r2_hidden(sK13,sK11)
        & r2_hidden(k4_tarski(sK10,sK13),sK12)
        & r2_hidden(sK13,k2_relat_1(sK12)) )
      | r2_hidden(sK10,k10_relat_1(sK12,sK11)) )
    & v1_relat_1(sK12) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11,sK12,sK13])],[f1475,f1477,f1476])).

fof(f1476,plain,
    ( ? [X0,X1,X2] :
        ( ( ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X0,X4),X2)
              & r2_hidden(X4,k2_relat_1(X2)) )
          | r2_hidden(X0,k10_relat_1(X2,X1)) )
        & v1_relat_1(X2) )
   => ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK11)
            | ~ r2_hidden(k4_tarski(sK10,X3),sK12)
            | ~ r2_hidden(X3,k2_relat_1(sK12)) )
        | ~ r2_hidden(sK10,k10_relat_1(sK12,sK11)) )
      & ( ? [X4] :
            ( r2_hidden(X4,sK11)
            & r2_hidden(k4_tarski(sK10,X4),sK12)
            & r2_hidden(X4,k2_relat_1(sK12)) )
        | r2_hidden(sK10,k10_relat_1(sK12,sK11)) )
      & v1_relat_1(sK12) ) ),
    introduced(choice_axiom,[])).

fof(f1477,plain,
    ( ? [X4] :
        ( r2_hidden(X4,sK11)
        & r2_hidden(k4_tarski(sK10,X4),sK12)
        & r2_hidden(X4,k2_relat_1(sK12)) )
   => ( r2_hidden(sK13,sK11)
      & r2_hidden(k4_tarski(sK10,sK13),sK12)
      & r2_hidden(sK13,k2_relat_1(sK12)) ) ),
    introduced(choice_axiom,[])).

fof(f1475,plain,(
    ? [X0,X1,X2] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X0,X3),X2)
            | ~ r2_hidden(X3,k2_relat_1(X2)) )
        | ~ r2_hidden(X0,k10_relat_1(X2,X1)) )
      & ( ? [X4] :
            ( r2_hidden(X4,X1)
            & r2_hidden(k4_tarski(X0,X4),X2)
            & r2_hidden(X4,k2_relat_1(X2)) )
        | r2_hidden(X0,k10_relat_1(X2,X1)) )
      & v1_relat_1(X2) ) ),
    inference(rectify,[],[f1474])).

fof(f1474,plain,(
    ? [X0,X1,X2] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X0,X3),X2)
            | ~ r2_hidden(X3,k2_relat_1(X2)) )
        | ~ r2_hidden(X0,k10_relat_1(X2,X1)) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) )
        | r2_hidden(X0,k10_relat_1(X2,X1)) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f1473])).

fof(f1473,plain,(
    ? [X0,X1,X2] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X0,X3),X2)
            | ~ r2_hidden(X3,k2_relat_1(X2)) )
        | ~ r2_hidden(X0,k10_relat_1(X2,X1)) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) )
        | r2_hidden(X0,k10_relat_1(X2,X1)) )
      & v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f834])).

fof(f834,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <~> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f750])).

fof(f750,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(X0,k10_relat_1(X2,X1))
        <=> ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X0,X3),X2)
              & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f749])).

fof(f749,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

fof(f4161,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK13,X2)
        | r2_hidden(sK10,k10_relat_1(sK12,X2))
        | ~ v1_relat_1(sK12) )
    | ~ spl168_6 ),
    inference(resolution,[],[f4103,f3194])).

fof(f3194,plain,(
    ! [X6,X0,X7,X1] :
      ( ~ r2_hidden(k4_tarski(X6,X7),X0)
      | ~ r2_hidden(X7,X1)
      | r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f2085])).

fof(f2085,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1518])).

fof(f1518,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(sK32(X0,X1,X2),X4),X0) )
                | ~ r2_hidden(sK32(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK33(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK32(X0,X1,X2),sK33(X0,X1,X2)),X0) )
                | r2_hidden(sK32(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ( r2_hidden(sK34(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(X6,sK34(X0,X1,X6)),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK32,sK33,sK34])],[f1514,f1517,f1516,f1515])).

fof(f1515,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r2_hidden(k4_tarski(X3,X4),X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X3,X5),X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(sK32(X0,X1,X2),X4),X0) )
          | ~ r2_hidden(sK32(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(sK32(X0,X1,X2),X5),X0) )
          | r2_hidden(sK32(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1516,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(sK32(X0,X1,X2),X5),X0) )
     => ( r2_hidden(sK33(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK32(X0,X1,X2),sK33(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1517,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X6,X8),X0) )
     => ( r2_hidden(sK34(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(X6,sK34(X0,X1,X6)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1514,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( r2_hidden(X5,X1)
                      & r2_hidden(k4_tarski(X3,X5),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ? [X8] :
                      ( r2_hidden(X8,X1)
                      & r2_hidden(k4_tarski(X6,X8),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f1513])).

fof(f1513,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) ) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f914])).

fof(f914,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f644])).

fof(f644,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

fof(f4103,plain,
    ( r2_hidden(k4_tarski(sK10,sK13),sK12)
    | ~ spl168_6 ),
    inference(avatar_component_clause,[],[f4101])).

fof(f4101,plain,
    ( spl168_6
  <=> r2_hidden(k4_tarski(sK10,sK13),sK12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl168_6])])).

fof(f4154,plain,(
    ~ spl168_1 ),
    inference(avatar_contradiction_clause,[],[f4153])).

fof(f4153,plain,
    ( $false
    | ~ spl168_1 ),
    inference(subsumption_resolution,[],[f4152,f1922])).

fof(f4152,plain,
    ( ~ v1_relat_1(sK12)
    | ~ spl168_1 ),
    inference(subsumption_resolution,[],[f4151,f4065])).

fof(f4065,plain,
    ( r2_hidden(sK10,k10_relat_1(sK12,sK11))
    | ~ spl168_1 ),
    inference(avatar_component_clause,[],[f4063])).

fof(f4151,plain,
    ( ~ r2_hidden(sK10,k10_relat_1(sK12,sK11))
    | ~ v1_relat_1(sK12)
    | ~ spl168_1 ),
    inference(duplicate_literal_removal,[],[f4150])).

fof(f4150,plain,
    ( ~ r2_hidden(sK10,k10_relat_1(sK12,sK11))
    | ~ r2_hidden(sK10,k10_relat_1(sK12,sK11))
    | ~ v1_relat_1(sK12)
    | ~ spl168_1 ),
    inference(resolution,[],[f4140,f3195])).

fof(f3195,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK34(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f2084])).

fof(f2084,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK34(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1518])).

fof(f4140,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK34(sK12,X2,sK10),sK11)
        | ~ r2_hidden(sK10,k10_relat_1(sK12,X2)) )
    | ~ spl168_1 ),
    inference(subsumption_resolution,[],[f4137,f1922])).

fof(f4137,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK34(sK12,X2,sK10),sK11)
        | ~ r2_hidden(sK10,k10_relat_1(sK12,X2))
        | ~ v1_relat_1(sK12) )
    | ~ spl168_1 ),
    inference(resolution,[],[f4121,f3196])).

fof(f3196,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k4_tarski(X6,sK34(X0,X1,X6)),X0)
      | ~ r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f2083])).

fof(f2083,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(k4_tarski(X6,sK34(X0,X1,X6)),X0)
      | ~ r2_hidden(X6,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1518])).

fof(f4121,plain,
    ( ! [X3] :
        ( ~ r2_hidden(k4_tarski(sK10,X3),sK12)
        | ~ r2_hidden(X3,sK11) )
    | ~ spl168_1 ),
    inference(subsumption_resolution,[],[f4061,f4065])).

fof(f4061,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK11)
      | ~ r2_hidden(k4_tarski(sK10,X3),sK12)
      | ~ r2_hidden(sK10,k10_relat_1(sK12,sK11)) ) ),
    inference(subsumption_resolution,[],[f1926,f3227])).

fof(f3227,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X6,X5),X0)
      | r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f2534])).

fof(f2534,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1698])).

fof(f1698,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK99(X0,X1)),X0)
            | ~ r2_hidden(sK99(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK100(X0,X1),sK99(X0,X1)),X0)
            | r2_hidden(sK99(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK101(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK99,sK100,sK101])],[f1694,f1697,f1696,f1695])).

fof(f1695,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK99(X0,X1)),X0)
          | ~ r2_hidden(sK99(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK99(X0,X1)),X0)
          | r2_hidden(sK99(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1696,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK99(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK100(X0,X1),sK99(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1697,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK101(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1694,plain,(
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
    inference(rectify,[],[f1693])).

fof(f1693,plain,(
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
    inference(nnf_transformation,[],[f649])).

fof(f649,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f1926,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK11)
      | ~ r2_hidden(k4_tarski(sK10,X3),sK12)
      | ~ r2_hidden(X3,k2_relat_1(sK12))
      | ~ r2_hidden(sK10,k10_relat_1(sK12,sK11)) ) ),
    inference(cnf_transformation,[],[f1478])).

fof(f4104,plain,
    ( spl168_1
    | spl168_6 ),
    inference(avatar_split_clause,[],[f1924,f4101,f4063])).

fof(f1924,plain,
    ( r2_hidden(k4_tarski(sK10,sK13),sK12)
    | r2_hidden(sK10,k10_relat_1(sK12,sK11)) ),
    inference(cnf_transformation,[],[f1478])).

fof(f4070,plain,
    ( spl168_1
    | spl168_2 ),
    inference(avatar_split_clause,[],[f1925,f4067,f4063])).

fof(f1925,plain,
    ( r2_hidden(sK13,sK11)
    | r2_hidden(sK10,k10_relat_1(sK12,sK11)) ),
    inference(cnf_transformation,[],[f1478])).
%------------------------------------------------------------------------------
