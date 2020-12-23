%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0541+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:36 EST 2020

% Result     : Theorem 1.46s
% Output     : Refutation 1.46s
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
fof(f4200,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3952,f3986,f4036,f4199])).

fof(f4199,plain,
    ( spl164_1
    | ~ spl164_2
    | ~ spl164_6 ),
    inference(avatar_contradiction_clause,[],[f4198])).

fof(f4198,plain,
    ( $false
    | spl164_1
    | ~ spl164_2
    | ~ spl164_6 ),
    inference(subsumption_resolution,[],[f4192,f3951])).

fof(f3951,plain,
    ( r2_hidden(sK13,sK11)
    | ~ spl164_2 ),
    inference(avatar_component_clause,[],[f3949])).

fof(f3949,plain,
    ( spl164_2
  <=> r2_hidden(sK13,sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl164_2])])).

fof(f4192,plain,
    ( ~ r2_hidden(sK13,sK11)
    | spl164_1
    | ~ spl164_6 ),
    inference(resolution,[],[f4056,f3946])).

fof(f3946,plain,
    ( ~ r2_hidden(sK10,k9_relat_1(sK12,sK11))
    | spl164_1 ),
    inference(avatar_component_clause,[],[f3945])).

fof(f3945,plain,
    ( spl164_1
  <=> r2_hidden(sK10,k9_relat_1(sK12,sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl164_1])])).

fof(f4056,plain,
    ( ! [X1] :
        ( r2_hidden(sK10,k9_relat_1(sK12,X1))
        | ~ r2_hidden(sK13,X1) )
    | ~ spl164_6 ),
    inference(subsumption_resolution,[],[f4042,f1857])).

fof(f1857,plain,(
    v1_relat_1(sK12) ),
    inference(cnf_transformation,[],[f1424])).

fof(f1424,plain,
    ( ( ! [X3] :
          ( ~ r2_hidden(X3,sK11)
          | ~ r2_hidden(k4_tarski(X3,sK10),sK12)
          | ~ r2_hidden(X3,k1_relat_1(sK12)) )
      | ~ r2_hidden(sK10,k9_relat_1(sK12,sK11)) )
    & ( ( r2_hidden(sK13,sK11)
        & r2_hidden(k4_tarski(sK13,sK10),sK12)
        & r2_hidden(sK13,k1_relat_1(sK12)) )
      | r2_hidden(sK10,k9_relat_1(sK12,sK11)) )
    & v1_relat_1(sK12) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11,sK12,sK13])],[f1421,f1423,f1422])).

fof(f1422,plain,
    ( ? [X0,X1,X2] :
        ( ( ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | r2_hidden(X0,k9_relat_1(X2,X1)) )
        & v1_relat_1(X2) )
   => ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK11)
            | ~ r2_hidden(k4_tarski(X3,sK10),sK12)
            | ~ r2_hidden(X3,k1_relat_1(sK12)) )
        | ~ r2_hidden(sK10,k9_relat_1(sK12,sK11)) )
      & ( ? [X4] :
            ( r2_hidden(X4,sK11)
            & r2_hidden(k4_tarski(X4,sK10),sK12)
            & r2_hidden(X4,k1_relat_1(sK12)) )
        | r2_hidden(sK10,k9_relat_1(sK12,sK11)) )
      & v1_relat_1(sK12) ) ),
    introduced(choice_axiom,[])).

fof(f1423,plain,
    ( ? [X4] :
        ( r2_hidden(X4,sK11)
        & r2_hidden(k4_tarski(X4,sK10),sK12)
        & r2_hidden(X4,k1_relat_1(sK12)) )
   => ( r2_hidden(sK13,sK11)
      & r2_hidden(k4_tarski(sK13,sK10),sK12)
      & r2_hidden(sK13,k1_relat_1(sK12)) ) ),
    introduced(choice_axiom,[])).

fof(f1421,plain,(
    ? [X0,X1,X2] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X0),X2)
            | ~ r2_hidden(X3,k1_relat_1(X2)) )
        | ~ r2_hidden(X0,k9_relat_1(X2,X1)) )
      & ( ? [X4] :
            ( r2_hidden(X4,X1)
            & r2_hidden(k4_tarski(X4,X0),X2)
            & r2_hidden(X4,k1_relat_1(X2)) )
        | r2_hidden(X0,k9_relat_1(X2,X1)) )
      & v1_relat_1(X2) ) ),
    inference(rectify,[],[f1420])).

fof(f1420,plain,(
    ? [X0,X1,X2] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X0),X2)
            | ~ r2_hidden(X3,k1_relat_1(X2)) )
        | ~ r2_hidden(X0,k9_relat_1(X2,X1)) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) )
        | r2_hidden(X0,k9_relat_1(X2,X1)) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f1419])).

fof(f1419,plain,(
    ? [X0,X1,X2] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X0),X2)
            | ~ r2_hidden(X3,k1_relat_1(X2)) )
        | ~ r2_hidden(X0,k9_relat_1(X2,X1)) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) )
        | r2_hidden(X0,k9_relat_1(X2,X1)) )
      & v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f807])).

fof(f807,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <~> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f721])).

fof(f721,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(X0,k9_relat_1(X2,X1))
        <=> ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f720])).

fof(f720,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(f4042,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK13,X1)
        | r2_hidden(sK10,k9_relat_1(sK12,X1))
        | ~ v1_relat_1(sK12) )
    | ~ spl164_6 ),
    inference(resolution,[],[f3985,f3094])).

fof(f3094,plain,(
    ! [X6,X0,X7,X1] :
      ( ~ r2_hidden(k4_tarski(X7,X6),X0)
      | ~ r2_hidden(X7,X1)
      | r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f2012])).

fof(f2012,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1464])).

fof(f1464,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(X4,sK32(X0,X1,X2)),X0) )
                | ~ r2_hidden(sK32(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK33(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK33(X0,X1,X2),sK32(X0,X1,X2)),X0) )
                | r2_hidden(sK32(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ( r2_hidden(sK34(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(sK34(X0,X1,X6),X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK32,sK33,sK34])],[f1460,f1463,f1462,f1461])).

fof(f1461,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r2_hidden(k4_tarski(X4,X3),X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X5,X3),X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(X4,sK32(X0,X1,X2)),X0) )
          | ~ r2_hidden(sK32(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(X5,sK32(X0,X1,X2)),X0) )
          | r2_hidden(sK32(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1462,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X5,sK32(X0,X1,X2)),X0) )
     => ( r2_hidden(sK33(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK33(X0,X1,X2),sK32(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1463,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X8,X6),X0) )
     => ( r2_hidden(sK34(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(sK34(X0,X1,X6),X6),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1460,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( r2_hidden(X5,X1)
                      & r2_hidden(k4_tarski(X5,X3),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ? [X8] :
                      ( r2_hidden(X8,X1)
                      & r2_hidden(k4_tarski(X8,X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f1459])).

fof(f1459,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X4,X3),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) ) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f882])).

fof(f882,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f643])).

fof(f643,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_relat_1)).

fof(f3985,plain,
    ( r2_hidden(k4_tarski(sK13,sK10),sK12)
    | ~ spl164_6 ),
    inference(avatar_component_clause,[],[f3983])).

fof(f3983,plain,
    ( spl164_6
  <=> r2_hidden(k4_tarski(sK13,sK10),sK12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl164_6])])).

fof(f4036,plain,(
    ~ spl164_1 ),
    inference(avatar_contradiction_clause,[],[f4035])).

fof(f4035,plain,
    ( $false
    | ~ spl164_1 ),
    inference(subsumption_resolution,[],[f4034,f1857])).

fof(f4034,plain,
    ( ~ v1_relat_1(sK12)
    | ~ spl164_1 ),
    inference(subsumption_resolution,[],[f4033,f3947])).

fof(f3947,plain,
    ( r2_hidden(sK10,k9_relat_1(sK12,sK11))
    | ~ spl164_1 ),
    inference(avatar_component_clause,[],[f3945])).

fof(f4033,plain,
    ( ~ r2_hidden(sK10,k9_relat_1(sK12,sK11))
    | ~ v1_relat_1(sK12)
    | ~ spl164_1 ),
    inference(duplicate_literal_removal,[],[f4032])).

fof(f4032,plain,
    ( ~ r2_hidden(sK10,k9_relat_1(sK12,sK11))
    | ~ r2_hidden(sK10,k9_relat_1(sK12,sK11))
    | ~ v1_relat_1(sK12)
    | ~ spl164_1 ),
    inference(resolution,[],[f4021,f3095])).

fof(f3095,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK34(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f2011])).

fof(f2011,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK34(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1464])).

fof(f4021,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK34(sK12,X0,sK10),sK11)
        | ~ r2_hidden(sK10,k9_relat_1(sK12,X0)) )
    | ~ spl164_1 ),
    inference(subsumption_resolution,[],[f4018,f1857])).

fof(f4018,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK34(sK12,X0,sK10),sK11)
        | ~ r2_hidden(sK10,k9_relat_1(sK12,X0))
        | ~ v1_relat_1(sK12) )
    | ~ spl164_1 ),
    inference(resolution,[],[f4003,f3096])).

fof(f3096,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k4_tarski(sK34(X0,X1,X6),X6),X0)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f2010])).

fof(f2010,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK34(X0,X1,X6),X6),X0)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1464])).

fof(f4003,plain,
    ( ! [X3] :
        ( ~ r2_hidden(k4_tarski(X3,sK10),sK12)
        | ~ r2_hidden(X3,sK11) )
    | ~ spl164_1 ),
    inference(subsumption_resolution,[],[f3943,f3947])).

fof(f3943,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK11)
      | ~ r2_hidden(k4_tarski(X3,sK10),sK12)
      | ~ r2_hidden(sK10,k9_relat_1(sK12,sK11)) ) ),
    inference(subsumption_resolution,[],[f1861,f3124])).

fof(f3124,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X0)
      | r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f2444])).

fof(f2444,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1637])).

fof(f1637,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK96(X0,X1),X3),X0)
            | ~ r2_hidden(sK96(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK96(X0,X1),sK97(X0,X1)),X0)
            | r2_hidden(sK96(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK98(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK96,sK97,sK98])],[f1633,f1636,f1635,f1634])).

fof(f1634,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK96(X0,X1),X3),X0)
          | ~ r2_hidden(sK96(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK96(X0,X1),X4),X0)
          | r2_hidden(sK96(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1635,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK96(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK96(X0,X1),sK97(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1636,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK98(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1633,plain,(
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
    inference(rectify,[],[f1632])).

fof(f1632,plain,(
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
    inference(nnf_transformation,[],[f647])).

fof(f647,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f1861,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK11)
      | ~ r2_hidden(k4_tarski(X3,sK10),sK12)
      | ~ r2_hidden(X3,k1_relat_1(sK12))
      | ~ r2_hidden(sK10,k9_relat_1(sK12,sK11)) ) ),
    inference(cnf_transformation,[],[f1424])).

fof(f3986,plain,
    ( spl164_1
    | spl164_6 ),
    inference(avatar_split_clause,[],[f1859,f3983,f3945])).

fof(f1859,plain,
    ( r2_hidden(k4_tarski(sK13,sK10),sK12)
    | r2_hidden(sK10,k9_relat_1(sK12,sK11)) ),
    inference(cnf_transformation,[],[f1424])).

fof(f3952,plain,
    ( spl164_1
    | spl164_2 ),
    inference(avatar_split_clause,[],[f1860,f3949,f3945])).

fof(f1860,plain,
    ( r2_hidden(sK13,sK11)
    | r2_hidden(sK10,k9_relat_1(sK12,sK11)) ),
    inference(cnf_transformation,[],[f1424])).
%------------------------------------------------------------------------------
