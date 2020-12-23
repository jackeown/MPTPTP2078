%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0675+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:26 EST 2020

% Result     : Theorem 0.11s
% Output     : Refutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 474 expanded)
%              Number of leaves         :   23 ( 175 expanded)
%              Depth                    :   18
%              Number of atoms          :  542 (3356 expanded)
%              Number of equality atoms :  163 (1190 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2033,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f62,f67,f72,f77,f608,f618,f722,f1478,f1487,f2030,f2031,f2032])).

fof(f2032,plain,
    ( sK0 != sK4(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1)))
    | sK3(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1))) != k1_funct_1(sK2,sK4(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1))))
    | k1_funct_1(sK2,sK0) = sK3(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2031,plain,
    ( sK1 != sK4(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1)))
    | sK3(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1))) != k1_funct_1(sK2,sK4(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1))))
    | k1_funct_1(sK2,sK1) = sK3(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2030,plain,
    ( spl7_34
    | spl7_35
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f2015,f1475,f2027,f2023])).

fof(f2023,plain,
    ( spl7_34
  <=> sK1 = sK4(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f2027,plain,
    ( spl7_35
  <=> sK0 = sK4(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f1475,plain,
    ( spl7_24
  <=> r2_hidden(sK4(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1))),k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f2015,plain,
    ( sK0 = sK4(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1)))
    | sK1 = sK4(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1)))
    | ~ spl7_24 ),
    inference(resolution,[],[f1477,f52])).

fof(f52,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_tarski(X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK6(X0,X1,X2) != X1
              & sK6(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( sK6(X0,X1,X2) = X1
            | sK6(X0,X1,X2) = X0
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f20,f21])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK6(X0,X1,X2) != X1
            & sK6(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( sK6(X0,X1,X2) = X1
          | sK6(X0,X1,X2) = X0
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f1477,plain,
    ( r2_hidden(sK4(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1))),k2_tarski(sK0,sK1))
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f1475])).

fof(f1487,plain,
    ( spl7_23
    | spl7_1
    | ~ spl7_4
    | ~ spl7_5
    | spl7_22 ),
    inference(avatar_split_clause,[],[f1486,f716,f74,f69,f54,f1470])).

fof(f1470,plain,
    ( spl7_23
  <=> sK3(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1))) = k1_funct_1(sK2,sK4(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f54,plain,
    ( spl7_1
  <=> k9_relat_1(sK2,k2_tarski(sK0,sK1)) = k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f69,plain,
    ( spl7_4
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f74,plain,
    ( spl7_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f716,plain,
    ( spl7_22
  <=> r2_hidden(sK3(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1))),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f1486,plain,
    ( sK3(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1))) = k1_funct_1(sK2,sK4(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1))))
    | spl7_1
    | ~ spl7_4
    | ~ spl7_5
    | spl7_22 ),
    inference(subsumption_resolution,[],[f1485,f76])).

fof(f76,plain,
    ( v1_relat_1(sK2)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f74])).

fof(f1485,plain,
    ( sK3(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1))) = k1_funct_1(sK2,sK4(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1))))
    | ~ v1_relat_1(sK2)
    | spl7_1
    | ~ spl7_4
    | spl7_22 ),
    inference(subsumption_resolution,[],[f1484,f71])).

fof(f71,plain,
    ( v1_funct_1(sK2)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f69])).

fof(f1484,plain,
    ( sK3(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1))) = k1_funct_1(sK2,sK4(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1))))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl7_1
    | spl7_22 ),
    inference(subsumption_resolution,[],[f1468,f56])).

fof(f56,plain,
    ( k9_relat_1(sK2,k2_tarski(sK0,sK1)) != k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f1468,plain,
    ( sK3(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1))) = k1_funct_1(sK2,sK4(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1))))
    | k9_relat_1(sK2,k2_tarski(sK0,sK1)) = k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl7_22 ),
    inference(resolution,[],[f718,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X2)
      | sK3(X0,X1,X2) = k1_funct_1(X0,sK4(X0,X1,X2))
      | k9_relat_1(X0,X1) = X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( k1_funct_1(X0,X4) != sK3(X0,X1,X2)
                    | ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(X4,k1_relat_1(X0)) )
                | ~ r2_hidden(sK3(X0,X1,X2),X2) )
              & ( ( sK3(X0,X1,X2) = k1_funct_1(X0,sK4(X0,X1,X2))
                  & r2_hidden(sK4(X0,X1,X2),X1)
                  & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK5(X0,X1,X6)) = X6
                    & r2_hidden(sK5(X0,X1,X6),X1)
                    & r2_hidden(sK5(X0,X1,X6),k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f13,f16,f15,f14])).

fof(f14,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( k1_funct_1(X0,X4) != X3
                | ~ r2_hidden(X4,X1)
                | ~ r2_hidden(X4,k1_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( k1_funct_1(X0,X5) = X3
                & r2_hidden(X5,X1)
                & r2_hidden(X5,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( k1_funct_1(X0,X4) != sK3(X0,X1,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,k1_relat_1(X0)) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( k1_funct_1(X0,X5) = sK3(X0,X1,X2)
              & r2_hidden(X5,X1)
              & r2_hidden(X5,k1_relat_1(X0)) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = sK3(X0,X1,X2)
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( sK3(X0,X1,X2) = k1_funct_1(X0,sK4(X0,X1,X2))
        & r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK5(X0,X1,X6)) = X6
        & r2_hidden(sK5(X0,X1,X6),X1)
        & r2_hidden(sK5(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( k1_funct_1(X0,X5) = X3
                      & r2_hidden(X5,X1)
                      & r2_hidden(X5,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ? [X8] :
                      ( k1_funct_1(X0,X8) = X6
                      & r2_hidden(X8,X1)
                      & r2_hidden(X8,k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) ) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).

fof(f718,plain,
    ( ~ r2_hidden(sK3(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1))),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1)))
    | spl7_22 ),
    inference(avatar_component_clause,[],[f716])).

fof(f1478,plain,
    ( spl7_24
    | spl7_1
    | ~ spl7_4
    | ~ spl7_5
    | spl7_22 ),
    inference(avatar_split_clause,[],[f1466,f716,f74,f69,f54,f1475])).

fof(f1466,plain,
    ( r2_hidden(sK4(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1))),k2_tarski(sK0,sK1))
    | spl7_1
    | ~ spl7_4
    | ~ spl7_5
    | spl7_22 ),
    inference(unit_resulting_resolution,[],[f76,f71,f56,f718,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X1)
      | k9_relat_1(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f722,plain,
    ( ~ spl7_22
    | spl7_15
    | spl7_16 ),
    inference(avatar_split_clause,[],[f721,f615,f605,f716])).

fof(f605,plain,
    ( spl7_15
  <=> k1_funct_1(sK2,sK1) = sK3(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f615,plain,
    ( spl7_16
  <=> k1_funct_1(sK2,sK0) = sK3(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f721,plain,
    ( ~ r2_hidden(sK3(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1))),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1)))
    | spl7_15
    | spl7_16 ),
    inference(forward_demodulation,[],[f694,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f694,plain,
    ( ~ r2_hidden(sK3(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1))),k2_tarski(k1_funct_1(sK2,sK1),k1_funct_1(sK2,sK0)))
    | spl7_15
    | spl7_16 ),
    inference(unit_resulting_resolution,[],[f607,f617,f52])).

fof(f617,plain,
    ( k1_funct_1(sK2,sK0) != sK3(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1)))
    | spl7_16 ),
    inference(avatar_component_clause,[],[f615])).

fof(f607,plain,
    ( k1_funct_1(sK2,sK1) != sK3(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1)))
    | spl7_15 ),
    inference(avatar_component_clause,[],[f605])).

fof(f618,plain,
    ( ~ spl7_16
    | spl7_1
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f613,f74,f69,f64,f54,f615])).

fof(f64,plain,
    ( spl7_3
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f613,plain,
    ( k1_funct_1(sK2,sK0) != sK3(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1)))
    | spl7_1
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(unit_resulting_resolution,[],[f51,f56,f173,f331])).

fof(f331,plain,
    ( ! [X4,X2,X3] :
        ( k1_funct_1(sK2,sK0) != sK3(sK2,X3,X4)
        | k9_relat_1(sK2,X3) = X4
        | ~ r2_hidden(sK5(sK2,k2_tarski(sK0,X2),k1_funct_1(sK2,sK0)),X3)
        | ~ r2_hidden(k1_funct_1(sK2,sK0),X4) )
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(inner_rewriting,[],[f330])).

fof(f330,plain,
    ( ! [X4,X2,X3] :
        ( k1_funct_1(sK2,sK0) != sK3(sK2,X3,X4)
        | k9_relat_1(sK2,X3) = X4
        | ~ r2_hidden(sK5(sK2,k2_tarski(sK0,X2),k1_funct_1(sK2,sK0)),X3)
        | ~ r2_hidden(sK3(sK2,X3,X4),X4) )
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f329,f76])).

fof(f329,plain,
    ( ! [X4,X2,X3] :
        ( k1_funct_1(sK2,sK0) != sK3(sK2,X3,X4)
        | k9_relat_1(sK2,X3) = X4
        | ~ r2_hidden(sK5(sK2,k2_tarski(sK0,X2),k1_funct_1(sK2,sK0)),X3)
        | ~ r2_hidden(sK3(sK2,X3,X4),X4)
        | ~ v1_relat_1(sK2) )
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f328,f71])).

fof(f328,plain,
    ( ! [X4,X2,X3] :
        ( k1_funct_1(sK2,sK0) != sK3(sK2,X3,X4)
        | k9_relat_1(sK2,X3) = X4
        | ~ r2_hidden(sK5(sK2,k2_tarski(sK0,X2),k1_funct_1(sK2,sK0)),X3)
        | ~ r2_hidden(sK3(sK2,X3,X4),X4)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f324,f172])).

fof(f172,plain,
    ( ! [X0] : r2_hidden(sK5(sK2,k2_tarski(sK0,X0),k1_funct_1(sK2,sK0)),k1_relat_1(sK2))
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(unit_resulting_resolution,[],[f76,f71,f89,f47])).

fof(f47,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f89,plain,
    ( ! [X0] : r2_hidden(k1_funct_1(sK2,sK0),k9_relat_1(sK2,k2_tarski(sK0,X0)))
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(unit_resulting_resolution,[],[f76,f71,f51,f66,f44])).

fof(f44,plain,(
    ! [X0,X7,X1] :
      ( r2_hidden(k1_funct_1(X0,X7),k9_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X7,X1] :
      ( r2_hidden(k1_funct_1(X0,X7),X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | k1_funct_1(X0,X7) != X6
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f66,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f64])).

fof(f324,plain,
    ( ! [X4,X2,X3] :
        ( k1_funct_1(sK2,sK0) != sK3(sK2,X3,X4)
        | k9_relat_1(sK2,X3) = X4
        | ~ r2_hidden(sK5(sK2,k2_tarski(sK0,X2),k1_funct_1(sK2,sK0)),X3)
        | ~ r2_hidden(sK5(sK2,k2_tarski(sK0,X2),k1_funct_1(sK2,sK0)),k1_relat_1(sK2))
        | ~ r2_hidden(sK3(sK2,X3,X4),X4)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(superposition,[],[f35,f174])).

fof(f174,plain,
    ( ! [X0] : k1_funct_1(sK2,sK0) = k1_funct_1(sK2,sK5(sK2,k2_tarski(sK0,X0),k1_funct_1(sK2,sK0)))
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(unit_resulting_resolution,[],[f76,f71,f89,f45])).

fof(f45,plain,(
    ! [X6,X0,X1] :
      ( ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | k1_funct_1(X0,sK5(X0,X1,X6)) = X6
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_funct_1(X0,sK5(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f35,plain,(
    ! [X4,X2,X0,X1] :
      ( k1_funct_1(X0,X4) != sK3(X0,X1,X2)
      | k9_relat_1(X0,X1) = X2
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f173,plain,
    ( ! [X0] : r2_hidden(sK5(sK2,k2_tarski(sK0,X0),k1_funct_1(sK2,sK0)),k2_tarski(sK0,X0))
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(unit_resulting_resolution,[],[f76,f71,f89,f46])).

fof(f46,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f51,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f608,plain,
    ( ~ spl7_15
    | spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f603,f74,f69,f59,f54,f605])).

fof(f59,plain,
    ( spl7_2
  <=> r2_hidden(sK1,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f603,plain,
    ( k1_funct_1(sK2,sK1) != sK3(sK2,k2_tarski(sK0,sK1),k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1)))
    | spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(unit_resulting_resolution,[],[f49,f56,f155,f298])).

fof(f298,plain,
    ( ! [X4,X2,X3] :
        ( k1_funct_1(sK2,sK1) != sK3(sK2,X3,X4)
        | k9_relat_1(sK2,X3) = X4
        | ~ r2_hidden(sK5(sK2,k2_tarski(X2,sK1),k1_funct_1(sK2,sK1)),X3)
        | ~ r2_hidden(k1_funct_1(sK2,sK1),X4) )
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(inner_rewriting,[],[f297])).

fof(f297,plain,
    ( ! [X4,X2,X3] :
        ( k1_funct_1(sK2,sK1) != sK3(sK2,X3,X4)
        | k9_relat_1(sK2,X3) = X4
        | ~ r2_hidden(sK5(sK2,k2_tarski(X2,sK1),k1_funct_1(sK2,sK1)),X3)
        | ~ r2_hidden(sK3(sK2,X3,X4),X4) )
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f296,f76])).

fof(f296,plain,
    ( ! [X4,X2,X3] :
        ( k1_funct_1(sK2,sK1) != sK3(sK2,X3,X4)
        | k9_relat_1(sK2,X3) = X4
        | ~ r2_hidden(sK5(sK2,k2_tarski(X2,sK1),k1_funct_1(sK2,sK1)),X3)
        | ~ r2_hidden(sK3(sK2,X3,X4),X4)
        | ~ v1_relat_1(sK2) )
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f295,f71])).

fof(f295,plain,
    ( ! [X4,X2,X3] :
        ( k1_funct_1(sK2,sK1) != sK3(sK2,X3,X4)
        | k9_relat_1(sK2,X3) = X4
        | ~ r2_hidden(sK5(sK2,k2_tarski(X2,sK1),k1_funct_1(sK2,sK1)),X3)
        | ~ r2_hidden(sK3(sK2,X3,X4),X4)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f291,f154])).

fof(f154,plain,
    ( ! [X0] : r2_hidden(sK5(sK2,k2_tarski(X0,sK1),k1_funct_1(sK2,sK1)),k1_relat_1(sK2))
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(unit_resulting_resolution,[],[f76,f71,f78,f47])).

fof(f78,plain,
    ( ! [X0] : r2_hidden(k1_funct_1(sK2,sK1),k9_relat_1(sK2,k2_tarski(X0,sK1)))
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(unit_resulting_resolution,[],[f76,f71,f49,f61,f44])).

fof(f61,plain,
    ( r2_hidden(sK1,k1_relat_1(sK2))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f291,plain,
    ( ! [X4,X2,X3] :
        ( k1_funct_1(sK2,sK1) != sK3(sK2,X3,X4)
        | k9_relat_1(sK2,X3) = X4
        | ~ r2_hidden(sK5(sK2,k2_tarski(X2,sK1),k1_funct_1(sK2,sK1)),X3)
        | ~ r2_hidden(sK5(sK2,k2_tarski(X2,sK1),k1_funct_1(sK2,sK1)),k1_relat_1(sK2))
        | ~ r2_hidden(sK3(sK2,X3,X4),X4)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(superposition,[],[f35,f156])).

fof(f156,plain,
    ( ! [X0] : k1_funct_1(sK2,sK1) = k1_funct_1(sK2,sK5(sK2,k2_tarski(X0,sK1),k1_funct_1(sK2,sK1)))
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(unit_resulting_resolution,[],[f76,f71,f78,f45])).

fof(f155,plain,
    ( ! [X0] : r2_hidden(sK5(sK2,k2_tarski(X0,sK1),k1_funct_1(sK2,sK1)),k2_tarski(X0,sK1))
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(unit_resulting_resolution,[],[f76,f71,f78,f46])).

fof(f49,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f77,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f23,f74])).

fof(f23,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( k9_relat_1(sK2,k2_tarski(sK0,sK1)) != k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1))
    & r2_hidden(sK1,k1_relat_1(sK2))
    & r2_hidden(sK0,k1_relat_1(sK2))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2] :
        ( k9_relat_1(X2,k2_tarski(X0,X1)) != k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))
        & r2_hidden(X1,k1_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k9_relat_1(sK2,k2_tarski(sK0,sK1)) != k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1))
      & r2_hidden(sK1,k1_relat_1(sK2))
      & r2_hidden(sK0,k1_relat_1(sK2))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( k9_relat_1(X2,k2_tarski(X0,X1)) != k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))
      & r2_hidden(X1,k1_relat_1(X2))
      & r2_hidden(X0,k1_relat_1(X2))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f6])).

% (7806)Refutation not found, incomplete strategy% (7806)------------------------------
% (7806)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f6,plain,(
    ? [X0,X1,X2] :
      ( k9_relat_1(X2,k2_tarski(X0,X1)) != k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))
      & r2_hidden(X1,k1_relat_1(X2))
      & r2_hidden(X0,k1_relat_1(X2))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r2_hidden(X1,k1_relat_1(X2))
            & r2_hidden(X0,k1_relat_1(X2)) )
         => k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r2_hidden(X1,k1_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) )
       => k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_funct_1)).

fof(f72,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f24,f69])).

fof(f24,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f67,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f25,f64])).

fof(f25,plain,(
    r2_hidden(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f62,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f26,f59])).

fof(f26,plain,(
    r2_hidden(sK1,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f57,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f27,f54])).

fof(f27,plain,(
    k9_relat_1(sK2,k2_tarski(sK0,sK1)) != k2_tarski(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f11])).

%------------------------------------------------------------------------------
