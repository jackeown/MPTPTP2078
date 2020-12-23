%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t144_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:15 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  114 (1109 expanded)
%              Number of leaves         :   17 ( 342 expanded)
%              Depth                    :   19
%              Number of atoms          :  589 (7234 expanded)
%              Number of equality atoms :  156 (2093 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f302,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f107,f226,f301])).

fof(f301,plain,
    ( ~ spl10_0
    | ~ spl10_2 ),
    inference(avatar_contradiction_clause,[],[f300])).

fof(f300,plain,
    ( $false
    | ~ spl10_0
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f297,f278])).

fof(f278,plain,
    ( r2_hidden(k1_funct_1(sK0,sK6(sK9(sK0,sK1),k10_relat_1(sK0,k1_tarski(sK1)))),k1_tarski(sK1))
    | ~ spl10_0
    | ~ spl10_2 ),
    inference(unit_resulting_resolution,[],[f57,f58,f275,f85])).

fof(f85,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k10_relat_1(X0,X1))
      | r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ~ r2_hidden(k1_funct_1(X0,sK5(X0,X1,X2)),X1)
                | ~ r2_hidden(sK5(X0,X1,X2),k1_relat_1(X0))
                | ~ r2_hidden(sK5(X0,X1,X2),X2) )
              & ( ( r2_hidden(k1_funct_1(X0,sK5(X0,X1,X2)),X1)
                  & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X4),X1)
                  | ~ r2_hidden(X4,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X4),X1)
                    & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X4,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f44,f45])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
            | ~ r2_hidden(X3,k1_relat_1(X0))
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
              & r2_hidden(X3,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k1_funct_1(X0,sK5(X0,X1,X2)),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),k1_relat_1(X0))
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( r2_hidden(k1_funct_1(X0,sK5(X0,X1,X2)),X1)
            & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X0)) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0))
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X4),X1)
                  | ~ r2_hidden(X4,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X4),X1)
                    & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X4,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0))
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0))
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t144_funct_1.p',d13_funct_1)).

fof(f275,plain,
    ( r2_hidden(sK6(sK9(sK0,sK1),k10_relat_1(sK0,k1_tarski(sK1))),k10_relat_1(sK0,k1_tarski(sK1)))
    | ~ spl10_0
    | ~ spl10_2 ),
    inference(unit_resulting_resolution,[],[f231,f264,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X1)
      | sK6(X0,X1) = X0
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK6(X0,X1) != X0
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( sK6(X0,X1) = X0
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f48,f49])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK6(X0,X1) != X0
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( sK6(X0,X1) = X0
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t144_funct_1.p',d1_tarski)).

fof(f264,plain,
    ( sK6(sK9(sK0,sK1),k10_relat_1(sK0,k1_tarski(sK1))) != sK9(sK0,sK1)
    | ~ spl10_0
    | ~ spl10_2 ),
    inference(unit_resulting_resolution,[],[f231,f261,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( sK6(X0,X1) != X0
      | k1_tarski(X0) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(inner_rewriting,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK6(X0,X1) != X0
      | ~ r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f261,plain,
    ( r2_hidden(sK9(sK0,sK1),k10_relat_1(sK0,k1_tarski(sK1)))
    | ~ spl10_0 ),
    inference(forward_demodulation,[],[f234,f227])).

fof(f227,plain,
    ( k1_funct_1(sK0,sK9(sK0,sK1)) = sK1
    | ~ spl10_0 ),
    inference(unit_resulting_resolution,[],[f57,f58,f100,f92])).

fof(f92,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,k2_relat_1(X0))
      | k1_funct_1(X0,sK9(X0,X5)) = X5
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK9(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK7(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK7(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK8(X0,X1)) = sK7(X0,X1)
                  & r2_hidden(sK8(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK7(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK9(X0,X5)) = X5
                    & r2_hidden(sK9(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f52,f55,f54,f53])).

fof(f53,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK7(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK7(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK7(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK7(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK8(X0,X1)) = X2
        & r2_hidden(sK8(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK9(X0,X5)) = X5
        & r2_hidden(sK9(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t144_funct_1.p',d5_funct_1)).

fof(f100,plain,
    ( r2_hidden(sK1,k2_relat_1(sK0))
    | ~ spl10_0 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl10_0
  <=> r2_hidden(sK1,k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_0])])).

fof(f234,plain,
    ( r2_hidden(sK9(sK0,sK1),k10_relat_1(sK0,k1_tarski(k1_funct_1(sK0,sK9(sK0,sK1)))))
    | ~ spl10_0 ),
    inference(unit_resulting_resolution,[],[f57,f58,f88,f228,f84])).

fof(f84,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(k1_funct_1(X0,X4),X1)
      | r2_hidden(X4,k10_relat_1(X0,X1))
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | k10_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f228,plain,
    ( r2_hidden(sK9(sK0,sK1),k1_relat_1(sK0))
    | ~ spl10_0 ),
    inference(unit_resulting_resolution,[],[f57,f58,f100,f93])).

fof(f93,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK9(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK9(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f88,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f231,plain,
    ( ! [X2] : k1_tarski(X2) != k10_relat_1(sK0,k1_tarski(sK1))
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f61,f103])).

fof(f103,plain,
    ( v2_funct_1(sK0)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl10_2
  <=> v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f61,plain,(
    ! [X2] :
      ( ~ v2_funct_1(sK0)
      | k1_tarski(X2) != k10_relat_1(sK0,k1_tarski(sK1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ( ~ v2_funct_1(sK0)
      | ( ! [X2] : k1_tarski(X2) != k10_relat_1(sK0,k1_tarski(sK1))
        & r2_hidden(sK1,k2_relat_1(sK0)) ) )
    & ( v2_funct_1(sK0)
      | ! [X3] :
          ( k1_tarski(sK2(X3)) = k10_relat_1(sK0,k1_tarski(X3))
          | ~ r2_hidden(X3,k2_relat_1(sK0)) ) )
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f36,f35,f34])).

fof(f34,plain,
    ( ? [X0] :
        ( ( ~ v2_funct_1(X0)
          | ? [X1] :
              ( ! [X2] : k1_tarski(X2) != k10_relat_1(X0,k1_tarski(X1))
              & r2_hidden(X1,k2_relat_1(X0)) ) )
        & ( v2_funct_1(X0)
          | ! [X3] :
              ( ? [X4] : k1_tarski(X4) = k10_relat_1(X0,k1_tarski(X3))
              | ~ r2_hidden(X3,k2_relat_1(X0)) ) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( ~ v2_funct_1(sK0)
        | ? [X1] :
            ( ! [X2] : k1_tarski(X2) != k10_relat_1(sK0,k1_tarski(X1))
            & r2_hidden(X1,k2_relat_1(sK0)) ) )
      & ( v2_funct_1(sK0)
        | ! [X3] :
            ( ? [X4] : k1_tarski(X4) = k10_relat_1(sK0,k1_tarski(X3))
            | ~ r2_hidden(X3,k2_relat_1(sK0)) ) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] : k1_tarski(X2) != k10_relat_1(X0,k1_tarski(X1))
          & r2_hidden(X1,k2_relat_1(X0)) )
     => ( ! [X2] : k1_tarski(X2) != k10_relat_1(X0,k1_tarski(sK1))
        & r2_hidden(sK1,k2_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X3] :
      ( ? [X4] : k1_tarski(X4) = k10_relat_1(X0,k1_tarski(X3))
     => k1_tarski(sK2(X3)) = k10_relat_1(X0,k1_tarski(X3)) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ? [X0] :
      ( ( ~ v2_funct_1(X0)
        | ? [X1] :
            ( ! [X2] : k1_tarski(X2) != k10_relat_1(X0,k1_tarski(X1))
            & r2_hidden(X1,k2_relat_1(X0)) ) )
      & ( v2_funct_1(X0)
        | ! [X3] :
            ( ? [X4] : k1_tarski(X4) = k10_relat_1(X0,k1_tarski(X3))
            | ~ r2_hidden(X3,k2_relat_1(X0)) ) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ( ~ v2_funct_1(X0)
        | ? [X1] :
            ( ! [X2] : k1_tarski(X2) != k10_relat_1(X0,k1_tarski(X1))
            & r2_hidden(X1,k2_relat_1(X0)) ) )
      & ( v2_funct_1(X0)
        | ! [X1] :
            ( ? [X2] : k1_tarski(X2) = k10_relat_1(X0,k1_tarski(X1))
            | ~ r2_hidden(X1,k2_relat_1(X0)) ) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ( ~ v2_funct_1(X0)
        | ? [X1] :
            ( ! [X2] : k1_tarski(X2) != k10_relat_1(X0,k1_tarski(X1))
            & r2_hidden(X1,k2_relat_1(X0)) ) )
      & ( v2_funct_1(X0)
        | ! [X1] :
            ( ? [X2] : k1_tarski(X2) = k10_relat_1(X0,k1_tarski(X1))
            | ~ r2_hidden(X1,k2_relat_1(X0)) ) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ( ! [X1] :
            ( ? [X2] : k1_tarski(X2) = k10_relat_1(X0,k1_tarski(X1))
            | ~ r2_hidden(X1,k2_relat_1(X0)) )
      <~> v2_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ( ! [X1] :
            ( ? [X2] : k1_tarski(X2) = k10_relat_1(X0,k1_tarski(X1))
            | ~ r2_hidden(X1,k2_relat_1(X0)) )
      <~> v2_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( ! [X1] :
              ~ ( ! [X2] : k1_tarski(X2) != k10_relat_1(X0,k1_tarski(X1))
                & r2_hidden(X1,k2_relat_1(X0)) )
        <=> v2_funct_1(X0) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ! [X1] :
            ~ ( ! [X2] : k1_tarski(X2) != k10_relat_1(X0,k1_tarski(X1))
              & r2_hidden(X1,k2_relat_1(X0)) )
      <=> v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t144_funct_1.p',t144_funct_1)).

fof(f58,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f57,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f297,plain,
    ( ~ r2_hidden(k1_funct_1(sK0,sK6(sK9(sK0,sK1),k10_relat_1(sK0,k1_tarski(sK1)))),k1_tarski(sK1))
    | ~ spl10_0
    | ~ spl10_2 ),
    inference(unit_resulting_resolution,[],[f283,f89])).

fof(f89,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f283,plain,
    ( k1_funct_1(sK0,sK6(sK9(sK0,sK1),k10_relat_1(sK0,k1_tarski(sK1)))) != sK1
    | ~ spl10_0
    | ~ spl10_2 ),
    inference(unit_resulting_resolution,[],[f264,f279,f250])).

fof(f250,plain,
    ( ! [X1] :
        ( k1_funct_1(sK0,X1) != sK1
        | sK9(sK0,sK1) = X1
        | ~ r2_hidden(X1,k1_relat_1(sK0)) )
    | ~ spl10_0
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f249,f57])).

fof(f249,plain,
    ( ! [X1] :
        ( k1_funct_1(sK0,X1) != sK1
        | sK9(sK0,sK1) = X1
        | ~ r2_hidden(X1,k1_relat_1(sK0))
        | ~ v1_relat_1(sK0) )
    | ~ spl10_0
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f248,f58])).

fof(f248,plain,
    ( ! [X1] :
        ( k1_funct_1(sK0,X1) != sK1
        | sK9(sK0,sK1) = X1
        | ~ r2_hidden(X1,k1_relat_1(sK0))
        | ~ v1_funct_1(sK0)
        | ~ v1_relat_1(sK0) )
    | ~ spl10_0
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f247,f103])).

fof(f247,plain,
    ( ! [X1] :
        ( k1_funct_1(sK0,X1) != sK1
        | sK9(sK0,sK1) = X1
        | ~ r2_hidden(X1,k1_relat_1(sK0))
        | ~ v2_funct_1(sK0)
        | ~ v1_funct_1(sK0)
        | ~ v1_relat_1(sK0) )
    | ~ spl10_0 ),
    inference(subsumption_resolution,[],[f239,f228])).

fof(f239,plain,
    ( ! [X1] :
        ( k1_funct_1(sK0,X1) != sK1
        | sK9(sK0,sK1) = X1
        | ~ r2_hidden(sK9(sK0,sK1),k1_relat_1(sK0))
        | ~ r2_hidden(X1,k1_relat_1(sK0))
        | ~ v2_funct_1(sK0)
        | ~ v1_funct_1(sK0)
        | ~ v1_relat_1(sK0) )
    | ~ spl10_0 ),
    inference(superposition,[],[f62,f227])).

fof(f62,plain,(
    ! [X4,X0,X3] :
      ( k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | X3 = X4
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ( sK3(X0) != sK4(X0)
            & k1_funct_1(X0,sK3(X0)) = k1_funct_1(X0,sK4(X0))
            & r2_hidden(sK4(X0),k1_relat_1(X0))
            & r2_hidden(sK3(X0),k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f39,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK3(X0) != sK4(X0)
        & k1_funct_1(X0,sK3(X0)) = k1_funct_1(X0,sK4(X0))
        & r2_hidden(sK4(X0),k1_relat_1(X0))
        & r2_hidden(sK3(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t144_funct_1.p',d8_funct_1)).

fof(f279,plain,
    ( r2_hidden(sK6(sK9(sK0,sK1),k10_relat_1(sK0,k1_tarski(sK1))),k1_relat_1(sK0))
    | ~ spl10_0
    | ~ spl10_2 ),
    inference(unit_resulting_resolution,[],[f57,f58,f275,f86])).

fof(f86,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k10_relat_1(X0,X1))
      | r2_hidden(X4,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f226,plain,(
    spl10_3 ),
    inference(avatar_contradiction_clause,[],[f225])).

fof(f225,plain,
    ( $false
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f222,f120])).

fof(f120,plain,
    ( ~ r2_hidden(sK3(sK0),k1_tarski(sK4(sK0)))
    | ~ spl10_3 ),
    inference(unit_resulting_resolution,[],[f118,f89])).

fof(f118,plain,
    ( sK3(sK0) != sK4(sK0)
    | ~ spl10_3 ),
    inference(unit_resulting_resolution,[],[f57,f58,f106,f66])).

fof(f66,plain,(
    ! [X0] :
      ( sK3(X0) != sK4(X0)
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f106,plain,
    ( ~ v2_funct_1(sK0)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl10_3
  <=> ~ v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f222,plain,
    ( r2_hidden(sK3(sK0),k1_tarski(sK4(sK0)))
    | ~ spl10_3 ),
    inference(backward_demodulation,[],[f216,f208])).

fof(f208,plain,
    ( r2_hidden(sK3(sK0),k1_tarski(sK2(k1_funct_1(sK0,sK3(sK0)))))
    | ~ spl10_3 ),
    inference(backward_demodulation,[],[f125,f131])).

fof(f131,plain,
    ( r2_hidden(sK3(sK0),k10_relat_1(sK0,k1_tarski(k1_funct_1(sK0,sK3(sK0)))))
    | ~ spl10_3 ),
    inference(unit_resulting_resolution,[],[f57,f58,f112,f88,f84])).

fof(f112,plain,
    ( r2_hidden(sK3(sK0),k1_relat_1(sK0))
    | ~ spl10_3 ),
    inference(unit_resulting_resolution,[],[f57,f106,f58,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | r2_hidden(sK3(X0),k1_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f125,plain,
    ( k1_tarski(sK2(k1_funct_1(sK0,sK3(sK0)))) = k10_relat_1(sK0,k1_tarski(k1_funct_1(sK0,sK3(sK0))))
    | ~ spl10_3 ),
    inference(unit_resulting_resolution,[],[f122,f108])).

fof(f108,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k2_relat_1(sK0))
        | k1_tarski(sK2(X3)) = k10_relat_1(sK0,k1_tarski(X3)) )
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f59,f106])).

fof(f59,plain,(
    ! [X3] :
      ( v2_funct_1(sK0)
      | k1_tarski(sK2(X3)) = k10_relat_1(sK0,k1_tarski(X3))
      | ~ r2_hidden(X3,k2_relat_1(sK0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f122,plain,
    ( r2_hidden(k1_funct_1(sK0,sK3(sK0)),k2_relat_1(sK0))
    | ~ spl10_3 ),
    inference(unit_resulting_resolution,[],[f57,f58,f112,f91])).

fof(f91,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f216,plain,
    ( sK2(k1_funct_1(sK0,sK3(sK0))) = sK4(sK0)
    | ~ spl10_3 ),
    inference(unit_resulting_resolution,[],[f207,f89])).

fof(f207,plain,
    ( r2_hidden(sK4(sK0),k1_tarski(sK2(k1_funct_1(sK0,sK3(sK0)))))
    | ~ spl10_3 ),
    inference(backward_demodulation,[],[f125,f174])).

fof(f174,plain,
    ( r2_hidden(sK4(sK0),k10_relat_1(sK0,k1_tarski(k1_funct_1(sK0,sK3(sK0)))))
    | ~ spl10_3 ),
    inference(forward_demodulation,[],[f132,f124])).

fof(f124,plain,
    ( k1_funct_1(sK0,sK3(sK0)) = k1_funct_1(sK0,sK4(sK0))
    | ~ spl10_3 ),
    inference(unit_resulting_resolution,[],[f57,f106,f58,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK3(X0)) = k1_funct_1(X0,sK4(X0))
      | v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f132,plain,
    ( r2_hidden(sK4(sK0),k10_relat_1(sK0,k1_tarski(k1_funct_1(sK0,sK4(sK0)))))
    | ~ spl10_3 ),
    inference(unit_resulting_resolution,[],[f57,f58,f115,f88,f84])).

fof(f115,plain,
    ( r2_hidden(sK4(sK0),k1_relat_1(sK0))
    | ~ spl10_3 ),
    inference(unit_resulting_resolution,[],[f57,f106,f58,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | r2_hidden(sK4(X0),k1_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f107,plain,
    ( spl10_0
    | ~ spl10_3 ),
    inference(avatar_split_clause,[],[f60,f105,f99])).

fof(f60,plain,
    ( ~ v2_funct_1(sK0)
    | r2_hidden(sK1,k2_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
