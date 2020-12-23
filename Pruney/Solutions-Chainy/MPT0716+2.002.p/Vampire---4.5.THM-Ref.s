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
% DateTime   : Thu Dec  3 12:54:48 EST 2020

% Result     : Theorem 1.60s
% Output     : Refutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 302 expanded)
%              Number of leaves         :   20 ( 104 expanded)
%              Depth                    :   19
%              Number of atoms          :  457 (2179 expanded)
%              Number of equality atoms :   23 (  33 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f905,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f80,f83,f85,f148,f457,f480,f515,f648,f903])).

fof(f903,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_contradiction_clause,[],[f898])).

fof(f898,plain,
    ( $false
    | ~ spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f76,f893])).

fof(f893,plain,
    ( r1_tarski(sK2,k1_relat_1(sK0))
    | ~ spl5_1 ),
    inference(duplicate_literal_removal,[],[f891])).

fof(f891,plain,
    ( r1_tarski(sK2,k1_relat_1(sK0))
    | r1_tarski(sK2,k1_relat_1(sK0))
    | ~ spl5_1 ),
    inference(resolution,[],[f872,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f39,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
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

fof(f872,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK4(X2,k1_relat_1(sK0)),sK2)
        | r1_tarski(X2,k1_relat_1(sK0)) )
    | ~ spl5_1 ),
    inference(resolution,[],[f865,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f865,plain,
    ( ! [X9] :
        ( r2_hidden(X9,k1_relat_1(sK0))
        | ~ r2_hidden(X9,sK2) )
    | ~ spl5_1 ),
    inference(resolution,[],[f264,f81])).

fof(f81,plain,
    ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl5_1
  <=> r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f264,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k1_relat_1(k5_relat_1(sK0,sK1)))
      | ~ r2_hidden(X0,X1)
      | r2_hidden(X0,k1_relat_1(sK0)) ) ),
    inference(resolution,[],[f172,f60])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f172,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_relat_1(k5_relat_1(sK0,sK1)))
      | r2_hidden(X1,k1_relat_1(sK0)) ) ),
    inference(global_subsumption,[],[f43,f42,f168])).

fof(f168,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_relat_1(k5_relat_1(sK0,sK1)))
      | r2_hidden(X1,k1_relat_1(sK0))
      | ~ v1_funct_1(sK0)
      | ~ v1_relat_1(sK0) ) ),
    inference(superposition,[],[f68,f117])).

fof(f117,plain,(
    k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k1_relat_1(sK1)) ),
    inference(resolution,[],[f87,f42])).

fof(f87,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(X0,sK1)) = k10_relat_1(X0,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f44,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f44,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
      | ~ r1_tarski(sK2,k1_relat_1(sK0))
      | ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) )
    & ( ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
        & r1_tarski(sK2,k1_relat_1(sK0)) )
      | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) )
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f29,f28,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                  | ~ r1_tarski(X2,k1_relat_1(X0))
                  | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) )
                & ( ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                    & r1_tarski(X2,k1_relat_1(X0)) )
                  | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) ) )
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1))
                | ~ r1_tarski(X2,k1_relat_1(sK0))
                | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1))) )
              & ( ( r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(sK0)) )
                | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1))) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1))
              | ~ r1_tarski(X2,k1_relat_1(sK0))
              | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1))) )
            & ( ( r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(sK0)) )
              | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1))) ) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(sK1))
            | ~ r1_tarski(X2,k1_relat_1(sK0))
            | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,sK1))) )
          & ( ( r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(sK1))
              & r1_tarski(X2,k1_relat_1(sK0)) )
            | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,sK1))) ) )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X2] :
        ( ( ~ r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(sK1))
          | ~ r1_tarski(X2,k1_relat_1(sK0))
          | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,sK1))) )
        & ( ( r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(sK1))
            & r1_tarski(X2,k1_relat_1(sK0)) )
          | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,sK1))) ) )
   => ( ( ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
        | ~ r1_tarski(sK2,k1_relat_1(sK0))
        | ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) )
      & ( ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
          & r1_tarski(sK2,k1_relat_1(sK0)) )
        | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                | ~ r1_tarski(X2,k1_relat_1(X0))
                | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) )
              & ( ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(X0)) )
                | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                | ~ r1_tarski(X2,k1_relat_1(X0))
                | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) )
              & ( ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(X0)) )
                | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
            <~> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
            <~> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
              <=> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(X0)) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
            <=> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_1)).

fof(f68,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k10_relat_1(X0,X1))
      | r2_hidden(X4,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ~ r2_hidden(k1_funct_1(X0,sK3(X0,X1,X2)),X1)
                | ~ r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0))
                | ~ r2_hidden(sK3(X0,X1,X2),X2) )
              & ( ( r2_hidden(k1_funct_1(X0,sK3(X0,X1,X2)),X1)
                  & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f34])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
            | ~ r2_hidden(X3,k1_relat_1(X0))
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
              & r2_hidden(X3,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k1_funct_1(X0,sK3(X0,X1,X2)),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0))
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( r2_hidden(k1_funct_1(X0,sK3(X0,X1,X2)),X1)
            & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0)) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_funct_1)).

fof(f42,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f43,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f76,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK0))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl5_2
  <=> r1_tarski(sK2,k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f648,plain,
    ( ~ spl5_2
    | ~ spl5_3
    | spl5_1 ),
    inference(avatar_split_clause,[],[f647,f72,f78,f75])).

fof(f78,plain,
    ( spl5_3
  <=> r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f647,plain,
    ( ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ r1_tarski(sK2,k1_relat_1(sK0))
    | spl5_1 ),
    inference(resolution,[],[f170,f73])).

fof(f73,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f170,plain,(
    ! [X0] :
      ( r1_tarski(X0,k1_relat_1(k5_relat_1(sK0,sK1)))
      | ~ r1_tarski(k9_relat_1(sK0,X0),k1_relat_1(sK1))
      | ~ r1_tarski(X0,k1_relat_1(sK0)) ) ),
    inference(global_subsumption,[],[f43,f42,f166])).

fof(f166,plain,(
    ! [X0] :
      ( r1_tarski(X0,k1_relat_1(k5_relat_1(sK0,sK1)))
      | ~ r1_tarski(k9_relat_1(sK0,X0),k1_relat_1(sK1))
      | ~ r1_tarski(X0,k1_relat_1(sK0))
      | ~ v1_funct_1(sK0)
      | ~ v1_relat_1(sK0) ) ),
    inference(superposition,[],[f64,f117])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

fof(f515,plain,
    ( ~ spl5_1
    | ~ spl5_42
    | ~ spl5_8
    | ~ spl5_35 ),
    inference(avatar_split_clause,[],[f508,f323,f125,f402,f72])).

fof(f402,plain,
    ( spl5_42
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f125,plain,
    ( spl5_8
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f323,plain,
    ( spl5_35
  <=> ! [X1,X0] :
        ( ~ r1_tarski(k9_relat_1(X0,X1),k1_relat_1(sK1))
        | ~ v1_relat_1(X0)
        | ~ r1_tarski(sK0,X0)
        | ~ r1_tarski(sK2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f508,plain,
    ( ~ v1_relat_1(sK0)
    | ~ r1_tarski(sK0,sK0)
    | ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl5_35 ),
    inference(resolution,[],[f324,f171])).

fof(f171,plain,(
    r1_tarski(k9_relat_1(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),k1_relat_1(sK1)) ),
    inference(global_subsumption,[],[f43,f42,f167])).

fof(f167,plain,
    ( r1_tarski(k9_relat_1(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),k1_relat_1(sK1))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(superposition,[],[f56,f117])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(f324,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k9_relat_1(X0,X1),k1_relat_1(sK1))
        | ~ v1_relat_1(X0)
        | ~ r1_tarski(sK0,X0)
        | ~ r1_tarski(sK2,X1) )
    | ~ spl5_35 ),
    inference(avatar_component_clause,[],[f323])).

fof(f480,plain,(
    spl5_42 ),
    inference(avatar_contradiction_clause,[],[f476])).

fof(f476,plain,
    ( $false
    | spl5_42 ),
    inference(resolution,[],[f403,f70])).

fof(f70,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
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

fof(f403,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl5_42 ),
    inference(avatar_component_clause,[],[f402])).

fof(f457,plain,
    ( ~ spl5_8
    | spl5_35
    | spl5_3 ),
    inference(avatar_split_clause,[],[f451,f78,f323,f125])).

fof(f451,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k9_relat_1(X0,X1),k1_relat_1(sK1))
        | ~ r1_tarski(sK2,X1)
        | ~ r1_tarski(sK0,X0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(sK0) )
    | spl5_3 ),
    inference(resolution,[],[f444,f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
      | ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X3)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
          | ~ r1_tarski(X0,X1)
          | ~ r1_tarski(X2,X3)
          | ~ v1_relat_1(X3) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
          | ~ r1_tarski(X0,X1)
          | ~ r1_tarski(X2,X3)
          | ~ v1_relat_1(X3) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_relat_1)).

fof(f444,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k9_relat_1(sK0,sK2),X0)
        | ~ r1_tarski(X0,k1_relat_1(sK1)) )
    | spl5_3 ),
    inference(resolution,[],[f79,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f79,plain,
    ( ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f78])).

fof(f148,plain,(
    spl5_8 ),
    inference(avatar_contradiction_clause,[],[f147])).

fof(f147,plain,
    ( $false
    | spl5_8 ),
    inference(subsumption_resolution,[],[f42,f126])).

fof(f126,plain,
    ( ~ v1_relat_1(sK0)
    | spl5_8 ),
    inference(avatar_component_clause,[],[f125])).

fof(f85,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f46,f75,f72])).

fof(f46,plain,
    ( r1_tarski(sK2,k1_relat_1(sK0))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f30])).

fof(f83,plain,
    ( spl5_1
    | spl5_3 ),
    inference(avatar_split_clause,[],[f47,f78,f72])).

fof(f47,plain,
    ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f30])).

fof(f80,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f48,f78,f75,f72])).

fof(f48,plain,
    ( ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ r1_tarski(sK2,k1_relat_1(sK0))
    | ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:46:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (3615)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.50  % (3624)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.50  % (3629)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.50  % (3616)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.51  % (3608)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (3621)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.52  % (3613)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (3603)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (3604)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (3627)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.53  % (3606)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (3602)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (3607)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (3609)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.53  % (3605)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (3619)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.54  % (3611)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.54  % (3618)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.54  % (3620)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.54  % (3610)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.54  % (3612)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.47/0.55  % (3614)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.47/0.55  % (3630)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.47/0.55  % (3617)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.47/0.55  % (3628)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.47/0.55  % (3623)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.47/0.55  % (3625)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.47/0.55  % (3622)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.47/0.56  % (3626)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.47/0.56  % (3631)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.60/0.57  % (3604)Refutation found. Thanks to Tanya!
% 1.60/0.57  % SZS status Theorem for theBenchmark
% 1.60/0.57  % SZS output start Proof for theBenchmark
% 1.60/0.57  fof(f905,plain,(
% 1.60/0.57    $false),
% 1.60/0.57    inference(avatar_sat_refutation,[],[f80,f83,f85,f148,f457,f480,f515,f648,f903])).
% 1.60/0.57  fof(f903,plain,(
% 1.60/0.57    ~spl5_1 | spl5_2),
% 1.60/0.57    inference(avatar_contradiction_clause,[],[f898])).
% 1.60/0.57  fof(f898,plain,(
% 1.60/0.57    $false | (~spl5_1 | spl5_2)),
% 1.60/0.57    inference(subsumption_resolution,[],[f76,f893])).
% 1.60/0.57  fof(f893,plain,(
% 1.60/0.57    r1_tarski(sK2,k1_relat_1(sK0)) | ~spl5_1),
% 1.60/0.57    inference(duplicate_literal_removal,[],[f891])).
% 1.60/0.57  fof(f891,plain,(
% 1.60/0.57    r1_tarski(sK2,k1_relat_1(sK0)) | r1_tarski(sK2,k1_relat_1(sK0)) | ~spl5_1),
% 1.60/0.57    inference(resolution,[],[f872,f61])).
% 1.60/0.57  fof(f61,plain,(
% 1.60/0.57    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.60/0.57    inference(cnf_transformation,[],[f41])).
% 1.60/0.57  fof(f41,plain,(
% 1.60/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.60/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f39,f40])).
% 1.60/0.57  fof(f40,plain,(
% 1.60/0.57    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.60/0.57    introduced(choice_axiom,[])).
% 1.60/0.57  fof(f39,plain,(
% 1.60/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.60/0.57    inference(rectify,[],[f38])).
% 1.60/0.57  fof(f38,plain,(
% 1.60/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.60/0.57    inference(nnf_transformation,[],[f18])).
% 1.60/0.57  fof(f18,plain,(
% 1.60/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.60/0.57    inference(ennf_transformation,[],[f1])).
% 1.60/0.57  fof(f1,axiom,(
% 1.60/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.60/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.60/0.57  fof(f872,plain,(
% 1.60/0.57    ( ! [X2] : (~r2_hidden(sK4(X2,k1_relat_1(sK0)),sK2) | r1_tarski(X2,k1_relat_1(sK0))) ) | ~spl5_1),
% 1.60/0.57    inference(resolution,[],[f865,f62])).
% 1.60/0.57  fof(f62,plain,(
% 1.60/0.57    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.60/0.57    inference(cnf_transformation,[],[f41])).
% 1.60/0.57  fof(f865,plain,(
% 1.60/0.57    ( ! [X9] : (r2_hidden(X9,k1_relat_1(sK0)) | ~r2_hidden(X9,sK2)) ) | ~spl5_1),
% 1.60/0.57    inference(resolution,[],[f264,f81])).
% 1.60/0.57  fof(f81,plain,(
% 1.60/0.57    r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) | ~spl5_1),
% 1.60/0.57    inference(avatar_component_clause,[],[f72])).
% 1.60/0.57  fof(f72,plain,(
% 1.60/0.57    spl5_1 <=> r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.60/0.57  fof(f264,plain,(
% 1.60/0.57    ( ! [X0,X1] : (~r1_tarski(X1,k1_relat_1(k5_relat_1(sK0,sK1))) | ~r2_hidden(X0,X1) | r2_hidden(X0,k1_relat_1(sK0))) )),
% 1.60/0.57    inference(resolution,[],[f172,f60])).
% 1.60/0.57  fof(f60,plain,(
% 1.60/0.57    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.60/0.57    inference(cnf_transformation,[],[f41])).
% 1.60/0.57  fof(f172,plain,(
% 1.60/0.57    ( ! [X1] : (~r2_hidden(X1,k1_relat_1(k5_relat_1(sK0,sK1))) | r2_hidden(X1,k1_relat_1(sK0))) )),
% 1.60/0.57    inference(global_subsumption,[],[f43,f42,f168])).
% 1.60/0.57  fof(f168,plain,(
% 1.60/0.57    ( ! [X1] : (~r2_hidden(X1,k1_relat_1(k5_relat_1(sK0,sK1))) | r2_hidden(X1,k1_relat_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)) )),
% 1.60/0.57    inference(superposition,[],[f68,f117])).
% 1.60/0.57  fof(f117,plain,(
% 1.60/0.57    k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k1_relat_1(sK1))),
% 1.60/0.57    inference(resolution,[],[f87,f42])).
% 1.60/0.57  fof(f87,plain,(
% 1.60/0.57    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(k5_relat_1(X0,sK1)) = k10_relat_1(X0,k1_relat_1(sK1))) )),
% 1.60/0.57    inference(resolution,[],[f44,f49])).
% 1.60/0.57  fof(f49,plain,(
% 1.60/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 1.60/0.57    inference(cnf_transformation,[],[f13])).
% 1.60/0.57  fof(f13,plain,(
% 1.60/0.57    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.60/0.57    inference(ennf_transformation,[],[f5])).
% 1.60/0.57  fof(f5,axiom,(
% 1.60/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 1.60/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 1.60/0.57  fof(f44,plain,(
% 1.60/0.57    v1_relat_1(sK1)),
% 1.60/0.57    inference(cnf_transformation,[],[f30])).
% 1.60/0.57  fof(f30,plain,(
% 1.60/0.57    (((~r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~r1_tarski(sK2,k1_relat_1(sK0)) | ~r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))) & ((r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) & r1_tarski(sK2,k1_relat_1(sK0))) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))))) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 1.60/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f29,f28,f27])).
% 1.60/0.57  fof(f27,plain,(
% 1.60/0.57    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(sK0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1)))) & ((r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(sK0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 1.60/0.57    introduced(choice_axiom,[])).
% 1.60/0.57  fof(f28,plain,(
% 1.60/0.57    ? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(sK0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1)))) & ((r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(sK0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : ((~r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(sK1)) | ~r1_tarski(X2,k1_relat_1(sK0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,sK1)))) & ((r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(sK1)) & r1_tarski(X2,k1_relat_1(sK0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,sK1))))) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 1.60/0.57    introduced(choice_axiom,[])).
% 1.60/0.57  fof(f29,plain,(
% 1.60/0.57    ? [X2] : ((~r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(sK1)) | ~r1_tarski(X2,k1_relat_1(sK0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,sK1)))) & ((r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(sK1)) & r1_tarski(X2,k1_relat_1(sK0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,sK1))))) => ((~r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~r1_tarski(sK2,k1_relat_1(sK0)) | ~r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))) & ((r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) & r1_tarski(sK2,k1_relat_1(sK0))) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))))),
% 1.60/0.57    introduced(choice_axiom,[])).
% 1.60/0.57  fof(f26,plain,(
% 1.60/0.57    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.60/0.57    inference(flattening,[],[f25])).
% 1.60/0.57  fof(f25,plain,(
% 1.60/0.57    ? [X0] : (? [X1] : (? [X2] : (((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.60/0.57    inference(nnf_transformation,[],[f12])).
% 1.60/0.57  fof(f12,plain,(
% 1.60/0.57    ? [X0] : (? [X1] : (? [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <~> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.60/0.57    inference(flattening,[],[f11])).
% 1.60/0.57  fof(f11,plain,(
% 1.60/0.57    ? [X0] : (? [X1] : (? [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <~> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.60/0.57    inference(ennf_transformation,[],[f10])).
% 1.60/0.57  fof(f10,negated_conjecture,(
% 1.60/0.57    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <=> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))))))),
% 1.60/0.57    inference(negated_conjecture,[],[f9])).
% 1.60/0.57  fof(f9,conjecture,(
% 1.60/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <=> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))))))),
% 1.60/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_1)).
% 1.60/0.57  fof(f68,plain,(
% 1.60/0.57    ( ! [X4,X0,X1] : (~r2_hidden(X4,k10_relat_1(X0,X1)) | r2_hidden(X4,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.60/0.57    inference(equality_resolution,[],[f50])).
% 1.60/0.57  fof(f50,plain,(
% 1.60/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X4,X2) | k10_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.60/0.57    inference(cnf_transformation,[],[f35])).
% 1.60/0.57  fof(f35,plain,(
% 1.60/0.57    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ((~r2_hidden(k1_funct_1(X0,sK3(X0,X1,X2)),X1) | ~r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(k1_funct_1(X0,sK3(X0,X1,X2)),X1) & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k1_funct_1(X0,X4),X1) | ~r2_hidden(X4,k1_relat_1(X0))) & ((r2_hidden(k1_funct_1(X0,X4),X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X4,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.60/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f34])).
% 1.60/0.57  fof(f34,plain,(
% 1.60/0.57    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2))) => ((~r2_hidden(k1_funct_1(X0,sK3(X0,X1,X2)),X1) | ~r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(k1_funct_1(X0,sK3(X0,X1,X2)),X1) & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 1.60/0.57    introduced(choice_axiom,[])).
% 1.60/0.57  fof(f33,plain,(
% 1.60/0.57    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k1_funct_1(X0,X4),X1) | ~r2_hidden(X4,k1_relat_1(X0))) & ((r2_hidden(k1_funct_1(X0,X4),X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X4,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.60/0.57    inference(rectify,[],[f32])).
% 1.60/0.57  fof(f32,plain,(
% 1.60/0.57    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0))) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.60/0.57    inference(flattening,[],[f31])).
% 1.60/0.57  fof(f31,plain,(
% 1.60/0.57    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)))) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.60/0.57    inference(nnf_transformation,[],[f15])).
% 1.60/0.57  fof(f15,plain,(
% 1.60/0.57    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.60/0.57    inference(flattening,[],[f14])).
% 1.60/0.57  fof(f14,plain,(
% 1.60/0.57    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.60/0.57    inference(ennf_transformation,[],[f6])).
% 1.60/0.57  fof(f6,axiom,(
% 1.60/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))))),
% 1.60/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_funct_1)).
% 1.60/0.57  fof(f42,plain,(
% 1.60/0.57    v1_relat_1(sK0)),
% 1.60/0.57    inference(cnf_transformation,[],[f30])).
% 1.60/0.57  fof(f43,plain,(
% 1.60/0.57    v1_funct_1(sK0)),
% 1.60/0.57    inference(cnf_transformation,[],[f30])).
% 1.60/0.57  fof(f76,plain,(
% 1.60/0.57    ~r1_tarski(sK2,k1_relat_1(sK0)) | spl5_2),
% 1.60/0.57    inference(avatar_component_clause,[],[f75])).
% 1.60/0.57  fof(f75,plain,(
% 1.60/0.57    spl5_2 <=> r1_tarski(sK2,k1_relat_1(sK0))),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.60/0.57  fof(f648,plain,(
% 1.60/0.57    ~spl5_2 | ~spl5_3 | spl5_1),
% 1.60/0.57    inference(avatar_split_clause,[],[f647,f72,f78,f75])).
% 1.60/0.57  fof(f78,plain,(
% 1.60/0.57    spl5_3 <=> r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.60/0.57  fof(f647,plain,(
% 1.60/0.57    ~r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~r1_tarski(sK2,k1_relat_1(sK0)) | spl5_1),
% 1.60/0.57    inference(resolution,[],[f170,f73])).
% 1.60/0.57  fof(f73,plain,(
% 1.60/0.57    ~r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) | spl5_1),
% 1.60/0.57    inference(avatar_component_clause,[],[f72])).
% 1.60/0.57  fof(f170,plain,(
% 1.60/0.57    ( ! [X0] : (r1_tarski(X0,k1_relat_1(k5_relat_1(sK0,sK1))) | ~r1_tarski(k9_relat_1(sK0,X0),k1_relat_1(sK1)) | ~r1_tarski(X0,k1_relat_1(sK0))) )),
% 1.60/0.57    inference(global_subsumption,[],[f43,f42,f166])).
% 1.60/0.57  fof(f166,plain,(
% 1.60/0.57    ( ! [X0] : (r1_tarski(X0,k1_relat_1(k5_relat_1(sK0,sK1))) | ~r1_tarski(k9_relat_1(sK0,X0),k1_relat_1(sK1)) | ~r1_tarski(X0,k1_relat_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)) )),
% 1.60/0.57    inference(superposition,[],[f64,f117])).
% 1.60/0.57  fof(f64,plain,(
% 1.60/0.57    ( ! [X2,X0,X1] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.60/0.57    inference(cnf_transformation,[],[f22])).
% 1.60/0.57  fof(f22,plain,(
% 1.60/0.57    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.60/0.57    inference(flattening,[],[f21])).
% 1.60/0.57  fof(f21,plain,(
% 1.60/0.57    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.60/0.57    inference(ennf_transformation,[],[f8])).
% 1.60/0.57  fof(f8,axiom,(
% 1.60/0.57    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 1.60/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).
% 1.60/0.57  fof(f515,plain,(
% 1.60/0.57    ~spl5_1 | ~spl5_42 | ~spl5_8 | ~spl5_35),
% 1.60/0.57    inference(avatar_split_clause,[],[f508,f323,f125,f402,f72])).
% 1.60/0.57  fof(f402,plain,(
% 1.60/0.57    spl5_42 <=> r1_tarski(sK0,sK0)),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).
% 1.60/0.57  fof(f125,plain,(
% 1.60/0.57    spl5_8 <=> v1_relat_1(sK0)),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.60/0.57  fof(f323,plain,(
% 1.60/0.57    spl5_35 <=> ! [X1,X0] : (~r1_tarski(k9_relat_1(X0,X1),k1_relat_1(sK1)) | ~v1_relat_1(X0) | ~r1_tarski(sK0,X0) | ~r1_tarski(sK2,X1))),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 1.60/0.57  fof(f508,plain,(
% 1.60/0.57    ~v1_relat_1(sK0) | ~r1_tarski(sK0,sK0) | ~r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) | ~spl5_35),
% 1.60/0.57    inference(resolution,[],[f324,f171])).
% 1.60/0.57  fof(f171,plain,(
% 1.60/0.57    r1_tarski(k9_relat_1(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),k1_relat_1(sK1))),
% 1.60/0.57    inference(global_subsumption,[],[f43,f42,f167])).
% 1.60/0.57  fof(f167,plain,(
% 1.60/0.57    r1_tarski(k9_relat_1(sK0,k1_relat_1(k5_relat_1(sK0,sK1))),k1_relat_1(sK1)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 1.60/0.57    inference(superposition,[],[f56,f117])).
% 1.60/0.57  fof(f56,plain,(
% 1.60/0.57    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.60/0.57    inference(cnf_transformation,[],[f17])).
% 1.60/0.57  fof(f17,plain,(
% 1.60/0.57    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.60/0.57    inference(flattening,[],[f16])).
% 1.60/0.57  fof(f16,plain,(
% 1.60/0.57    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.60/0.57    inference(ennf_transformation,[],[f7])).
% 1.60/0.57  fof(f7,axiom,(
% 1.60/0.57    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 1.60/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).
% 1.60/0.57  fof(f324,plain,(
% 1.60/0.57    ( ! [X0,X1] : (~r1_tarski(k9_relat_1(X0,X1),k1_relat_1(sK1)) | ~v1_relat_1(X0) | ~r1_tarski(sK0,X0) | ~r1_tarski(sK2,X1)) ) | ~spl5_35),
% 1.60/0.57    inference(avatar_component_clause,[],[f323])).
% 1.60/0.57  fof(f480,plain,(
% 1.60/0.57    spl5_42),
% 1.60/0.57    inference(avatar_contradiction_clause,[],[f476])).
% 1.60/0.57  fof(f476,plain,(
% 1.60/0.57    $false | spl5_42),
% 1.60/0.57    inference(resolution,[],[f403,f70])).
% 1.60/0.57  fof(f70,plain,(
% 1.60/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.60/0.57    inference(equality_resolution,[],[f57])).
% 1.60/0.57  fof(f57,plain,(
% 1.60/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.60/0.57    inference(cnf_transformation,[],[f37])).
% 1.60/0.57  fof(f37,plain,(
% 1.60/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.60/0.57    inference(flattening,[],[f36])).
% 1.60/0.57  fof(f36,plain,(
% 1.60/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.60/0.57    inference(nnf_transformation,[],[f2])).
% 1.60/0.57  fof(f2,axiom,(
% 1.60/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.60/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.60/0.57  fof(f403,plain,(
% 1.60/0.57    ~r1_tarski(sK0,sK0) | spl5_42),
% 1.60/0.57    inference(avatar_component_clause,[],[f402])).
% 1.60/0.57  fof(f457,plain,(
% 1.60/0.57    ~spl5_8 | spl5_35 | spl5_3),
% 1.60/0.57    inference(avatar_split_clause,[],[f451,f78,f323,f125])).
% 1.60/0.57  fof(f451,plain,(
% 1.60/0.57    ( ! [X0,X1] : (~r1_tarski(k9_relat_1(X0,X1),k1_relat_1(sK1)) | ~r1_tarski(sK2,X1) | ~r1_tarski(sK0,X0) | ~v1_relat_1(X0) | ~v1_relat_1(sK0)) ) | spl5_3),
% 1.60/0.57    inference(resolution,[],[f444,f63])).
% 1.60/0.57  fof(f63,plain,(
% 1.60/0.57    ( ! [X2,X0,X3,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) | ~r1_tarski(X0,X1) | ~r1_tarski(X2,X3) | ~v1_relat_1(X3) | ~v1_relat_1(X2)) )),
% 1.60/0.57    inference(cnf_transformation,[],[f20])).
% 1.60/0.57  fof(f20,plain,(
% 1.60/0.57    ! [X0,X1,X2] : (! [X3] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) | ~r1_tarski(X0,X1) | ~r1_tarski(X2,X3) | ~v1_relat_1(X3)) | ~v1_relat_1(X2))),
% 1.60/0.57    inference(flattening,[],[f19])).
% 1.60/0.57  fof(f19,plain,(
% 1.60/0.57    ! [X0,X1,X2] : (! [X3] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) | (~r1_tarski(X0,X1) | ~r1_tarski(X2,X3))) | ~v1_relat_1(X3)) | ~v1_relat_1(X2))),
% 1.60/0.57    inference(ennf_transformation,[],[f4])).
% 1.60/0.57  fof(f4,axiom,(
% 1.60/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)))))),
% 1.60/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_relat_1)).
% 1.60/0.57  fof(f444,plain,(
% 1.60/0.57    ( ! [X0] : (~r1_tarski(k9_relat_1(sK0,sK2),X0) | ~r1_tarski(X0,k1_relat_1(sK1))) ) | spl5_3),
% 1.60/0.57    inference(resolution,[],[f79,f65])).
% 1.60/0.57  fof(f65,plain,(
% 1.60/0.57    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.60/0.57    inference(cnf_transformation,[],[f24])).
% 1.60/0.57  fof(f24,plain,(
% 1.60/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.60/0.57    inference(flattening,[],[f23])).
% 1.60/0.57  fof(f23,plain,(
% 1.60/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.60/0.57    inference(ennf_transformation,[],[f3])).
% 1.60/0.57  fof(f3,axiom,(
% 1.60/0.57    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.60/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.60/0.57  fof(f79,plain,(
% 1.60/0.57    ~r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | spl5_3),
% 1.60/0.57    inference(avatar_component_clause,[],[f78])).
% 1.60/0.57  fof(f148,plain,(
% 1.60/0.57    spl5_8),
% 1.60/0.57    inference(avatar_contradiction_clause,[],[f147])).
% 1.60/0.57  fof(f147,plain,(
% 1.60/0.57    $false | spl5_8),
% 1.60/0.57    inference(subsumption_resolution,[],[f42,f126])).
% 1.60/0.57  fof(f126,plain,(
% 1.60/0.57    ~v1_relat_1(sK0) | spl5_8),
% 1.60/0.57    inference(avatar_component_clause,[],[f125])).
% 1.60/0.57  fof(f85,plain,(
% 1.60/0.57    spl5_1 | spl5_2),
% 1.60/0.57    inference(avatar_split_clause,[],[f46,f75,f72])).
% 1.60/0.57  fof(f46,plain,(
% 1.60/0.57    r1_tarski(sK2,k1_relat_1(sK0)) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 1.60/0.57    inference(cnf_transformation,[],[f30])).
% 1.60/0.57  fof(f83,plain,(
% 1.60/0.57    spl5_1 | spl5_3),
% 1.60/0.57    inference(avatar_split_clause,[],[f47,f78,f72])).
% 1.60/0.57  fof(f47,plain,(
% 1.60/0.57    r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 1.60/0.57    inference(cnf_transformation,[],[f30])).
% 1.60/0.57  fof(f80,plain,(
% 1.60/0.57    ~spl5_1 | ~spl5_2 | ~spl5_3),
% 1.60/0.57    inference(avatar_split_clause,[],[f48,f78,f75,f72])).
% 1.60/0.57  fof(f48,plain,(
% 1.60/0.57    ~r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~r1_tarski(sK2,k1_relat_1(sK0)) | ~r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 1.60/0.57    inference(cnf_transformation,[],[f30])).
% 1.60/0.57  % SZS output end Proof for theBenchmark
% 1.60/0.57  % (3604)------------------------------
% 1.60/0.57  % (3604)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.57  % (3604)Termination reason: Refutation
% 1.60/0.57  
% 1.60/0.57  % (3604)Memory used [KB]: 11257
% 1.60/0.57  % (3604)Time elapsed: 0.168 s
% 1.60/0.57  % (3604)------------------------------
% 1.60/0.57  % (3604)------------------------------
% 1.60/0.58  % (3601)Success in time 0.223 s
%------------------------------------------------------------------------------
