%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0709+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 229 expanded)
%              Number of leaves         :   13 (  65 expanded)
%              Depth                    :   13
%              Number of atoms          :  413 (1309 expanded)
%              Number of equality atoms :   67 ( 214 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f231,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f129,f158,f171,f180,f181,f222])).

fof(f222,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_contradiction_clause,[],[f221])).

fof(f221,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f213,f184])).

fof(f184,plain,
    ( ~ r2_hidden(sK2(sK1,k9_relat_1(sK1,sK0),sK0),k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f59,f123,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f123,plain,
    ( ~ r2_hidden(sK2(sK1,k9_relat_1(sK1,sK0),sK0),sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl6_1
  <=> r2_hidden(sK2(sK1,k9_relat_1(sK1,sK0),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f59,plain,(
    ! [X0] : r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) ),
    inference(unit_resulting_resolution,[],[f30,f31,f33,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).

fof(f33,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0))
    & v2_funct_1(sK1)
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
        & v2_funct_1(X1)
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0))
      & v2_funct_1(sK1)
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( v2_funct_1(X1)
            & r1_tarski(X0,k1_relat_1(X1)) )
         => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

fof(f31,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f30,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f213,plain,
    ( r2_hidden(sK2(sK1,k9_relat_1(sK1,sK0),sK0),k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f30,f31,f128,f157,f51])).

fof(f51,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k10_relat_1(X0,X1))
      | ~ r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | k10_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ~ r2_hidden(k1_funct_1(X0,sK2(X0,X1,X2)),X1)
                | ~ r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0))
                | ~ r2_hidden(sK2(X0,X1,X2),X2) )
              & ( ( r2_hidden(k1_funct_1(X0,sK2(X0,X1,X2)),X1)
                  & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f22])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
            | ~ r2_hidden(X3,k1_relat_1(X0))
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
              & r2_hidden(X3,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k1_funct_1(X0,sK2(X0,X1,X2)),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0))
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( r2_hidden(k1_funct_1(X0,sK2(X0,X1,X2)),X1)
            & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0)) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f157,plain,
    ( r2_hidden(k1_funct_1(sK1,sK2(sK1,k9_relat_1(sK1,sK0),sK0)),k9_relat_1(sK1,sK0))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl6_3
  <=> r2_hidden(k1_funct_1(sK1,sK2(sK1,k9_relat_1(sK1,sK0),sK0)),k9_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f128,plain,
    ( r2_hidden(sK2(sK1,k9_relat_1(sK1,sK0),sK0),k1_relat_1(sK1))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl6_2
  <=> r2_hidden(sK2(sK1,k9_relat_1(sK1,sK0),sK0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f181,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f159,f155,f126,f122])).

fof(f159,plain,
    ( ~ r2_hidden(k1_funct_1(sK1,sK2(sK1,k9_relat_1(sK1,sK0),sK0)),k9_relat_1(sK1,sK0))
    | ~ r2_hidden(sK2(sK1,k9_relat_1(sK1,sK0),sK0),k1_relat_1(sK1))
    | ~ r2_hidden(sK2(sK1,k9_relat_1(sK1,sK0),sK0),sK0) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X2] :
      ( sK0 != X2
      | ~ r2_hidden(k1_funct_1(sK1,sK2(sK1,k9_relat_1(sK1,sK0),X2)),k9_relat_1(sK1,sK0))
      | ~ r2_hidden(sK2(sK1,k9_relat_1(sK1,sK0),X2),k1_relat_1(sK1))
      | ~ r2_hidden(sK2(sK1,k9_relat_1(sK1,sK0),X2),X2) ) ),
    inference(subsumption_resolution,[],[f79,f30])).

fof(f79,plain,(
    ! [X2] :
      ( sK0 != X2
      | ~ r2_hidden(k1_funct_1(sK1,sK2(sK1,k9_relat_1(sK1,sK0),X2)),k9_relat_1(sK1,sK0))
      | ~ r2_hidden(sK2(sK1,k9_relat_1(sK1,sK0),X2),k1_relat_1(sK1))
      | ~ r2_hidden(sK2(sK1,k9_relat_1(sK1,sK0),X2),X2)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f66,f31])).

fof(f66,plain,(
    ! [X2] :
      ( sK0 != X2
      | ~ r2_hidden(k1_funct_1(sK1,sK2(sK1,k9_relat_1(sK1,sK0),X2)),k9_relat_1(sK1,sK0))
      | ~ r2_hidden(sK2(sK1,k9_relat_1(sK1,sK0),X2),k1_relat_1(sK1))
      | ~ r2_hidden(sK2(sK1,k9_relat_1(sK1,sK0),X2),X2)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f34,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | ~ r2_hidden(k1_funct_1(X0,sK2(X0,X1,X2)),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0))
      | ~ r2_hidden(sK2(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f34,plain,(
    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f180,plain,
    ( spl6_2
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f164,f122,f126])).

fof(f164,plain,
    ( r2_hidden(sK2(sK1,k9_relat_1(sK1,sK0),sK0),k1_relat_1(sK1))
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f32,f124,f50])).

fof(f124,plain,
    ( r2_hidden(sK2(sK1,k9_relat_1(sK1,sK0),sK0),sK0)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f122])).

fof(f32,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f171,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | spl6_3 ),
    inference(avatar_contradiction_clause,[],[f170])).

fof(f170,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3 ),
    inference(subsumption_resolution,[],[f165,f156])).

fof(f156,plain,
    ( ~ r2_hidden(k1_funct_1(sK1,sK2(sK1,k9_relat_1(sK1,sK0),sK0)),k9_relat_1(sK1,sK0))
    | spl6_3 ),
    inference(avatar_component_clause,[],[f155])).

fof(f165,plain,
    ( r2_hidden(k1_funct_1(sK1,sK2(sK1,k9_relat_1(sK1,sK0),sK0)),k9_relat_1(sK1,sK0))
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f30,f31,f128,f124,f55])).

fof(f55,plain,(
    ! [X0,X7,X1] :
      ( r2_hidden(k1_funct_1(X0,X7),k9_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X7,X1] :
      ( r2_hidden(k1_funct_1(X0,X7),X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | k1_funct_1(X0,X7) != X6
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f25,f28,f27,f26])).

fof(f26,plain,(
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

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = sK3(X0,X1,X2)
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( sK3(X0,X1,X2) = k1_funct_1(X0,sK4(X0,X1,X2))
        & r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK5(X0,X1,X6)) = X6
        & r2_hidden(sK5(X0,X1,X6),X1)
        & r2_hidden(sK5(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).

fof(f158,plain,
    ( spl6_1
    | spl6_3 ),
    inference(avatar_split_clause,[],[f153,f155,f122])).

fof(f153,plain,
    ( r2_hidden(k1_funct_1(sK1,sK2(sK1,k9_relat_1(sK1,sK0),sK0)),k9_relat_1(sK1,sK0))
    | r2_hidden(sK2(sK1,k9_relat_1(sK1,sK0),sK0),sK0) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X1] :
      ( sK0 != X1
      | r2_hidden(k1_funct_1(sK1,sK2(sK1,k9_relat_1(sK1,sK0),X1)),k9_relat_1(sK1,sK0))
      | r2_hidden(sK2(sK1,k9_relat_1(sK1,sK0),X1),X1) ) ),
    inference(subsumption_resolution,[],[f77,f30])).

fof(f77,plain,(
    ! [X1] :
      ( sK0 != X1
      | r2_hidden(k1_funct_1(sK1,sK2(sK1,k9_relat_1(sK1,sK0),X1)),k9_relat_1(sK1,sK0))
      | r2_hidden(sK2(sK1,k9_relat_1(sK1,sK0),X1),X1)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f65,f31])).

fof(f65,plain,(
    ! [X1] :
      ( sK0 != X1
      | r2_hidden(k1_funct_1(sK1,sK2(sK1,k9_relat_1(sK1,sK0),X1)),k9_relat_1(sK1,sK0))
      | r2_hidden(sK2(sK1,k9_relat_1(sK1,sK0),X1),X1)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f34,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | r2_hidden(k1_funct_1(X0,sK2(X0,X1,X2)),X1)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f129,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f120,f126,f122])).

fof(f120,plain,
    ( r2_hidden(sK2(sK1,k9_relat_1(sK1,sK0),sK0),k1_relat_1(sK1))
    | r2_hidden(sK2(sK1,k9_relat_1(sK1,sK0),sK0),sK0) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X0] :
      ( sK0 != X0
      | r2_hidden(sK2(sK1,k9_relat_1(sK1,sK0),X0),k1_relat_1(sK1))
      | r2_hidden(sK2(sK1,k9_relat_1(sK1,sK0),X0),X0) ) ),
    inference(subsumption_resolution,[],[f75,f30])).

fof(f75,plain,(
    ! [X0] :
      ( sK0 != X0
      | r2_hidden(sK2(sK1,k9_relat_1(sK1,sK0),X0),k1_relat_1(sK1))
      | r2_hidden(sK2(sK1,k9_relat_1(sK1,sK0),X0),X0)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f64,f31])).

fof(f64,plain,(
    ! [X0] :
      ( sK0 != X0
      | r2_hidden(sK2(sK1,k9_relat_1(sK1,sK0),X0),k1_relat_1(sK1))
      | r2_hidden(sK2(sK1,k9_relat_1(sK1,sK0),X0),X0)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f34,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0))
      | r2_hidden(sK2(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

%------------------------------------------------------------------------------
