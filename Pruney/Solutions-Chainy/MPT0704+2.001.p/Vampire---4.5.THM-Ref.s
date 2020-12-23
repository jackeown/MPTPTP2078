%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:25 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 225 expanded)
%              Number of leaves         :   20 (  78 expanded)
%              Depth                    :   13
%              Number of atoms          :  314 ( 854 expanded)
%              Number of equality atoms :   49 (  82 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f317,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f73,f77,f147,f251,f287,f292,f304,f313,f316])).

fof(f316,plain,(
    ~ spl7_6 ),
    inference(avatar_contradiction_clause,[],[f315])).

fof(f315,plain,
    ( $false
    | ~ spl7_6 ),
    inference(equality_resolution,[],[f105])).

fof(f105,plain,
    ( ! [X0] : k1_tarski(X0) != k1_tarski(sK4(sK5(sK2)))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl7_6
  <=> ! [X0] : k1_tarski(X0) != k1_tarski(sK4(sK5(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f313,plain,
    ( spl7_5
    | ~ spl7_7 ),
    inference(avatar_contradiction_clause,[],[f312])).

fof(f312,plain,
    ( $false
    | spl7_5
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f311,f101])).

fof(f101,plain,
    ( ~ sP0(sK2)
    | spl7_5 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl7_5
  <=> sP0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f311,plain,
    ( sP0(sK2)
    | ~ spl7_7 ),
    inference(resolution,[],[f250,f48])).

fof(f48,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),k2_relat_1(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ( ! [X2] : k1_tarski(X2) != k10_relat_1(X0,k1_tarski(sK5(X0)))
          & r2_hidden(sK5(X0),k2_relat_1(X0)) ) )
      & ( ! [X3] :
            ( k10_relat_1(X0,k1_tarski(X3)) = k1_tarski(sK6(X0,X3))
            | ~ r2_hidden(X3,k2_relat_1(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f31,f33,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] : k10_relat_1(X0,k1_tarski(X1)) != k1_tarski(X2)
          & r2_hidden(X1,k2_relat_1(X0)) )
     => ( ! [X2] : k1_tarski(X2) != k10_relat_1(X0,k1_tarski(sK5(X0)))
        & r2_hidden(sK5(X0),k2_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X3,X0] :
      ( ? [X4] : k10_relat_1(X0,k1_tarski(X3)) = k1_tarski(X4)
     => k10_relat_1(X0,k1_tarski(X3)) = k1_tarski(sK6(X0,X3)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ! [X2] : k10_relat_1(X0,k1_tarski(X1)) != k1_tarski(X2)
            & r2_hidden(X1,k2_relat_1(X0)) ) )
      & ( ! [X3] :
            ( ? [X4] : k10_relat_1(X0,k1_tarski(X3)) = k1_tarski(X4)
            | ~ r2_hidden(X3,k2_relat_1(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ! [X2] : k10_relat_1(X0,k1_tarski(X1)) != k1_tarski(X2)
            & r2_hidden(X1,k2_relat_1(X0)) ) )
      & ( ! [X1] :
            ( ? [X2] : k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(X2)
            | ~ r2_hidden(X1,k2_relat_1(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ! [X1] :
          ( ? [X2] : k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(X2)
          | ~ r2_hidden(X1,k2_relat_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f250,plain,
    ( ~ r2_hidden(sK5(sK2),k2_relat_1(sK2))
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f236,f40])).

fof(f40,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( ! [X2] : ~ r1_tarski(k10_relat_1(sK2,k1_tarski(sK3)),k1_tarski(X2))
      | ~ v2_funct_1(sK2) )
    & ( ! [X3] : r1_tarski(k10_relat_1(sK2,k1_tarski(X3)),k1_tarski(sK4(X3)))
      | v2_funct_1(sK2) )
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f24,f27,f26,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( ( ? [X1] :
            ! [X2] : ~ r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2))
          | ~ v2_funct_1(X0) )
        & ( ! [X3] :
            ? [X4] : r1_tarski(k10_relat_1(X0,k1_tarski(X3)),k1_tarski(X4))
          | v2_funct_1(X0) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( ? [X1] :
          ! [X2] : ~ r1_tarski(k10_relat_1(sK2,k1_tarski(X1)),k1_tarski(X2))
        | ~ v2_funct_1(sK2) )
      & ( ! [X3] :
          ? [X4] : r1_tarski(k10_relat_1(sK2,k1_tarski(X3)),k1_tarski(X4))
        | v2_funct_1(sK2) )
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X1] :
      ! [X2] : ~ r1_tarski(k10_relat_1(sK2,k1_tarski(X1)),k1_tarski(X2))
   => ! [X2] : ~ r1_tarski(k10_relat_1(sK2,k1_tarski(sK3)),k1_tarski(X2)) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X3] :
      ( ? [X4] : r1_tarski(k10_relat_1(sK2,k1_tarski(X3)),k1_tarski(X4))
     => r1_tarski(k10_relat_1(sK2,k1_tarski(X3)),k1_tarski(sK4(X3))) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0] :
      ( ( ? [X1] :
          ! [X2] : ~ r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2))
        | ~ v2_funct_1(X0) )
      & ( ! [X3] :
          ? [X4] : r1_tarski(k10_relat_1(X0,k1_tarski(X3)),k1_tarski(X4))
        | v2_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ( ? [X1] :
          ! [X2] : ~ r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2))
        | ~ v2_funct_1(X0) )
      & ( ! [X1] :
          ? [X2] : r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2))
        | v2_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ( ? [X1] :
          ! [X2] : ~ r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2))
        | ~ v2_funct_1(X0) )
      & ( ! [X1] :
          ? [X2] : r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2))
        | v2_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ( v2_funct_1(X0)
      <~> ! [X1] :
          ? [X2] : r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2)) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ( v2_funct_1(X0)
      <~> ! [X1] :
          ? [X2] : r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2)) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
        <=> ! [X1] :
            ? [X2] : r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2)) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1] :
          ? [X2] : r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_funct_1)).

fof(f236,plain,
    ( ~ r2_hidden(sK5(sK2),k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl7_7 ),
    inference(trivial_inequality_removal,[],[f235])).

fof(f235,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r2_hidden(sK5(sK2),k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl7_7 ),
    inference(superposition,[],[f52,f136])).

fof(f136,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK5(sK2)))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl7_7
  <=> k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK5(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,k2_relat_1(X1))
          | k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) )
        & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
          | ~ r2_hidden(X0,k2_relat_1(X1)) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k2_relat_1(X1))
      <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k2_relat_1(X1))
      <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).

fof(f304,plain,
    ( spl7_1
    | ~ spl7_5 ),
    inference(avatar_contradiction_clause,[],[f303])).

fof(f303,plain,
    ( $false
    | spl7_1
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f302,f69])).

fof(f69,plain,
    ( ~ v2_funct_1(sK2)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl7_1
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f302,plain,
    ( v2_funct_1(sK2)
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f301,f41])).

fof(f41,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f301,plain,
    ( ~ v1_funct_1(sK2)
    | v2_funct_1(sK2)
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f300,f40])).

fof(f300,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | v2_funct_1(sK2)
    | ~ spl7_5 ),
    inference(resolution,[],[f102,f79])).

fof(f79,plain,(
    ! [X1] :
      ( ~ sP0(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | v2_funct_1(X1) ) ),
    inference(resolution,[],[f50,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | ~ sP0(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( ( sP0(X0)
          | ~ v2_funct_1(X0) )
        & ( v2_funct_1(X0)
          | ~ sP0(X0) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( sP0(X0)
      <=> v2_funct_1(X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f50,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f14,f20,f19])).

fof(f14,plain,(
    ! [X0] :
      ( ( ! [X1] :
            ( ? [X2] : k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(X2)
            | ~ r2_hidden(X1,k2_relat_1(X0)) )
      <=> v2_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( ! [X1] :
            ( ? [X2] : k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(X2)
            | ~ r2_hidden(X1,k2_relat_1(X0)) )
      <=> v2_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ! [X1] :
            ~ ( ! [X2] : k10_relat_1(X0,k1_tarski(X1)) != k1_tarski(X2)
              & r2_hidden(X1,k2_relat_1(X0)) )
      <=> v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_funct_1)).

fof(f102,plain,
    ( sP0(sK2)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f100])).

fof(f292,plain,
    ( ~ spl7_1
    | spl7_5 ),
    inference(avatar_contradiction_clause,[],[f291])).

fof(f291,plain,
    ( $false
    | ~ spl7_1
    | spl7_5 ),
    inference(subsumption_resolution,[],[f290,f41])).

fof(f290,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl7_1
    | spl7_5 ),
    inference(subsumption_resolution,[],[f289,f68])).

fof(f68,plain,
    ( v2_funct_1(sK2)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f67])).

fof(f289,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | spl7_5 ),
    inference(subsumption_resolution,[],[f288,f40])).

fof(f288,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | spl7_5 ),
    inference(resolution,[],[f101,f78])).

fof(f78,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f50,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | ~ v2_funct_1(X0)
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f287,plain,
    ( ~ spl7_5
    | ~ spl7_2
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f286,f203,f71,f100])).

fof(f71,plain,
    ( spl7_2
  <=> ! [X2] : ~ r1_tarski(k10_relat_1(sK2,k1_tarski(sK3)),k1_tarski(X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f203,plain,
    ( spl7_10
  <=> r2_hidden(sK3,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f286,plain,
    ( ~ sP0(sK2)
    | ~ spl7_2
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f281,f205])).

fof(f205,plain,
    ( r2_hidden(sK3,k2_relat_1(sK2))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f203])).

fof(f281,plain,
    ( ~ r2_hidden(sK3,k2_relat_1(sK2))
    | ~ sP0(sK2)
    | ~ spl7_2 ),
    inference(resolution,[],[f274,f62])).

fof(f62,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f274,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k10_relat_1(sK2,k1_tarski(sK3)),k10_relat_1(X0,k1_tarski(X1)))
        | ~ r2_hidden(X1,k2_relat_1(X0))
        | ~ sP0(X0) )
    | ~ spl7_2 ),
    inference(superposition,[],[f72,f47])).

fof(f47,plain,(
    ! [X0,X3] :
      ( k10_relat_1(X0,k1_tarski(X3)) = k1_tarski(sK6(X0,X3))
      | ~ r2_hidden(X3,k2_relat_1(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f72,plain,
    ( ! [X2] : ~ r1_tarski(k10_relat_1(sK2,k1_tarski(sK3)),k1_tarski(X2))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f251,plain,
    ( spl7_10
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f223,f71,f203])).

fof(f223,plain,
    ( r2_hidden(sK3,k2_relat_1(sK2))
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f222,f40])).

fof(f222,plain,
    ( r2_hidden(sK3,k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f182,f44])).

fof(f44,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f182,plain,
    ( ! [X23] :
        ( ~ r1_tarski(k1_xboole_0,k1_tarski(X23))
        | r2_hidden(sK3,k2_relat_1(sK2))
        | ~ v1_relat_1(sK2) )
    | ~ spl7_2 ),
    inference(superposition,[],[f72,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
      | r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f147,plain,
    ( spl7_7
    | spl7_5
    | spl7_6
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f131,f75,f104,f100,f134])).

fof(f75,plain,
    ( spl7_3
  <=> ! [X3] : r1_tarski(k10_relat_1(sK2,k1_tarski(X3)),k1_tarski(sK4(X3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f131,plain,
    ( ! [X5] :
        ( k1_tarski(sK4(sK5(sK2))) != k1_tarski(X5)
        | sP0(sK2)
        | k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK5(sK2))) )
    | ~ spl7_3 ),
    inference(superposition,[],[f49,f121])).

fof(f121,plain,
    ( ! [X0] :
        ( k10_relat_1(sK2,k1_tarski(X0)) = k1_tarski(sK4(X0))
        | k1_xboole_0 = k10_relat_1(sK2,k1_tarski(X0)) )
    | ~ spl7_3 ),
    inference(resolution,[],[f57,f76])).

fof(f76,plain,
    ( ! [X3] : r1_tarski(k10_relat_1(sK2,k1_tarski(X3)),k1_tarski(sK4(X3)))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f75])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_zfmisc_1)).

fof(f49,plain,(
    ! [X2,X0] :
      ( k1_tarski(X2) != k10_relat_1(X0,k1_tarski(sK5(X0)))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f77,plain,
    ( spl7_1
    | spl7_3 ),
    inference(avatar_split_clause,[],[f42,f75,f67])).

fof(f42,plain,(
    ! [X3] :
      ( r1_tarski(k10_relat_1(sK2,k1_tarski(X3)),k1_tarski(sK4(X3)))
      | v2_funct_1(sK2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f73,plain,
    ( ~ spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f43,f71,f67])).

fof(f43,plain,(
    ! [X2] :
      ( ~ r1_tarski(k10_relat_1(sK2,k1_tarski(sK3)),k1_tarski(X2))
      | ~ v2_funct_1(sK2) ) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:05:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (29875)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.53  % (29875)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.54  % (29883)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f317,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f73,f77,f147,f251,f287,f292,f304,f313,f316])).
% 0.22/0.54  fof(f316,plain,(
% 0.22/0.54    ~spl7_6),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f315])).
% 0.22/0.54  fof(f315,plain,(
% 0.22/0.54    $false | ~spl7_6),
% 0.22/0.54    inference(equality_resolution,[],[f105])).
% 0.22/0.54  fof(f105,plain,(
% 0.22/0.54    ( ! [X0] : (k1_tarski(X0) != k1_tarski(sK4(sK5(sK2)))) ) | ~spl7_6),
% 0.22/0.54    inference(avatar_component_clause,[],[f104])).
% 0.22/0.54  fof(f104,plain,(
% 0.22/0.54    spl7_6 <=> ! [X0] : k1_tarski(X0) != k1_tarski(sK4(sK5(sK2)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.22/0.54  fof(f313,plain,(
% 0.22/0.54    spl7_5 | ~spl7_7),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f312])).
% 0.22/0.54  fof(f312,plain,(
% 0.22/0.54    $false | (spl7_5 | ~spl7_7)),
% 0.22/0.54    inference(subsumption_resolution,[],[f311,f101])).
% 0.22/0.54  fof(f101,plain,(
% 0.22/0.54    ~sP0(sK2) | spl7_5),
% 0.22/0.54    inference(avatar_component_clause,[],[f100])).
% 0.22/0.54  fof(f100,plain,(
% 0.22/0.54    spl7_5 <=> sP0(sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.22/0.54  fof(f311,plain,(
% 0.22/0.54    sP0(sK2) | ~spl7_7),
% 0.22/0.54    inference(resolution,[],[f250,f48])).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    ( ! [X0] : (r2_hidden(sK5(X0),k2_relat_1(X0)) | sP0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ! [X0] : ((sP0(X0) | (! [X2] : k1_tarski(X2) != k10_relat_1(X0,k1_tarski(sK5(X0))) & r2_hidden(sK5(X0),k2_relat_1(X0)))) & (! [X3] : (k10_relat_1(X0,k1_tarski(X3)) = k1_tarski(sK6(X0,X3)) | ~r2_hidden(X3,k2_relat_1(X0))) | ~sP0(X0)))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f31,f33,f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ! [X0] : (? [X1] : (! [X2] : k10_relat_1(X0,k1_tarski(X1)) != k1_tarski(X2) & r2_hidden(X1,k2_relat_1(X0))) => (! [X2] : k1_tarski(X2) != k10_relat_1(X0,k1_tarski(sK5(X0))) & r2_hidden(sK5(X0),k2_relat_1(X0))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ! [X3,X0] : (? [X4] : k10_relat_1(X0,k1_tarski(X3)) = k1_tarski(X4) => k10_relat_1(X0,k1_tarski(X3)) = k1_tarski(sK6(X0,X3)))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ! [X0] : ((sP0(X0) | ? [X1] : (! [X2] : k10_relat_1(X0,k1_tarski(X1)) != k1_tarski(X2) & r2_hidden(X1,k2_relat_1(X0)))) & (! [X3] : (? [X4] : k10_relat_1(X0,k1_tarski(X3)) = k1_tarski(X4) | ~r2_hidden(X3,k2_relat_1(X0))) | ~sP0(X0)))),
% 0.22/0.54    inference(rectify,[],[f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ! [X0] : ((sP0(X0) | ? [X1] : (! [X2] : k10_relat_1(X0,k1_tarski(X1)) != k1_tarski(X2) & r2_hidden(X1,k2_relat_1(X0)))) & (! [X1] : (? [X2] : k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(X2) | ~r2_hidden(X1,k2_relat_1(X0))) | ~sP0(X0)))),
% 0.22/0.54    inference(nnf_transformation,[],[f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ! [X0] : (sP0(X0) <=> ! [X1] : (? [X2] : k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(X2) | ~r2_hidden(X1,k2_relat_1(X0))))),
% 0.22/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.54  fof(f250,plain,(
% 0.22/0.54    ~r2_hidden(sK5(sK2),k2_relat_1(sK2)) | ~spl7_7),
% 0.22/0.54    inference(subsumption_resolution,[],[f236,f40])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    v1_relat_1(sK2)),
% 0.22/0.54    inference(cnf_transformation,[],[f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    (! [X2] : ~r1_tarski(k10_relat_1(sK2,k1_tarski(sK3)),k1_tarski(X2)) | ~v2_funct_1(sK2)) & (! [X3] : r1_tarski(k10_relat_1(sK2,k1_tarski(X3)),k1_tarski(sK4(X3))) | v2_funct_1(sK2)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f24,f27,f26,f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ? [X0] : ((? [X1] : ! [X2] : ~r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2)) | ~v2_funct_1(X0)) & (! [X3] : ? [X4] : r1_tarski(k10_relat_1(X0,k1_tarski(X3)),k1_tarski(X4)) | v2_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0)) => ((? [X1] : ! [X2] : ~r1_tarski(k10_relat_1(sK2,k1_tarski(X1)),k1_tarski(X2)) | ~v2_funct_1(sK2)) & (! [X3] : ? [X4] : r1_tarski(k10_relat_1(sK2,k1_tarski(X3)),k1_tarski(X4)) | v2_funct_1(sK2)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ? [X1] : ! [X2] : ~r1_tarski(k10_relat_1(sK2,k1_tarski(X1)),k1_tarski(X2)) => ! [X2] : ~r1_tarski(k10_relat_1(sK2,k1_tarski(sK3)),k1_tarski(X2))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ! [X3] : (? [X4] : r1_tarski(k10_relat_1(sK2,k1_tarski(X3)),k1_tarski(X4)) => r1_tarski(k10_relat_1(sK2,k1_tarski(X3)),k1_tarski(sK4(X3))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ? [X0] : ((? [X1] : ! [X2] : ~r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2)) | ~v2_funct_1(X0)) & (! [X3] : ? [X4] : r1_tarski(k10_relat_1(X0,k1_tarski(X3)),k1_tarski(X4)) | v2_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.22/0.54    inference(rectify,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ? [X0] : ((? [X1] : ! [X2] : ~r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2)) | ~v2_funct_1(X0)) & (! [X1] : ? [X2] : r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2)) | v2_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.22/0.54    inference(flattening,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ? [X0] : (((? [X1] : ! [X2] : ~r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2)) | ~v2_funct_1(X0)) & (! [X1] : ? [X2] : r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2)) | v2_funct_1(X0))) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.22/0.54    inference(nnf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,plain,(
% 0.22/0.54    ? [X0] : ((v2_funct_1(X0) <~> ! [X1] : ? [X2] : r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2))) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.22/0.54    inference(flattening,[],[f11])).
% 0.22/0.54  fof(f11,plain,(
% 0.22/0.54    ? [X0] : ((v2_funct_1(X0) <~> ! [X1] : ? [X2] : r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,negated_conjecture,(
% 0.22/0.54    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1] : ? [X2] : r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2))))),
% 0.22/0.54    inference(negated_conjecture,[],[f9])).
% 0.22/0.54  fof(f9,conjecture,(
% 0.22/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1] : ? [X2] : r1_tarski(k10_relat_1(X0,k1_tarski(X1)),k1_tarski(X2))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_funct_1)).
% 0.22/0.54  fof(f236,plain,(
% 0.22/0.54    ~r2_hidden(sK5(sK2),k2_relat_1(sK2)) | ~v1_relat_1(sK2) | ~spl7_7),
% 0.22/0.54    inference(trivial_inequality_removal,[],[f235])).
% 0.22/0.54  fof(f235,plain,(
% 0.22/0.54    k1_xboole_0 != k1_xboole_0 | ~r2_hidden(sK5(sK2),k2_relat_1(sK2)) | ~v1_relat_1(sK2) | ~spl7_7),
% 0.22/0.54    inference(superposition,[],[f52,f136])).
% 0.22/0.54  fof(f136,plain,(
% 0.22/0.54    k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK5(sK2))) | ~spl7_7),
% 0.22/0.54    inference(avatar_component_clause,[],[f134])).
% 0.22/0.54  fof(f134,plain,(
% 0.22/0.54    spl7_7 <=> k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK5(sK2)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.22/0.54  fof(f52,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f35])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ! [X0,X1] : (((r2_hidden(X0,k2_relat_1(X1)) | k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))) & (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) | ~r2_hidden(X0,k2_relat_1(X1)))) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(nnf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ! [X0,X1] : ((r2_hidden(X0,k2_relat_1(X1)) <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).
% 0.22/0.54  fof(f304,plain,(
% 0.22/0.54    spl7_1 | ~spl7_5),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f303])).
% 0.22/0.54  fof(f303,plain,(
% 0.22/0.54    $false | (spl7_1 | ~spl7_5)),
% 0.22/0.54    inference(subsumption_resolution,[],[f302,f69])).
% 0.22/0.54  fof(f69,plain,(
% 0.22/0.54    ~v2_funct_1(sK2) | spl7_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f67])).
% 0.22/0.54  fof(f67,plain,(
% 0.22/0.54    spl7_1 <=> v2_funct_1(sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.22/0.54  fof(f302,plain,(
% 0.22/0.54    v2_funct_1(sK2) | ~spl7_5),
% 0.22/0.54    inference(subsumption_resolution,[],[f301,f41])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    v1_funct_1(sK2)),
% 0.22/0.54    inference(cnf_transformation,[],[f28])).
% 0.22/0.54  fof(f301,plain,(
% 0.22/0.54    ~v1_funct_1(sK2) | v2_funct_1(sK2) | ~spl7_5),
% 0.22/0.54    inference(subsumption_resolution,[],[f300,f40])).
% 0.22/0.54  fof(f300,plain,(
% 0.22/0.54    ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | v2_funct_1(sK2) | ~spl7_5),
% 0.22/0.54    inference(resolution,[],[f102,f79])).
% 0.22/0.54  fof(f79,plain,(
% 0.22/0.54    ( ! [X1] : (~sP0(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | v2_funct_1(X1)) )),
% 0.22/0.54    inference(resolution,[],[f50,f45])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    ( ! [X0] : (~sP1(X0) | ~sP0(X0) | v2_funct_1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ! [X0] : (((sP0(X0) | ~v2_funct_1(X0)) & (v2_funct_1(X0) | ~sP0(X0))) | ~sP1(X0))),
% 0.22/0.54    inference(nnf_transformation,[],[f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ! [X0] : ((sP0(X0) <=> v2_funct_1(X0)) | ~sP1(X0))),
% 0.22/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    ( ! [X0] : (sP1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X0] : (sP1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(definition_folding,[],[f14,f20,f19])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ! [X0] : ((! [X1] : (? [X2] : k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(X2) | ~r2_hidden(X1,k2_relat_1(X0))) <=> v2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(flattening,[],[f13])).
% 0.22/0.54  fof(f13,plain,(
% 0.22/0.54    ! [X0] : ((! [X1] : (? [X2] : k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(X2) | ~r2_hidden(X1,k2_relat_1(X0))) <=> v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (! [X1] : ~(! [X2] : k10_relat_1(X0,k1_tarski(X1)) != k1_tarski(X2) & r2_hidden(X1,k2_relat_1(X0))) <=> v2_funct_1(X0)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_funct_1)).
% 0.22/0.54  fof(f102,plain,(
% 0.22/0.54    sP0(sK2) | ~spl7_5),
% 0.22/0.54    inference(avatar_component_clause,[],[f100])).
% 0.22/0.54  fof(f292,plain,(
% 0.22/0.54    ~spl7_1 | spl7_5),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f291])).
% 0.22/0.54  fof(f291,plain,(
% 0.22/0.54    $false | (~spl7_1 | spl7_5)),
% 0.22/0.54    inference(subsumption_resolution,[],[f290,f41])).
% 0.22/0.54  fof(f290,plain,(
% 0.22/0.54    ~v1_funct_1(sK2) | (~spl7_1 | spl7_5)),
% 0.22/0.54    inference(subsumption_resolution,[],[f289,f68])).
% 0.22/0.54  fof(f68,plain,(
% 0.22/0.54    v2_funct_1(sK2) | ~spl7_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f67])).
% 0.22/0.54  fof(f289,plain,(
% 0.22/0.54    ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | spl7_5),
% 0.22/0.54    inference(subsumption_resolution,[],[f288,f40])).
% 0.22/0.54  fof(f288,plain,(
% 0.22/0.54    ~v1_relat_1(sK2) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | spl7_5),
% 0.22/0.54    inference(resolution,[],[f101,f78])).
% 0.22/0.54  fof(f78,plain,(
% 0.22/0.54    ( ! [X0] : (sP0(X0) | ~v1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0)) )),
% 0.22/0.54    inference(resolution,[],[f50,f46])).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    ( ! [X0] : (~sP1(X0) | ~v2_funct_1(X0) | sP0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f29])).
% 0.22/0.54  fof(f287,plain,(
% 0.22/0.54    ~spl7_5 | ~spl7_2 | ~spl7_10),
% 0.22/0.54    inference(avatar_split_clause,[],[f286,f203,f71,f100])).
% 0.22/0.54  fof(f71,plain,(
% 0.22/0.54    spl7_2 <=> ! [X2] : ~r1_tarski(k10_relat_1(sK2,k1_tarski(sK3)),k1_tarski(X2))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.22/0.54  fof(f203,plain,(
% 0.22/0.54    spl7_10 <=> r2_hidden(sK3,k2_relat_1(sK2))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.22/0.54  fof(f286,plain,(
% 0.22/0.54    ~sP0(sK2) | (~spl7_2 | ~spl7_10)),
% 0.22/0.54    inference(subsumption_resolution,[],[f281,f205])).
% 0.22/0.54  fof(f205,plain,(
% 0.22/0.54    r2_hidden(sK3,k2_relat_1(sK2)) | ~spl7_10),
% 0.22/0.54    inference(avatar_component_clause,[],[f203])).
% 0.22/0.54  fof(f281,plain,(
% 0.22/0.54    ~r2_hidden(sK3,k2_relat_1(sK2)) | ~sP0(sK2) | ~spl7_2),
% 0.22/0.54    inference(resolution,[],[f274,f62])).
% 0.22/0.54  fof(f62,plain,(
% 0.22/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.54    inference(equality_resolution,[],[f55])).
% 0.22/0.54  fof(f55,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f37])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.54    inference(flattening,[],[f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.54    inference(nnf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.54  fof(f274,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(k10_relat_1(sK2,k1_tarski(sK3)),k10_relat_1(X0,k1_tarski(X1))) | ~r2_hidden(X1,k2_relat_1(X0)) | ~sP0(X0)) ) | ~spl7_2),
% 0.22/0.54    inference(superposition,[],[f72,f47])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    ( ! [X0,X3] : (k10_relat_1(X0,k1_tarski(X3)) = k1_tarski(sK6(X0,X3)) | ~r2_hidden(X3,k2_relat_1(X0)) | ~sP0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f34])).
% 0.22/0.54  fof(f72,plain,(
% 0.22/0.54    ( ! [X2] : (~r1_tarski(k10_relat_1(sK2,k1_tarski(sK3)),k1_tarski(X2))) ) | ~spl7_2),
% 0.22/0.54    inference(avatar_component_clause,[],[f71])).
% 0.22/0.54  fof(f251,plain,(
% 0.22/0.54    spl7_10 | ~spl7_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f223,f71,f203])).
% 0.22/0.54  fof(f223,plain,(
% 0.22/0.54    r2_hidden(sK3,k2_relat_1(sK2)) | ~spl7_2),
% 0.22/0.54    inference(subsumption_resolution,[],[f222,f40])).
% 0.22/0.54  fof(f222,plain,(
% 0.22/0.54    r2_hidden(sK3,k2_relat_1(sK2)) | ~v1_relat_1(sK2) | ~spl7_2),
% 0.22/0.54    inference(subsumption_resolution,[],[f182,f44])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.54  fof(f182,plain,(
% 0.22/0.54    ( ! [X23] : (~r1_tarski(k1_xboole_0,k1_tarski(X23)) | r2_hidden(sK3,k2_relat_1(sK2)) | ~v1_relat_1(sK2)) ) | ~spl7_2),
% 0.22/0.54    inference(superposition,[],[f72,f53])).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) | r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f35])).
% 0.22/0.54  fof(f147,plain,(
% 0.22/0.54    spl7_7 | spl7_5 | spl7_6 | ~spl7_3),
% 0.22/0.54    inference(avatar_split_clause,[],[f131,f75,f104,f100,f134])).
% 0.22/0.54  fof(f75,plain,(
% 0.22/0.54    spl7_3 <=> ! [X3] : r1_tarski(k10_relat_1(sK2,k1_tarski(X3)),k1_tarski(sK4(X3)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.22/0.54  fof(f131,plain,(
% 0.22/0.54    ( ! [X5] : (k1_tarski(sK4(sK5(sK2))) != k1_tarski(X5) | sP0(sK2) | k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK5(sK2)))) ) | ~spl7_3),
% 0.22/0.54    inference(superposition,[],[f49,f121])).
% 0.22/0.54  fof(f121,plain,(
% 0.22/0.54    ( ! [X0] : (k10_relat_1(sK2,k1_tarski(X0)) = k1_tarski(sK4(X0)) | k1_xboole_0 = k10_relat_1(sK2,k1_tarski(X0))) ) | ~spl7_3),
% 0.22/0.54    inference(resolution,[],[f57,f76])).
% 0.22/0.54  fof(f76,plain,(
% 0.22/0.54    ( ! [X3] : (r1_tarski(k10_relat_1(sK2,k1_tarski(X3)),k1_tarski(sK4(X3)))) ) | ~spl7_3),
% 0.22/0.54    inference(avatar_component_clause,[],[f75])).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f39])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.22/0.54    inference(flattening,[],[f38])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.22/0.54    inference(nnf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_zfmisc_1)).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    ( ! [X2,X0] : (k1_tarski(X2) != k10_relat_1(X0,k1_tarski(sK5(X0))) | sP0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f34])).
% 0.22/0.54  fof(f77,plain,(
% 0.22/0.54    spl7_1 | spl7_3),
% 0.22/0.54    inference(avatar_split_clause,[],[f42,f75,f67])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ( ! [X3] : (r1_tarski(k10_relat_1(sK2,k1_tarski(X3)),k1_tarski(sK4(X3))) | v2_funct_1(sK2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f28])).
% 0.22/0.54  fof(f73,plain,(
% 0.22/0.54    ~spl7_1 | spl7_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f43,f71,f67])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ( ! [X2] : (~r1_tarski(k10_relat_1(sK2,k1_tarski(sK3)),k1_tarski(X2)) | ~v2_funct_1(sK2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f28])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (29875)------------------------------
% 0.22/0.54  % (29875)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (29875)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (29875)Memory used [KB]: 6268
% 0.22/0.54  % (29875)Time elapsed: 0.094 s
% 0.22/0.54  % (29875)------------------------------
% 0.22/0.54  % (29875)------------------------------
% 0.22/0.55  % (29870)Success in time 0.176 s
%------------------------------------------------------------------------------
