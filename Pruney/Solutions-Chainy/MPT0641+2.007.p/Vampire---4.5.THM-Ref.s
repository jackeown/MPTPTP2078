%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:39 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :  200 (1033 expanded)
%              Number of leaves         :   30 ( 327 expanded)
%              Depth                    :   29
%              Number of atoms          :  754 (6538 expanded)
%              Number of equality atoms :  110 ( 998 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f705,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f106,f120,f262,f316,f327,f397,f548,f654,f676,f704])).

fof(f704,plain,
    ( spl12_3
    | ~ spl12_23 ),
    inference(avatar_contradiction_clause,[],[f703])).

fof(f703,plain,
    ( $false
    | spl12_3
    | ~ spl12_23 ),
    inference(subsumption_resolution,[],[f702,f119])).

fof(f119,plain,
    ( ~ sP0(sK5)
    | spl12_3 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl12_3
  <=> sP0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f702,plain,
    ( sP0(sK5)
    | ~ spl12_23 ),
    inference(trivial_inequality_removal,[],[f700])).

fof(f700,plain,
    ( sK7(sK5) != sK7(sK5)
    | sP0(sK5)
    | ~ spl12_23 ),
    inference(superposition,[],[f72,f571])).

fof(f571,plain,
    ( sK7(sK5) = sK8(sK5)
    | ~ spl12_23 ),
    inference(avatar_component_clause,[],[f570])).

fof(f570,plain,
    ( spl12_23
  <=> sK7(sK5) = sK8(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_23])])).

fof(f72,plain,(
    ! [X0] :
      ( sK7(X0) != sK8(X0)
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ( sK7(X0) != sK8(X0)
          & k1_funct_1(X0,sK7(X0)) = k1_funct_1(X0,sK8(X0))
          & r2_hidden(sK8(X0),k1_relat_1(X0))
          & r2_hidden(sK7(X0),k1_relat_1(X0)) ) )
      & ( ! [X3,X4] :
            ( X3 = X4
            | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
            | ~ r2_hidden(X4,k1_relat_1(X0))
            | ~ r2_hidden(X3,k1_relat_1(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f41,f42])).

fof(f42,plain,(
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

fof(f41,plain,(
    ! [X0] :
      ( ( sP0(X0)
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
        | ~ sP0(X0) ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( sP0(X0)
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
        | ~ sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ! [X1,X2] :
          ( X1 = X2
          | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
          | ~ r2_hidden(X2,k1_relat_1(X0))
          | ~ r2_hidden(X1,k1_relat_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f676,plain,
    ( spl12_6
    | ~ spl12_10
    | ~ spl12_20 ),
    inference(avatar_contradiction_clause,[],[f675])).

fof(f675,plain,
    ( $false
    | spl12_6
    | ~ spl12_10
    | ~ spl12_20 ),
    inference(subsumption_resolution,[],[f194,f658])).

fof(f658,plain,
    ( sP0(k5_relat_1(sK6,sK5))
    | ~ spl12_10
    | ~ spl12_20 ),
    inference(subsumption_resolution,[],[f553,f62])).

fof(f62,plain,(
    v2_funct_1(k5_relat_1(sK6,sK5)) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ( ~ v2_funct_1(sK5)
      | ~ v2_funct_1(sK6) )
    & k1_relat_1(sK5) = k2_relat_1(sK6)
    & v2_funct_1(k5_relat_1(sK6,sK5))
    & v1_funct_1(sK6)
    & v1_relat_1(sK6)
    & v1_funct_1(sK5)
    & v1_relat_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f13,f37,f36])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v2_funct_1(X0)
              | ~ v2_funct_1(X1) )
            & k1_relat_1(X0) = k2_relat_1(X1)
            & v2_funct_1(k5_relat_1(X1,X0))
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ( ~ v2_funct_1(sK5)
            | ~ v2_funct_1(X1) )
          & k2_relat_1(X1) = k1_relat_1(sK5)
          & v2_funct_1(k5_relat_1(X1,sK5))
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK5)
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X1] :
        ( ( ~ v2_funct_1(sK5)
          | ~ v2_funct_1(X1) )
        & k2_relat_1(X1) = k1_relat_1(sK5)
        & v2_funct_1(k5_relat_1(X1,sK5))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ( ~ v2_funct_1(sK5)
        | ~ v2_funct_1(sK6) )
      & k1_relat_1(sK5) = k2_relat_1(sK6)
      & v2_funct_1(k5_relat_1(sK6,sK5))
      & v1_funct_1(sK6)
      & v1_relat_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v2_funct_1(X0)
            | ~ v2_funct_1(X1) )
          & k1_relat_1(X0) = k2_relat_1(X1)
          & v2_funct_1(k5_relat_1(X1,X0))
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v2_funct_1(X0)
            | ~ v2_funct_1(X1) )
          & k1_relat_1(X0) = k2_relat_1(X1)
          & v2_funct_1(k5_relat_1(X1,X0))
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( k1_relat_1(X0) = k2_relat_1(X1)
                & v2_funct_1(k5_relat_1(X1,X0)) )
             => ( v2_funct_1(X0)
                & v2_funct_1(X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => ( v2_funct_1(X0)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).

fof(f553,plain,
    ( ~ v2_funct_1(k5_relat_1(sK6,sK5))
    | sP0(k5_relat_1(sK6,sK5))
    | ~ spl12_10
    | ~ spl12_20 ),
    inference(resolution,[],[f551,f66])).

fof(f66,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | ~ v2_funct_1(X0)
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ~ sP0(X0) )
        & ( sP0(X0)
          | ~ v2_funct_1(X0) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> sP0(X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f551,plain,
    ( sP1(k5_relat_1(sK6,sK5))
    | ~ spl12_10
    | ~ spl12_20 ),
    inference(subsumption_resolution,[],[f550,f301])).

fof(f301,plain,
    ( v1_relat_1(k5_relat_1(sK6,sK5))
    | ~ spl12_10 ),
    inference(avatar_component_clause,[],[f300])).

fof(f300,plain,
    ( spl12_10
  <=> v1_relat_1(k5_relat_1(sK6,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).

fof(f550,plain,
    ( sP1(k5_relat_1(sK6,sK5))
    | ~ v1_relat_1(k5_relat_1(sK6,sK5))
    | ~ spl12_20 ),
    inference(resolution,[],[f537,f73])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | sP1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f17,f29,f28])).

fof(f17,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

fof(f537,plain,
    ( v1_funct_1(k5_relat_1(sK6,sK5))
    | ~ spl12_20 ),
    inference(avatar_component_clause,[],[f536])).

fof(f536,plain,
    ( spl12_20
  <=> v1_funct_1(k5_relat_1(sK6,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_20])])).

fof(f194,plain,
    ( ~ sP0(k5_relat_1(sK6,sK5))
    | spl12_6 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl12_6
  <=> sP0(k5_relat_1(sK6,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).

fof(f654,plain,
    ( spl12_3
    | ~ spl12_6
    | ~ spl12_8
    | ~ spl12_12
    | spl12_23 ),
    inference(avatar_contradiction_clause,[],[f653])).

fof(f653,plain,
    ( $false
    | spl12_3
    | ~ spl12_6
    | ~ spl12_8
    | ~ spl12_12
    | spl12_23 ),
    inference(subsumption_resolution,[],[f652,f572])).

fof(f572,plain,
    ( sK7(sK5) != sK8(sK5)
    | spl12_23 ),
    inference(avatar_component_clause,[],[f570])).

fof(f652,plain,
    ( sK7(sK5) = sK8(sK5)
    | spl12_3
    | ~ spl12_6
    | ~ spl12_8
    | ~ spl12_12 ),
    inference(forward_demodulation,[],[f645,f227])).

fof(f227,plain,
    ( sK7(sK5) = k1_funct_1(sK6,sK11(sK6,sK7(sK5)))
    | spl12_3 ),
    inference(subsumption_resolution,[],[f226,f60])).

fof(f60,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f226,plain,
    ( ~ v1_relat_1(sK6)
    | sK7(sK5) = k1_funct_1(sK6,sK11(sK6,sK7(sK5)))
    | spl12_3 ),
    inference(subsumption_resolution,[],[f220,f61])).

fof(f61,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f220,plain,
    ( ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | sK7(sK5) = k1_funct_1(sK6,sK11(sK6,sK7(sK5)))
    | spl12_3 ),
    inference(resolution,[],[f206,f123])).

fof(f123,plain,
    ( r2_hidden(sK7(sK5),k2_relat_1(sK6))
    | spl12_3 ),
    inference(subsumption_resolution,[],[f122,f119])).

fof(f122,plain,
    ( r2_hidden(sK7(sK5),k2_relat_1(sK6))
    | sP0(sK5) ),
    inference(superposition,[],[f69,f63])).

fof(f63,plain,(
    k1_relat_1(sK5) = k2_relat_1(sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f69,plain,(
    ! [X0] :
      ( r2_hidden(sK7(X0),k1_relat_1(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f206,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,k2_relat_1(X4))
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | k1_funct_1(X4,sK11(X4,X3)) = X3 ) ),
    inference(resolution,[],[f204,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(X0,X1,X2)
      | k1_funct_1(X2,X1) = X0 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | k1_funct_1(X2,X1) != X0
        | ~ r2_hidden(X1,k1_relat_1(X2)) )
      & ( ( k1_funct_1(X2,X1) = X0
          & r2_hidden(X1,k1_relat_1(X2)) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(rectify,[],[f56])).

fof(f56,plain,(
    ! [X1,X0,X2] :
      ( ( sP3(X1,X0,X2)
        | k1_funct_1(X2,X0) != X1
        | ~ r2_hidden(X0,k1_relat_1(X2)) )
      & ( ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) )
        | ~ sP3(X1,X0,X2) ) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X1,X0,X2] :
      ( ( sP3(X1,X0,X2)
        | k1_funct_1(X2,X0) != X1
        | ~ r2_hidden(X0,k1_relat_1(X2)) )
      & ( ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) )
        | ~ sP3(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X1,X0,X2] :
      ( sP3(X1,X0,X2)
    <=> ( k1_funct_1(X2,X0) = X1
        & r2_hidden(X0,k1_relat_1(X2)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f204,plain,(
    ! [X0,X1] :
      ( sP3(X0,sK11(X1,X0),X1)
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f166,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( sP4(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( sP4(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_folding,[],[f27,f34,f33])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> sP3(X1,X0,X2) )
      | ~ sP4(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f166,plain,(
    ! [X0,X1] :
      ( ~ sP4(X1,sK11(X1,X0),X0)
      | sP3(X0,sK11(X1,X0),X1)
      | ~ r2_hidden(X0,k2_relat_1(X1)) ) ),
    inference(resolution,[],[f88,f157])).

fof(f157,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK11(X1,X0),X0),X1)
      | ~ r2_hidden(X0,k2_relat_1(X1)) ) ),
    inference(resolution,[],[f82,f96])).

fof(f96,plain,(
    ! [X0] : sP2(X0,k2_relat_1(X0)) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( sP2(X0,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ~ sP2(X0,X1) )
      & ( sP2(X0,X1)
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> sP2(X0,X1) ) ),
    inference(definition_folding,[],[f2,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( sP2(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f82,plain,(
    ! [X0,X5,X1] :
      ( ~ sP2(X0,X1)
      | ~ r2_hidden(X5,X1)
      | r2_hidden(k4_tarski(sK11(X0,X5),X5),X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK9(X0,X1)),X0)
            | ~ r2_hidden(sK9(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK10(X0,X1),sK9(X0,X1)),X0)
            | r2_hidden(sK9(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK11(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | ~ sP2(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f47,f50,f49,f48])).

fof(f48,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK9(X0,X1)),X0)
          | ~ r2_hidden(sK9(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK9(X0,X1)),X0)
          | r2_hidden(sK9(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK9(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK10(X0,X1),sK9(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK11(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
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
        | ~ sP2(X0,X1) ) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
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
        | ~ sP2(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),X0)
      | sP3(X2,X1,X0)
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X1,X2),X0)
          | ~ sP3(X2,X1,X0) )
        & ( sP3(X2,X1,X0)
          | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ sP4(X0,X1,X2) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ sP3(X1,X0,X2) )
        & ( sP3(X1,X0,X2)
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ sP4(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f645,plain,
    ( sK8(sK5) = k1_funct_1(sK6,sK11(sK6,sK7(sK5)))
    | spl12_3
    | ~ spl12_6
    | ~ spl12_8
    | ~ spl12_12 ),
    inference(backward_demodulation,[],[f229,f644])).

fof(f644,plain,
    ( sK11(sK6,sK7(sK5)) = sK11(sK6,sK8(sK5))
    | spl12_3
    | ~ spl12_6
    | ~ spl12_8
    | ~ spl12_12 ),
    inference(subsumption_resolution,[],[f643,f386])).

fof(f386,plain,
    ( r2_hidden(sK11(sK6,sK8(sK5)),k1_relat_1(sK6))
    | ~ spl12_12 ),
    inference(avatar_component_clause,[],[f385])).

fof(f385,plain,
    ( spl12_12
  <=> r2_hidden(sK11(sK6,sK8(sK5)),k1_relat_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_12])])).

fof(f643,plain,
    ( ~ r2_hidden(sK11(sK6,sK8(sK5)),k1_relat_1(sK6))
    | sK11(sK6,sK7(sK5)) = sK11(sK6,sK8(sK5))
    | spl12_3
    | ~ spl12_6
    | ~ spl12_8
    | ~ spl12_12 ),
    inference(trivial_inequality_removal,[],[f642])).

fof(f642,plain,
    ( k1_funct_1(sK5,sK7(sK5)) != k1_funct_1(sK5,sK7(sK5))
    | ~ r2_hidden(sK11(sK6,sK8(sK5)),k1_relat_1(sK6))
    | sK11(sK6,sK7(sK5)) = sK11(sK6,sK8(sK5))
    | spl12_3
    | ~ spl12_6
    | ~ spl12_8
    | ~ spl12_12 ),
    inference(superposition,[],[f507,f480])).

fof(f480,plain,
    ( k1_funct_1(sK5,sK7(sK5)) = k1_funct_1(k5_relat_1(sK6,sK5),sK11(sK6,sK8(sK5)))
    | spl12_3
    | ~ spl12_12 ),
    inference(forward_demodulation,[],[f479,f131])).

fof(f131,plain,
    ( k1_funct_1(sK5,sK7(sK5)) = k1_funct_1(sK5,sK8(sK5))
    | spl12_3 ),
    inference(resolution,[],[f71,f119])).

fof(f71,plain,(
    ! [X0] :
      ( sP0(X0)
      | k1_funct_1(X0,sK7(X0)) = k1_funct_1(X0,sK8(X0)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f479,plain,
    ( k1_funct_1(sK5,sK8(sK5)) = k1_funct_1(k5_relat_1(sK6,sK5),sK11(sK6,sK8(sK5)))
    | spl12_3
    | ~ spl12_12 ),
    inference(forward_demodulation,[],[f473,f229])).

fof(f473,plain,
    ( k1_funct_1(k5_relat_1(sK6,sK5),sK11(sK6,sK8(sK5))) = k1_funct_1(sK5,k1_funct_1(sK6,sK11(sK6,sK8(sK5))))
    | ~ spl12_12 ),
    inference(resolution,[],[f437,f386])).

fof(f437,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK6))
      | k1_funct_1(k5_relat_1(sK6,sK5),X0) = k1_funct_1(sK5,k1_funct_1(sK6,X0)) ) ),
    inference(subsumption_resolution,[],[f436,f58])).

fof(f58,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f38])).

fof(f436,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK6))
      | k1_funct_1(k5_relat_1(sK6,sK5),X0) = k1_funct_1(sK5,k1_funct_1(sK6,X0))
      | ~ v1_relat_1(sK5) ) ),
    inference(subsumption_resolution,[],[f435,f59])).

fof(f59,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f38])).

fof(f435,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK6))
      | k1_funct_1(k5_relat_1(sK6,sK5),X0) = k1_funct_1(sK5,k1_funct_1(sK6,X0))
      | ~ v1_funct_1(sK5)
      | ~ v1_relat_1(sK5) ) ),
    inference(subsumption_resolution,[],[f434,f60])).

fof(f434,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK6))
      | k1_funct_1(k5_relat_1(sK6,sK5),X0) = k1_funct_1(sK5,k1_funct_1(sK6,X0))
      | ~ v1_relat_1(sK6)
      | ~ v1_funct_1(sK5)
      | ~ v1_relat_1(sK5) ) ),
    inference(subsumption_resolution,[],[f431,f61])).

fof(f431,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK6))
      | k1_funct_1(k5_relat_1(sK6,sK5),X0) = k1_funct_1(sK5,k1_funct_1(sK6,X0))
      | ~ v1_funct_1(sK6)
      | ~ v1_relat_1(sK6)
      | ~ v1_funct_1(sK5)
      | ~ v1_relat_1(sK5) ) ),
    inference(superposition,[],[f77,f188])).

fof(f188,plain,(
    k1_relat_1(sK6) = k1_relat_1(k5_relat_1(sK6,sK5)) ),
    inference(subsumption_resolution,[],[f187,f60])).

fof(f187,plain,
    ( k1_relat_1(sK6) = k1_relat_1(k5_relat_1(sK6,sK5))
    | ~ v1_relat_1(sK6) ),
    inference(resolution,[],[f186,f94])).

fof(f94,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f186,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(X0),k2_relat_1(sK6))
      | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,sK5))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f185,f58])).

fof(f185,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(X0),k2_relat_1(sK6))
      | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,sK5))
      | ~ v1_relat_1(sK5)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f65,f63])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
           => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).

fof(f507,plain,
    ( ! [X0] :
        ( k1_funct_1(sK5,sK7(sK5)) != k1_funct_1(k5_relat_1(sK6,sK5),X0)
        | ~ r2_hidden(X0,k1_relat_1(sK6))
        | sK11(sK6,sK7(sK5)) = X0 )
    | spl12_3
    | ~ spl12_6
    | ~ spl12_8 ),
    inference(forward_demodulation,[],[f506,f188])).

fof(f506,plain,
    ( ! [X0] :
        ( k1_funct_1(sK5,sK7(sK5)) != k1_funct_1(k5_relat_1(sK6,sK5),X0)
        | sK11(sK6,sK7(sK5)) = X0
        | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK6,sK5))) )
    | spl12_3
    | ~ spl12_6
    | ~ spl12_8 ),
    inference(subsumption_resolution,[],[f505,f251])).

fof(f251,plain,
    ( r2_hidden(sK11(sK6,sK7(sK5)),k1_relat_1(sK6))
    | ~ spl12_8 ),
    inference(avatar_component_clause,[],[f250])).

fof(f250,plain,
    ( spl12_8
  <=> r2_hidden(sK11(sK6,sK7(sK5)),k1_relat_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).

fof(f505,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK11(sK6,sK7(sK5)),k1_relat_1(sK6))
        | k1_funct_1(sK5,sK7(sK5)) != k1_funct_1(k5_relat_1(sK6,sK5),X0)
        | sK11(sK6,sK7(sK5)) = X0
        | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK6,sK5))) )
    | spl12_3
    | ~ spl12_6
    | ~ spl12_8 ),
    inference(forward_demodulation,[],[f504,f188])).

fof(f504,plain,
    ( ! [X0] :
        ( k1_funct_1(sK5,sK7(sK5)) != k1_funct_1(k5_relat_1(sK6,sK5),X0)
        | sK11(sK6,sK7(sK5)) = X0
        | ~ r2_hidden(sK11(sK6,sK7(sK5)),k1_relat_1(k5_relat_1(sK6,sK5)))
        | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK6,sK5))) )
    | spl12_3
    | ~ spl12_6
    | ~ spl12_8 ),
    inference(subsumption_resolution,[],[f500,f195])).

fof(f195,plain,
    ( sP0(k5_relat_1(sK6,sK5))
    | ~ spl12_6 ),
    inference(avatar_component_clause,[],[f193])).

fof(f500,plain,
    ( ! [X0] :
        ( k1_funct_1(sK5,sK7(sK5)) != k1_funct_1(k5_relat_1(sK6,sK5),X0)
        | sK11(sK6,sK7(sK5)) = X0
        | ~ r2_hidden(sK11(sK6,sK7(sK5)),k1_relat_1(k5_relat_1(sK6,sK5)))
        | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK6,sK5)))
        | ~ sP0(k5_relat_1(sK6,sK5)) )
    | spl12_3
    | ~ spl12_8 ),
    inference(superposition,[],[f68,f478])).

fof(f478,plain,
    ( k1_funct_1(sK5,sK7(sK5)) = k1_funct_1(k5_relat_1(sK6,sK5),sK11(sK6,sK7(sK5)))
    | spl12_3
    | ~ spl12_8 ),
    inference(forward_demodulation,[],[f472,f227])).

fof(f472,plain,
    ( k1_funct_1(k5_relat_1(sK6,sK5),sK11(sK6,sK7(sK5))) = k1_funct_1(sK5,k1_funct_1(sK6,sK11(sK6,sK7(sK5))))
    | ~ spl12_8 ),
    inference(resolution,[],[f437,f251])).

fof(f68,plain,(
    ! [X4,X0,X3] :
      ( k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | X3 = X4
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f229,plain,
    ( sK8(sK5) = k1_funct_1(sK6,sK11(sK6,sK8(sK5)))
    | spl12_3 ),
    inference(subsumption_resolution,[],[f228,f60])).

fof(f228,plain,
    ( ~ v1_relat_1(sK6)
    | sK8(sK5) = k1_funct_1(sK6,sK11(sK6,sK8(sK5)))
    | spl12_3 ),
    inference(subsumption_resolution,[],[f222,f61])).

fof(f222,plain,
    ( ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | sK8(sK5) = k1_funct_1(sK6,sK11(sK6,sK8(sK5)))
    | spl12_3 ),
    inference(resolution,[],[f206,f125])).

fof(f125,plain,
    ( r2_hidden(sK8(sK5),k2_relat_1(sK6))
    | spl12_3 ),
    inference(subsumption_resolution,[],[f124,f119])).

fof(f124,plain,
    ( r2_hidden(sK8(sK5),k2_relat_1(sK6))
    | sP0(sK5) ),
    inference(superposition,[],[f70,f63])).

fof(f70,plain,(
    ! [X0] :
      ( r2_hidden(sK8(X0),k1_relat_1(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f548,plain,(
    spl12_20 ),
    inference(avatar_contradiction_clause,[],[f547])).

fof(f547,plain,
    ( $false
    | spl12_20 ),
    inference(subsumption_resolution,[],[f546,f60])).

fof(f546,plain,
    ( ~ v1_relat_1(sK6)
    | spl12_20 ),
    inference(subsumption_resolution,[],[f545,f61])).

fof(f545,plain,
    ( ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | spl12_20 ),
    inference(subsumption_resolution,[],[f544,f58])).

fof(f544,plain,
    ( ~ v1_relat_1(sK5)
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | spl12_20 ),
    inference(subsumption_resolution,[],[f543,f59])).

fof(f543,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | spl12_20 ),
    inference(resolution,[],[f538,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funct_1)).

fof(f538,plain,
    ( ~ v1_funct_1(k5_relat_1(sK6,sK5))
    | spl12_20 ),
    inference(avatar_component_clause,[],[f536])).

fof(f397,plain,(
    spl12_12 ),
    inference(avatar_contradiction_clause,[],[f396])).

fof(f396,plain,
    ( $false
    | spl12_12 ),
    inference(subsumption_resolution,[],[f395,f332])).

fof(f332,plain,(
    r2_hidden(sK8(sK5),k2_relat_1(sK6)) ),
    inference(global_subsumption,[],[f64,f111,f330,f124])).

fof(f330,plain,(
    v2_funct_1(sK6) ),
    inference(subsumption_resolution,[],[f329,f60])).

fof(f329,plain,
    ( v2_funct_1(sK6)
    | ~ v1_relat_1(sK6) ),
    inference(subsumption_resolution,[],[f328,f61])).

fof(f328,plain,
    ( v2_funct_1(sK6)
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6) ),
    inference(subsumption_resolution,[],[f322,f62])).

fof(f322,plain,
    ( v2_funct_1(sK6)
    | ~ v2_funct_1(k5_relat_1(sK6,sK5))
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6) ),
    inference(resolution,[],[f320,f94])).

fof(f320,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(X0),k2_relat_1(sK6))
      | v2_funct_1(X0)
      | ~ v2_funct_1(k5_relat_1(X0,sK5))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f319,f58])).

fof(f319,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(X0),k2_relat_1(sK6))
      | v2_funct_1(X0)
      | ~ v2_funct_1(k5_relat_1(X0,sK5))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK5) ) ),
    inference(subsumption_resolution,[],[f317,f59])).

fof(f317,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(X0),k2_relat_1(sK6))
      | v2_funct_1(X0)
      | ~ v2_funct_1(k5_relat_1(X0,sK5))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(sK5)
      | ~ v1_relat_1(sK5) ) ),
    inference(superposition,[],[f74,f63])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
      | v2_funct_1(X1)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(X1)
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(X1)
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => v2_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_funct_1)).

fof(f111,plain,
    ( ~ sP0(sK5)
    | v2_funct_1(sK5) ),
    inference(resolution,[],[f109,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | ~ sP0(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f109,plain,(
    sP1(sK5) ),
    inference(subsumption_resolution,[],[f107,f58])).

fof(f107,plain,
    ( sP1(sK5)
    | ~ v1_relat_1(sK5) ),
    inference(resolution,[],[f73,f59])).

fof(f64,plain,
    ( ~ v2_funct_1(sK5)
    | ~ v2_funct_1(sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f395,plain,
    ( ~ r2_hidden(sK8(sK5),k2_relat_1(sK6))
    | spl12_12 ),
    inference(subsumption_resolution,[],[f394,f60])).

fof(f394,plain,
    ( ~ v1_relat_1(sK6)
    | ~ r2_hidden(sK8(sK5),k2_relat_1(sK6))
    | spl12_12 ),
    inference(subsumption_resolution,[],[f393,f61])).

fof(f393,plain,
    ( ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | ~ r2_hidden(sK8(sK5),k2_relat_1(sK6))
    | spl12_12 ),
    inference(resolution,[],[f387,f207])).

fof(f207,plain,(
    ! [X6,X5] :
      ( r2_hidden(sK11(X6,X5),k1_relat_1(X6))
      | ~ v1_funct_1(X6)
      | ~ v1_relat_1(X6)
      | ~ r2_hidden(X5,k2_relat_1(X6)) ) ),
    inference(resolution,[],[f204,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(X0,X1,X2)
      | r2_hidden(X1,k1_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f387,plain,
    ( ~ r2_hidden(sK11(sK6,sK8(sK5)),k1_relat_1(sK6))
    | spl12_12 ),
    inference(avatar_component_clause,[],[f385])).

fof(f327,plain,(
    spl12_1 ),
    inference(avatar_contradiction_clause,[],[f326])).

fof(f326,plain,
    ( $false
    | spl12_1 ),
    inference(subsumption_resolution,[],[f325,f60])).

fof(f325,plain,
    ( ~ v1_relat_1(sK6)
    | spl12_1 ),
    inference(subsumption_resolution,[],[f324,f61])).

fof(f324,plain,
    ( ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | spl12_1 ),
    inference(subsumption_resolution,[],[f323,f62])).

fof(f323,plain,
    ( ~ v2_funct_1(k5_relat_1(sK6,sK5))
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | spl12_1 ),
    inference(subsumption_resolution,[],[f322,f101])).

fof(f101,plain,
    ( ~ v2_funct_1(sK6)
    | spl12_1 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl12_1
  <=> v2_funct_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f316,plain,(
    spl12_10 ),
    inference(avatar_contradiction_clause,[],[f315])).

fof(f315,plain,
    ( $false
    | spl12_10 ),
    inference(subsumption_resolution,[],[f314,f60])).

fof(f314,plain,
    ( ~ v1_relat_1(sK6)
    | spl12_10 ),
    inference(subsumption_resolution,[],[f308,f58])).

fof(f308,plain,
    ( ~ v1_relat_1(sK5)
    | ~ v1_relat_1(sK6)
    | spl12_10 ),
    inference(resolution,[],[f302,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f302,plain,
    ( ~ v1_relat_1(k5_relat_1(sK6,sK5))
    | spl12_10 ),
    inference(avatar_component_clause,[],[f300])).

fof(f262,plain,
    ( spl12_3
    | spl12_8 ),
    inference(avatar_contradiction_clause,[],[f261])).

fof(f261,plain,
    ( $false
    | spl12_3
    | spl12_8 ),
    inference(subsumption_resolution,[],[f260,f123])).

fof(f260,plain,
    ( ~ r2_hidden(sK7(sK5),k2_relat_1(sK6))
    | spl12_8 ),
    inference(subsumption_resolution,[],[f259,f60])).

fof(f259,plain,
    ( ~ v1_relat_1(sK6)
    | ~ r2_hidden(sK7(sK5),k2_relat_1(sK6))
    | spl12_8 ),
    inference(subsumption_resolution,[],[f258,f61])).

fof(f258,plain,
    ( ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | ~ r2_hidden(sK7(sK5),k2_relat_1(sK6))
    | spl12_8 ),
    inference(resolution,[],[f252,f207])).

fof(f252,plain,
    ( ~ r2_hidden(sK11(sK6,sK7(sK5)),k1_relat_1(sK6))
    | spl12_8 ),
    inference(avatar_component_clause,[],[f250])).

fof(f120,plain,
    ( spl12_2
    | ~ spl12_3 ),
    inference(avatar_split_clause,[],[f111,f117,f103])).

fof(f103,plain,
    ( spl12_2
  <=> v2_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f106,plain,
    ( ~ spl12_1
    | ~ spl12_2 ),
    inference(avatar_split_clause,[],[f64,f103,f99])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:40:09 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.20/0.49  % (2299)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.50  % (2314)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.50  % (2306)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.50  % (2301)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.50  % (2294)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.51  % (2322)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.51  % (2315)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.51  % (2312)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (2313)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.51  % (2297)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.52  % (2323)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.23/0.52  % (2296)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.23/0.52  % (2317)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.23/0.52  % (2320)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.23/0.52  % (2318)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.23/0.52  % (2324)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.23/0.52  % (2311)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.23/0.52  % (2307)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.23/0.53  % (2316)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.23/0.53  % (2298)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.34/0.54  % (2308)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.34/0.54  % (2310)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.34/0.54  % (2321)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.34/0.55  % (2295)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.34/0.55  % (2309)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.34/0.55  % (2319)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.34/0.57  % (2324)Refutation found. Thanks to Tanya!
% 1.34/0.57  % SZS status Theorem for theBenchmark
% 1.34/0.57  % SZS output start Proof for theBenchmark
% 1.34/0.57  fof(f705,plain,(
% 1.34/0.57    $false),
% 1.34/0.57    inference(avatar_sat_refutation,[],[f106,f120,f262,f316,f327,f397,f548,f654,f676,f704])).
% 1.34/0.57  fof(f704,plain,(
% 1.34/0.57    spl12_3 | ~spl12_23),
% 1.34/0.57    inference(avatar_contradiction_clause,[],[f703])).
% 1.34/0.57  fof(f703,plain,(
% 1.34/0.57    $false | (spl12_3 | ~spl12_23)),
% 1.34/0.57    inference(subsumption_resolution,[],[f702,f119])).
% 1.34/0.57  fof(f119,plain,(
% 1.34/0.57    ~sP0(sK5) | spl12_3),
% 1.34/0.57    inference(avatar_component_clause,[],[f117])).
% 1.34/0.57  fof(f117,plain,(
% 1.34/0.57    spl12_3 <=> sP0(sK5)),
% 1.34/0.57    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).
% 1.34/0.57  fof(f702,plain,(
% 1.34/0.57    sP0(sK5) | ~spl12_23),
% 1.34/0.57    inference(trivial_inequality_removal,[],[f700])).
% 1.34/0.57  fof(f700,plain,(
% 1.34/0.57    sK7(sK5) != sK7(sK5) | sP0(sK5) | ~spl12_23),
% 1.34/0.57    inference(superposition,[],[f72,f571])).
% 1.34/0.57  fof(f571,plain,(
% 1.34/0.57    sK7(sK5) = sK8(sK5) | ~spl12_23),
% 1.34/0.57    inference(avatar_component_clause,[],[f570])).
% 1.34/0.57  fof(f570,plain,(
% 1.34/0.57    spl12_23 <=> sK7(sK5) = sK8(sK5)),
% 1.34/0.57    introduced(avatar_definition,[new_symbols(naming,[spl12_23])])).
% 1.34/0.57  fof(f72,plain,(
% 1.34/0.57    ( ! [X0] : (sK7(X0) != sK8(X0) | sP0(X0)) )),
% 1.34/0.57    inference(cnf_transformation,[],[f43])).
% 1.34/0.57  fof(f43,plain,(
% 1.34/0.57    ! [X0] : ((sP0(X0) | (sK7(X0) != sK8(X0) & k1_funct_1(X0,sK7(X0)) = k1_funct_1(X0,sK8(X0)) & r2_hidden(sK8(X0),k1_relat_1(X0)) & r2_hidden(sK7(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X0)))),
% 1.34/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f41,f42])).
% 1.34/0.57  fof(f42,plain,(
% 1.34/0.57    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK7(X0) != sK8(X0) & k1_funct_1(X0,sK7(X0)) = k1_funct_1(X0,sK8(X0)) & r2_hidden(sK8(X0),k1_relat_1(X0)) & r2_hidden(sK7(X0),k1_relat_1(X0))))),
% 1.34/0.57    introduced(choice_axiom,[])).
% 1.34/0.57  fof(f41,plain,(
% 1.34/0.57    ! [X0] : ((sP0(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X0)))),
% 1.34/0.57    inference(rectify,[],[f40])).
% 1.34/0.57  fof(f40,plain,(
% 1.34/0.57    ! [X0] : ((sP0(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~sP0(X0)))),
% 1.34/0.57    inference(nnf_transformation,[],[f28])).
% 1.34/0.57  fof(f28,plain,(
% 1.34/0.57    ! [X0] : (sP0(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))),
% 1.34/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.34/0.57  fof(f676,plain,(
% 1.34/0.57    spl12_6 | ~spl12_10 | ~spl12_20),
% 1.34/0.57    inference(avatar_contradiction_clause,[],[f675])).
% 1.34/0.57  fof(f675,plain,(
% 1.34/0.57    $false | (spl12_6 | ~spl12_10 | ~spl12_20)),
% 1.34/0.57    inference(subsumption_resolution,[],[f194,f658])).
% 1.34/0.57  fof(f658,plain,(
% 1.34/0.57    sP0(k5_relat_1(sK6,sK5)) | (~spl12_10 | ~spl12_20)),
% 1.34/0.57    inference(subsumption_resolution,[],[f553,f62])).
% 1.34/0.57  fof(f62,plain,(
% 1.34/0.57    v2_funct_1(k5_relat_1(sK6,sK5))),
% 1.34/0.57    inference(cnf_transformation,[],[f38])).
% 1.34/0.57  fof(f38,plain,(
% 1.34/0.57    ((~v2_funct_1(sK5) | ~v2_funct_1(sK6)) & k1_relat_1(sK5) = k2_relat_1(sK6) & v2_funct_1(k5_relat_1(sK6,sK5)) & v1_funct_1(sK6) & v1_relat_1(sK6)) & v1_funct_1(sK5) & v1_relat_1(sK5)),
% 1.34/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f13,f37,f36])).
% 1.34/0.57  fof(f36,plain,(
% 1.34/0.57    ? [X0] : (? [X1] : ((~v2_funct_1(X0) | ~v2_funct_1(X1)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(k5_relat_1(X1,X0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : ((~v2_funct_1(sK5) | ~v2_funct_1(X1)) & k2_relat_1(X1) = k1_relat_1(sK5) & v2_funct_1(k5_relat_1(X1,sK5)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK5) & v1_relat_1(sK5))),
% 1.34/0.57    introduced(choice_axiom,[])).
% 1.34/0.57  fof(f37,plain,(
% 1.34/0.57    ? [X1] : ((~v2_funct_1(sK5) | ~v2_funct_1(X1)) & k2_relat_1(X1) = k1_relat_1(sK5) & v2_funct_1(k5_relat_1(X1,sK5)) & v1_funct_1(X1) & v1_relat_1(X1)) => ((~v2_funct_1(sK5) | ~v2_funct_1(sK6)) & k1_relat_1(sK5) = k2_relat_1(sK6) & v2_funct_1(k5_relat_1(sK6,sK5)) & v1_funct_1(sK6) & v1_relat_1(sK6))),
% 1.34/0.57    introduced(choice_axiom,[])).
% 1.34/0.57  fof(f13,plain,(
% 1.34/0.57    ? [X0] : (? [X1] : ((~v2_funct_1(X0) | ~v2_funct_1(X1)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(k5_relat_1(X1,X0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.34/0.57    inference(flattening,[],[f12])).
% 1.34/0.57  fof(f12,plain,(
% 1.34/0.57    ? [X0] : (? [X1] : (((~v2_funct_1(X0) | ~v2_funct_1(X1)) & (k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(k5_relat_1(X1,X0)))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.34/0.57    inference(ennf_transformation,[],[f11])).
% 1.34/0.57  fof(f11,negated_conjecture,(
% 1.34/0.57    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 1.34/0.57    inference(negated_conjecture,[],[f10])).
% 1.34/0.57  fof(f10,conjecture,(
% 1.34/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 1.34/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).
% 1.34/0.57  fof(f553,plain,(
% 1.34/0.57    ~v2_funct_1(k5_relat_1(sK6,sK5)) | sP0(k5_relat_1(sK6,sK5)) | (~spl12_10 | ~spl12_20)),
% 1.34/0.57    inference(resolution,[],[f551,f66])).
% 1.34/0.57  fof(f66,plain,(
% 1.34/0.57    ( ! [X0] : (~sP1(X0) | ~v2_funct_1(X0) | sP0(X0)) )),
% 1.34/0.57    inference(cnf_transformation,[],[f39])).
% 1.34/0.57  fof(f39,plain,(
% 1.34/0.57    ! [X0] : (((v2_funct_1(X0) | ~sP0(X0)) & (sP0(X0) | ~v2_funct_1(X0))) | ~sP1(X0))),
% 1.34/0.57    inference(nnf_transformation,[],[f29])).
% 1.34/0.57  fof(f29,plain,(
% 1.34/0.57    ! [X0] : ((v2_funct_1(X0) <=> sP0(X0)) | ~sP1(X0))),
% 1.34/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.34/0.57  fof(f551,plain,(
% 1.34/0.57    sP1(k5_relat_1(sK6,sK5)) | (~spl12_10 | ~spl12_20)),
% 1.34/0.57    inference(subsumption_resolution,[],[f550,f301])).
% 1.34/0.57  fof(f301,plain,(
% 1.34/0.57    v1_relat_1(k5_relat_1(sK6,sK5)) | ~spl12_10),
% 1.34/0.57    inference(avatar_component_clause,[],[f300])).
% 1.34/0.57  fof(f300,plain,(
% 1.34/0.57    spl12_10 <=> v1_relat_1(k5_relat_1(sK6,sK5))),
% 1.34/0.57    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).
% 1.34/0.57  fof(f550,plain,(
% 1.34/0.57    sP1(k5_relat_1(sK6,sK5)) | ~v1_relat_1(k5_relat_1(sK6,sK5)) | ~spl12_20),
% 1.34/0.57    inference(resolution,[],[f537,f73])).
% 1.34/0.57  fof(f73,plain,(
% 1.34/0.57    ( ! [X0] : (~v1_funct_1(X0) | sP1(X0) | ~v1_relat_1(X0)) )),
% 1.34/0.57    inference(cnf_transformation,[],[f30])).
% 1.34/0.57  fof(f30,plain,(
% 1.34/0.57    ! [X0] : (sP1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.34/0.57    inference(definition_folding,[],[f17,f29,f28])).
% 1.34/0.57  fof(f17,plain,(
% 1.34/0.57    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.34/0.57    inference(flattening,[],[f16])).
% 1.34/0.57  fof(f16,plain,(
% 1.34/0.57    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.34/0.57    inference(ennf_transformation,[],[f5])).
% 1.34/0.57  fof(f5,axiom,(
% 1.34/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 1.34/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).
% 1.34/0.57  fof(f537,plain,(
% 1.34/0.57    v1_funct_1(k5_relat_1(sK6,sK5)) | ~spl12_20),
% 1.34/0.57    inference(avatar_component_clause,[],[f536])).
% 1.34/0.57  fof(f536,plain,(
% 1.34/0.57    spl12_20 <=> v1_funct_1(k5_relat_1(sK6,sK5))),
% 1.34/0.57    introduced(avatar_definition,[new_symbols(naming,[spl12_20])])).
% 1.34/0.57  fof(f194,plain,(
% 1.34/0.57    ~sP0(k5_relat_1(sK6,sK5)) | spl12_6),
% 1.34/0.57    inference(avatar_component_clause,[],[f193])).
% 1.34/0.57  fof(f193,plain,(
% 1.34/0.57    spl12_6 <=> sP0(k5_relat_1(sK6,sK5))),
% 1.34/0.57    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).
% 1.34/0.57  fof(f654,plain,(
% 1.34/0.57    spl12_3 | ~spl12_6 | ~spl12_8 | ~spl12_12 | spl12_23),
% 1.34/0.57    inference(avatar_contradiction_clause,[],[f653])).
% 1.34/0.57  fof(f653,plain,(
% 1.34/0.57    $false | (spl12_3 | ~spl12_6 | ~spl12_8 | ~spl12_12 | spl12_23)),
% 1.34/0.57    inference(subsumption_resolution,[],[f652,f572])).
% 1.34/0.57  fof(f572,plain,(
% 1.34/0.57    sK7(sK5) != sK8(sK5) | spl12_23),
% 1.34/0.57    inference(avatar_component_clause,[],[f570])).
% 1.34/0.57  fof(f652,plain,(
% 1.34/0.57    sK7(sK5) = sK8(sK5) | (spl12_3 | ~spl12_6 | ~spl12_8 | ~spl12_12)),
% 1.34/0.57    inference(forward_demodulation,[],[f645,f227])).
% 1.34/0.57  fof(f227,plain,(
% 1.34/0.57    sK7(sK5) = k1_funct_1(sK6,sK11(sK6,sK7(sK5))) | spl12_3),
% 1.34/0.57    inference(subsumption_resolution,[],[f226,f60])).
% 1.34/0.57  fof(f60,plain,(
% 1.34/0.57    v1_relat_1(sK6)),
% 1.34/0.57    inference(cnf_transformation,[],[f38])).
% 1.34/0.57  fof(f226,plain,(
% 1.34/0.57    ~v1_relat_1(sK6) | sK7(sK5) = k1_funct_1(sK6,sK11(sK6,sK7(sK5))) | spl12_3),
% 1.34/0.57    inference(subsumption_resolution,[],[f220,f61])).
% 1.34/0.57  fof(f61,plain,(
% 1.34/0.57    v1_funct_1(sK6)),
% 1.34/0.57    inference(cnf_transformation,[],[f38])).
% 1.34/0.57  fof(f220,plain,(
% 1.34/0.57    ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | sK7(sK5) = k1_funct_1(sK6,sK11(sK6,sK7(sK5))) | spl12_3),
% 1.34/0.57    inference(resolution,[],[f206,f123])).
% 1.34/0.57  fof(f123,plain,(
% 1.34/0.57    r2_hidden(sK7(sK5),k2_relat_1(sK6)) | spl12_3),
% 1.34/0.57    inference(subsumption_resolution,[],[f122,f119])).
% 1.34/0.57  fof(f122,plain,(
% 1.34/0.57    r2_hidden(sK7(sK5),k2_relat_1(sK6)) | sP0(sK5)),
% 1.34/0.57    inference(superposition,[],[f69,f63])).
% 1.34/0.57  fof(f63,plain,(
% 1.34/0.57    k1_relat_1(sK5) = k2_relat_1(sK6)),
% 1.34/0.57    inference(cnf_transformation,[],[f38])).
% 1.34/0.57  fof(f69,plain,(
% 1.34/0.57    ( ! [X0] : (r2_hidden(sK7(X0),k1_relat_1(X0)) | sP0(X0)) )),
% 1.34/0.57    inference(cnf_transformation,[],[f43])).
% 1.34/0.57  fof(f206,plain,(
% 1.34/0.57    ( ! [X4,X3] : (~r2_hidden(X3,k2_relat_1(X4)) | ~v1_funct_1(X4) | ~v1_relat_1(X4) | k1_funct_1(X4,sK11(X4,X3)) = X3) )),
% 1.34/0.57    inference(resolution,[],[f204,f91])).
% 1.34/0.57  fof(f91,plain,(
% 1.34/0.57    ( ! [X2,X0,X1] : (~sP3(X0,X1,X2) | k1_funct_1(X2,X1) = X0) )),
% 1.34/0.57    inference(cnf_transformation,[],[f57])).
% 1.34/0.57  fof(f57,plain,(
% 1.34/0.57    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | k1_funct_1(X2,X1) != X0 | ~r2_hidden(X1,k1_relat_1(X2))) & ((k1_funct_1(X2,X1) = X0 & r2_hidden(X1,k1_relat_1(X2))) | ~sP3(X0,X1,X2)))),
% 1.34/0.57    inference(rectify,[],[f56])).
% 1.34/0.57  fof(f56,plain,(
% 1.34/0.57    ! [X1,X0,X2] : ((sP3(X1,X0,X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~sP3(X1,X0,X2)))),
% 1.34/0.57    inference(flattening,[],[f55])).
% 1.34/0.57  fof(f55,plain,(
% 1.34/0.57    ! [X1,X0,X2] : ((sP3(X1,X0,X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~sP3(X1,X0,X2)))),
% 1.34/0.57    inference(nnf_transformation,[],[f33])).
% 1.34/0.57  fof(f33,plain,(
% 1.34/0.57    ! [X1,X0,X2] : (sP3(X1,X0,X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))))),
% 1.34/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 1.34/0.57  fof(f204,plain,(
% 1.34/0.57    ( ! [X0,X1] : (sP3(X0,sK11(X1,X0),X1) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.34/0.57    inference(resolution,[],[f166,f93])).
% 1.34/0.57  fof(f93,plain,(
% 1.34/0.57    ( ! [X2,X0,X1] : (sP4(X2,X0,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.34/0.57    inference(cnf_transformation,[],[f35])).
% 1.34/0.57  fof(f35,plain,(
% 1.34/0.57    ! [X0,X1,X2] : (sP4(X2,X0,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.34/0.57    inference(definition_folding,[],[f27,f34,f33])).
% 1.34/0.57  fof(f34,plain,(
% 1.34/0.57    ! [X2,X0,X1] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> sP3(X1,X0,X2)) | ~sP4(X2,X0,X1))),
% 1.34/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 1.34/0.57  fof(f27,plain,(
% 1.34/0.57    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.34/0.57    inference(flattening,[],[f26])).
% 1.34/0.57  fof(f26,plain,(
% 1.34/0.57    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.34/0.57    inference(ennf_transformation,[],[f9])).
% 1.34/0.57  fof(f9,axiom,(
% 1.34/0.57    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.34/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 1.34/0.57  fof(f166,plain,(
% 1.34/0.57    ( ! [X0,X1] : (~sP4(X1,sK11(X1,X0),X0) | sP3(X0,sK11(X1,X0),X1) | ~r2_hidden(X0,k2_relat_1(X1))) )),
% 1.34/0.57    inference(resolution,[],[f88,f157])).
% 1.34/0.57  fof(f157,plain,(
% 1.34/0.57    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK11(X1,X0),X0),X1) | ~r2_hidden(X0,k2_relat_1(X1))) )),
% 1.34/0.57    inference(resolution,[],[f82,f96])).
% 1.34/0.57  fof(f96,plain,(
% 1.34/0.57    ( ! [X0] : (sP2(X0,k2_relat_1(X0))) )),
% 1.34/0.57    inference(equality_resolution,[],[f86])).
% 1.34/0.57  fof(f86,plain,(
% 1.34/0.57    ( ! [X0,X1] : (sP2(X0,X1) | k2_relat_1(X0) != X1) )),
% 1.34/0.57    inference(cnf_transformation,[],[f52])).
% 1.34/0.57  fof(f52,plain,(
% 1.34/0.57    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ~sP2(X0,X1)) & (sP2(X0,X1) | k2_relat_1(X0) != X1))),
% 1.34/0.57    inference(nnf_transformation,[],[f32])).
% 1.34/0.57  fof(f32,plain,(
% 1.34/0.57    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> sP2(X0,X1))),
% 1.34/0.57    inference(definition_folding,[],[f2,f31])).
% 1.34/0.57  fof(f31,plain,(
% 1.34/0.57    ! [X0,X1] : (sP2(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 1.34/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.34/0.57  fof(f2,axiom,(
% 1.34/0.57    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 1.34/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 1.34/0.57  fof(f82,plain,(
% 1.34/0.57    ( ! [X0,X5,X1] : (~sP2(X0,X1) | ~r2_hidden(X5,X1) | r2_hidden(k4_tarski(sK11(X0,X5),X5),X0)) )),
% 1.34/0.57    inference(cnf_transformation,[],[f51])).
% 1.34/0.57  fof(f51,plain,(
% 1.34/0.57    ! [X0,X1] : ((sP2(X0,X1) | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK9(X0,X1)),X0) | ~r2_hidden(sK9(X0,X1),X1)) & (r2_hidden(k4_tarski(sK10(X0,X1),sK9(X0,X1)),X0) | r2_hidden(sK9(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK11(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | ~sP2(X0,X1)))),
% 1.34/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f47,f50,f49,f48])).
% 1.34/0.57  fof(f48,plain,(
% 1.34/0.57    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK9(X0,X1)),X0) | ~r2_hidden(sK9(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK9(X0,X1)),X0) | r2_hidden(sK9(X0,X1),X1))))),
% 1.34/0.57    introduced(choice_axiom,[])).
% 1.34/0.57  fof(f49,plain,(
% 1.34/0.57    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK9(X0,X1)),X0) => r2_hidden(k4_tarski(sK10(X0,X1),sK9(X0,X1)),X0))),
% 1.34/0.57    introduced(choice_axiom,[])).
% 1.34/0.57  fof(f50,plain,(
% 1.34/0.57    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK11(X0,X5),X5),X0))),
% 1.34/0.57    introduced(choice_axiom,[])).
% 1.34/0.57  fof(f47,plain,(
% 1.34/0.57    ! [X0,X1] : ((sP2(X0,X1) | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | ~sP2(X0,X1)))),
% 1.34/0.57    inference(rectify,[],[f46])).
% 1.34/0.57  fof(f46,plain,(
% 1.34/0.57    ! [X0,X1] : ((sP2(X0,X1) | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | ~sP2(X0,X1)))),
% 1.34/0.57    inference(nnf_transformation,[],[f31])).
% 1.34/0.57  fof(f88,plain,(
% 1.34/0.57    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X1,X2),X0) | sP3(X2,X1,X0) | ~sP4(X0,X1,X2)) )),
% 1.34/0.57    inference(cnf_transformation,[],[f54])).
% 1.34/0.57  fof(f54,plain,(
% 1.34/0.57    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X1,X2),X0) | ~sP3(X2,X1,X0)) & (sP3(X2,X1,X0) | ~r2_hidden(k4_tarski(X1,X2),X0))) | ~sP4(X0,X1,X2))),
% 1.34/0.57    inference(rectify,[],[f53])).
% 1.34/0.57  fof(f53,plain,(
% 1.34/0.57    ! [X2,X0,X1] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~sP3(X1,X0,X2)) & (sP3(X1,X0,X2) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~sP4(X2,X0,X1))),
% 1.34/0.57    inference(nnf_transformation,[],[f34])).
% 1.34/0.57  fof(f645,plain,(
% 1.34/0.57    sK8(sK5) = k1_funct_1(sK6,sK11(sK6,sK7(sK5))) | (spl12_3 | ~spl12_6 | ~spl12_8 | ~spl12_12)),
% 1.34/0.57    inference(backward_demodulation,[],[f229,f644])).
% 1.34/0.57  fof(f644,plain,(
% 1.34/0.57    sK11(sK6,sK7(sK5)) = sK11(sK6,sK8(sK5)) | (spl12_3 | ~spl12_6 | ~spl12_8 | ~spl12_12)),
% 1.34/0.57    inference(subsumption_resolution,[],[f643,f386])).
% 1.34/0.57  fof(f386,plain,(
% 1.34/0.57    r2_hidden(sK11(sK6,sK8(sK5)),k1_relat_1(sK6)) | ~spl12_12),
% 1.34/0.57    inference(avatar_component_clause,[],[f385])).
% 1.34/0.57  fof(f385,plain,(
% 1.34/0.57    spl12_12 <=> r2_hidden(sK11(sK6,sK8(sK5)),k1_relat_1(sK6))),
% 1.34/0.57    introduced(avatar_definition,[new_symbols(naming,[spl12_12])])).
% 1.34/0.57  fof(f643,plain,(
% 1.34/0.57    ~r2_hidden(sK11(sK6,sK8(sK5)),k1_relat_1(sK6)) | sK11(sK6,sK7(sK5)) = sK11(sK6,sK8(sK5)) | (spl12_3 | ~spl12_6 | ~spl12_8 | ~spl12_12)),
% 1.34/0.57    inference(trivial_inequality_removal,[],[f642])).
% 1.34/0.57  fof(f642,plain,(
% 1.34/0.57    k1_funct_1(sK5,sK7(sK5)) != k1_funct_1(sK5,sK7(sK5)) | ~r2_hidden(sK11(sK6,sK8(sK5)),k1_relat_1(sK6)) | sK11(sK6,sK7(sK5)) = sK11(sK6,sK8(sK5)) | (spl12_3 | ~spl12_6 | ~spl12_8 | ~spl12_12)),
% 1.34/0.57    inference(superposition,[],[f507,f480])).
% 1.34/0.57  fof(f480,plain,(
% 1.34/0.57    k1_funct_1(sK5,sK7(sK5)) = k1_funct_1(k5_relat_1(sK6,sK5),sK11(sK6,sK8(sK5))) | (spl12_3 | ~spl12_12)),
% 1.34/0.57    inference(forward_demodulation,[],[f479,f131])).
% 1.34/0.57  fof(f131,plain,(
% 1.34/0.57    k1_funct_1(sK5,sK7(sK5)) = k1_funct_1(sK5,sK8(sK5)) | spl12_3),
% 1.34/0.57    inference(resolution,[],[f71,f119])).
% 1.34/0.57  fof(f71,plain,(
% 1.34/0.57    ( ! [X0] : (sP0(X0) | k1_funct_1(X0,sK7(X0)) = k1_funct_1(X0,sK8(X0))) )),
% 1.34/0.57    inference(cnf_transformation,[],[f43])).
% 1.34/0.57  fof(f479,plain,(
% 1.34/0.57    k1_funct_1(sK5,sK8(sK5)) = k1_funct_1(k5_relat_1(sK6,sK5),sK11(sK6,sK8(sK5))) | (spl12_3 | ~spl12_12)),
% 1.34/0.57    inference(forward_demodulation,[],[f473,f229])).
% 1.34/0.57  fof(f473,plain,(
% 1.34/0.57    k1_funct_1(k5_relat_1(sK6,sK5),sK11(sK6,sK8(sK5))) = k1_funct_1(sK5,k1_funct_1(sK6,sK11(sK6,sK8(sK5)))) | ~spl12_12),
% 1.34/0.57    inference(resolution,[],[f437,f386])).
% 1.34/0.57  fof(f437,plain,(
% 1.34/0.57    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK6)) | k1_funct_1(k5_relat_1(sK6,sK5),X0) = k1_funct_1(sK5,k1_funct_1(sK6,X0))) )),
% 1.34/0.57    inference(subsumption_resolution,[],[f436,f58])).
% 1.34/0.57  fof(f58,plain,(
% 1.34/0.57    v1_relat_1(sK5)),
% 1.34/0.57    inference(cnf_transformation,[],[f38])).
% 1.34/0.57  fof(f436,plain,(
% 1.34/0.57    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK6)) | k1_funct_1(k5_relat_1(sK6,sK5),X0) = k1_funct_1(sK5,k1_funct_1(sK6,X0)) | ~v1_relat_1(sK5)) )),
% 1.34/0.57    inference(subsumption_resolution,[],[f435,f59])).
% 1.34/0.57  fof(f59,plain,(
% 1.34/0.57    v1_funct_1(sK5)),
% 1.34/0.57    inference(cnf_transformation,[],[f38])).
% 1.34/0.57  fof(f435,plain,(
% 1.34/0.57    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK6)) | k1_funct_1(k5_relat_1(sK6,sK5),X0) = k1_funct_1(sK5,k1_funct_1(sK6,X0)) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5)) )),
% 1.34/0.57    inference(subsumption_resolution,[],[f434,f60])).
% 1.34/0.57  fof(f434,plain,(
% 1.34/0.57    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK6)) | k1_funct_1(k5_relat_1(sK6,sK5),X0) = k1_funct_1(sK5,k1_funct_1(sK6,X0)) | ~v1_relat_1(sK6) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5)) )),
% 1.34/0.57    inference(subsumption_resolution,[],[f431,f61])).
% 1.34/0.57  fof(f431,plain,(
% 1.34/0.57    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK6)) | k1_funct_1(k5_relat_1(sK6,sK5),X0) = k1_funct_1(sK5,k1_funct_1(sK6,X0)) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5)) )),
% 1.34/0.57    inference(superposition,[],[f77,f188])).
% 1.34/0.57  fof(f188,plain,(
% 1.34/0.57    k1_relat_1(sK6) = k1_relat_1(k5_relat_1(sK6,sK5))),
% 1.34/0.57    inference(subsumption_resolution,[],[f187,f60])).
% 1.34/0.57  fof(f187,plain,(
% 1.34/0.57    k1_relat_1(sK6) = k1_relat_1(k5_relat_1(sK6,sK5)) | ~v1_relat_1(sK6)),
% 1.34/0.57    inference(resolution,[],[f186,f94])).
% 1.34/0.57  fof(f94,plain,(
% 1.34/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.34/0.57    inference(equality_resolution,[],[f80])).
% 1.34/0.57  fof(f80,plain,(
% 1.34/0.57    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.34/0.57    inference(cnf_transformation,[],[f45])).
% 1.34/0.57  fof(f45,plain,(
% 1.34/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.34/0.57    inference(flattening,[],[f44])).
% 1.34/0.57  fof(f44,plain,(
% 1.34/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.34/0.57    inference(nnf_transformation,[],[f1])).
% 1.34/0.57  fof(f1,axiom,(
% 1.34/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.34/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.34/0.57  fof(f186,plain,(
% 1.34/0.57    ( ! [X0] : (~r1_tarski(k2_relat_1(X0),k2_relat_1(sK6)) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,sK5)) | ~v1_relat_1(X0)) )),
% 1.34/0.57    inference(subsumption_resolution,[],[f185,f58])).
% 1.34/0.57  fof(f185,plain,(
% 1.34/0.57    ( ! [X0] : (~r1_tarski(k2_relat_1(X0),k2_relat_1(sK6)) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,sK5)) | ~v1_relat_1(sK5) | ~v1_relat_1(X0)) )),
% 1.34/0.57    inference(superposition,[],[f65,f63])).
% 1.34/0.57  fof(f65,plain,(
% 1.34/0.57    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.34/0.57    inference(cnf_transformation,[],[f15])).
% 1.34/0.57  fof(f15,plain,(
% 1.34/0.57    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.34/0.57    inference(flattening,[],[f14])).
% 1.34/0.57  fof(f14,plain,(
% 1.34/0.57    ! [X0] : (! [X1] : ((k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.34/0.57    inference(ennf_transformation,[],[f4])).
% 1.34/0.57  fof(f4,axiom,(
% 1.34/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0))))),
% 1.34/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).
% 1.34/0.57  fof(f77,plain,(
% 1.34/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.34/0.57    inference(cnf_transformation,[],[f23])).
% 1.34/0.57  fof(f23,plain,(
% 1.34/0.57    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.34/0.57    inference(flattening,[],[f22])).
% 1.34/0.57  fof(f22,plain,(
% 1.34/0.57    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.34/0.57    inference(ennf_transformation,[],[f7])).
% 1.34/0.57  fof(f7,axiom,(
% 1.34/0.57    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)))))),
% 1.34/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).
% 1.34/0.57  fof(f507,plain,(
% 1.34/0.57    ( ! [X0] : (k1_funct_1(sK5,sK7(sK5)) != k1_funct_1(k5_relat_1(sK6,sK5),X0) | ~r2_hidden(X0,k1_relat_1(sK6)) | sK11(sK6,sK7(sK5)) = X0) ) | (spl12_3 | ~spl12_6 | ~spl12_8)),
% 1.34/0.57    inference(forward_demodulation,[],[f506,f188])).
% 1.34/0.57  fof(f506,plain,(
% 1.34/0.57    ( ! [X0] : (k1_funct_1(sK5,sK7(sK5)) != k1_funct_1(k5_relat_1(sK6,sK5),X0) | sK11(sK6,sK7(sK5)) = X0 | ~r2_hidden(X0,k1_relat_1(k5_relat_1(sK6,sK5)))) ) | (spl12_3 | ~spl12_6 | ~spl12_8)),
% 1.34/0.57    inference(subsumption_resolution,[],[f505,f251])).
% 1.34/0.57  fof(f251,plain,(
% 1.34/0.57    r2_hidden(sK11(sK6,sK7(sK5)),k1_relat_1(sK6)) | ~spl12_8),
% 1.34/0.57    inference(avatar_component_clause,[],[f250])).
% 1.34/0.57  fof(f250,plain,(
% 1.34/0.57    spl12_8 <=> r2_hidden(sK11(sK6,sK7(sK5)),k1_relat_1(sK6))),
% 1.34/0.57    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).
% 1.34/0.57  fof(f505,plain,(
% 1.34/0.57    ( ! [X0] : (~r2_hidden(sK11(sK6,sK7(sK5)),k1_relat_1(sK6)) | k1_funct_1(sK5,sK7(sK5)) != k1_funct_1(k5_relat_1(sK6,sK5),X0) | sK11(sK6,sK7(sK5)) = X0 | ~r2_hidden(X0,k1_relat_1(k5_relat_1(sK6,sK5)))) ) | (spl12_3 | ~spl12_6 | ~spl12_8)),
% 1.34/0.57    inference(forward_demodulation,[],[f504,f188])).
% 1.34/0.57  fof(f504,plain,(
% 1.34/0.57    ( ! [X0] : (k1_funct_1(sK5,sK7(sK5)) != k1_funct_1(k5_relat_1(sK6,sK5),X0) | sK11(sK6,sK7(sK5)) = X0 | ~r2_hidden(sK11(sK6,sK7(sK5)),k1_relat_1(k5_relat_1(sK6,sK5))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(sK6,sK5)))) ) | (spl12_3 | ~spl12_6 | ~spl12_8)),
% 1.34/0.57    inference(subsumption_resolution,[],[f500,f195])).
% 1.34/0.57  fof(f195,plain,(
% 1.34/0.57    sP0(k5_relat_1(sK6,sK5)) | ~spl12_6),
% 1.34/0.57    inference(avatar_component_clause,[],[f193])).
% 1.34/0.57  fof(f500,plain,(
% 1.34/0.57    ( ! [X0] : (k1_funct_1(sK5,sK7(sK5)) != k1_funct_1(k5_relat_1(sK6,sK5),X0) | sK11(sK6,sK7(sK5)) = X0 | ~r2_hidden(sK11(sK6,sK7(sK5)),k1_relat_1(k5_relat_1(sK6,sK5))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(sK6,sK5))) | ~sP0(k5_relat_1(sK6,sK5))) ) | (spl12_3 | ~spl12_8)),
% 1.34/0.57    inference(superposition,[],[f68,f478])).
% 1.34/0.57  fof(f478,plain,(
% 1.34/0.57    k1_funct_1(sK5,sK7(sK5)) = k1_funct_1(k5_relat_1(sK6,sK5),sK11(sK6,sK7(sK5))) | (spl12_3 | ~spl12_8)),
% 1.34/0.57    inference(forward_demodulation,[],[f472,f227])).
% 1.34/0.57  fof(f472,plain,(
% 1.34/0.57    k1_funct_1(k5_relat_1(sK6,sK5),sK11(sK6,sK7(sK5))) = k1_funct_1(sK5,k1_funct_1(sK6,sK11(sK6,sK7(sK5)))) | ~spl12_8),
% 1.34/0.57    inference(resolution,[],[f437,f251])).
% 1.34/0.57  fof(f68,plain,(
% 1.34/0.57    ( ! [X4,X0,X3] : (k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | X3 = X4 | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0)) | ~sP0(X0)) )),
% 1.34/0.57    inference(cnf_transformation,[],[f43])).
% 1.34/0.57  fof(f229,plain,(
% 1.34/0.57    sK8(sK5) = k1_funct_1(sK6,sK11(sK6,sK8(sK5))) | spl12_3),
% 1.34/0.57    inference(subsumption_resolution,[],[f228,f60])).
% 1.34/0.57  fof(f228,plain,(
% 1.34/0.57    ~v1_relat_1(sK6) | sK8(sK5) = k1_funct_1(sK6,sK11(sK6,sK8(sK5))) | spl12_3),
% 1.34/0.57    inference(subsumption_resolution,[],[f222,f61])).
% 1.34/0.57  fof(f222,plain,(
% 1.34/0.57    ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | sK8(sK5) = k1_funct_1(sK6,sK11(sK6,sK8(sK5))) | spl12_3),
% 1.34/0.57    inference(resolution,[],[f206,f125])).
% 1.34/0.57  fof(f125,plain,(
% 1.34/0.57    r2_hidden(sK8(sK5),k2_relat_1(sK6)) | spl12_3),
% 1.34/0.57    inference(subsumption_resolution,[],[f124,f119])).
% 1.34/0.57  fof(f124,plain,(
% 1.34/0.57    r2_hidden(sK8(sK5),k2_relat_1(sK6)) | sP0(sK5)),
% 1.34/0.57    inference(superposition,[],[f70,f63])).
% 1.34/0.57  fof(f70,plain,(
% 1.34/0.57    ( ! [X0] : (r2_hidden(sK8(X0),k1_relat_1(X0)) | sP0(X0)) )),
% 1.34/0.57    inference(cnf_transformation,[],[f43])).
% 1.34/0.57  fof(f548,plain,(
% 1.34/0.57    spl12_20),
% 1.34/0.57    inference(avatar_contradiction_clause,[],[f547])).
% 1.34/0.57  fof(f547,plain,(
% 1.34/0.57    $false | spl12_20),
% 1.34/0.57    inference(subsumption_resolution,[],[f546,f60])).
% 1.34/0.57  fof(f546,plain,(
% 1.34/0.57    ~v1_relat_1(sK6) | spl12_20),
% 1.34/0.57    inference(subsumption_resolution,[],[f545,f61])).
% 1.34/0.57  fof(f545,plain,(
% 1.34/0.57    ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | spl12_20),
% 1.34/0.57    inference(subsumption_resolution,[],[f544,f58])).
% 1.34/0.57  fof(f544,plain,(
% 1.34/0.57    ~v1_relat_1(sK5) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | spl12_20),
% 1.34/0.57    inference(subsumption_resolution,[],[f543,f59])).
% 1.34/0.57  fof(f543,plain,(
% 1.34/0.57    ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | spl12_20),
% 1.34/0.57    inference(resolution,[],[f538,f76])).
% 1.34/0.57  fof(f76,plain,(
% 1.34/0.57    ( ! [X0,X1] : (v1_funct_1(k5_relat_1(X0,X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.34/0.57    inference(cnf_transformation,[],[f21])).
% 1.34/0.57  fof(f21,plain,(
% 1.34/0.57    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.34/0.57    inference(flattening,[],[f20])).
% 1.34/0.57  fof(f20,plain,(
% 1.34/0.57    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.34/0.57    inference(ennf_transformation,[],[f6])).
% 1.34/0.57  fof(f6,axiom,(
% 1.34/0.57    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1) & v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))))),
% 1.34/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funct_1)).
% 1.34/0.57  fof(f538,plain,(
% 1.34/0.57    ~v1_funct_1(k5_relat_1(sK6,sK5)) | spl12_20),
% 1.34/0.57    inference(avatar_component_clause,[],[f536])).
% 1.34/0.57  fof(f397,plain,(
% 1.34/0.57    spl12_12),
% 1.34/0.57    inference(avatar_contradiction_clause,[],[f396])).
% 1.34/0.57  fof(f396,plain,(
% 1.34/0.57    $false | spl12_12),
% 1.34/0.57    inference(subsumption_resolution,[],[f395,f332])).
% 1.34/0.57  fof(f332,plain,(
% 1.34/0.57    r2_hidden(sK8(sK5),k2_relat_1(sK6))),
% 1.34/0.57    inference(global_subsumption,[],[f64,f111,f330,f124])).
% 1.34/0.57  fof(f330,plain,(
% 1.34/0.57    v2_funct_1(sK6)),
% 1.34/0.57    inference(subsumption_resolution,[],[f329,f60])).
% 1.34/0.57  fof(f329,plain,(
% 1.34/0.57    v2_funct_1(sK6) | ~v1_relat_1(sK6)),
% 1.34/0.57    inference(subsumption_resolution,[],[f328,f61])).
% 1.34/0.57  fof(f328,plain,(
% 1.34/0.57    v2_funct_1(sK6) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6)),
% 1.34/0.57    inference(subsumption_resolution,[],[f322,f62])).
% 1.34/0.57  fof(f322,plain,(
% 1.34/0.57    v2_funct_1(sK6) | ~v2_funct_1(k5_relat_1(sK6,sK5)) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6)),
% 1.34/0.57    inference(resolution,[],[f320,f94])).
% 1.34/0.57  fof(f320,plain,(
% 1.34/0.57    ( ! [X0] : (~r1_tarski(k2_relat_1(X0),k2_relat_1(sK6)) | v2_funct_1(X0) | ~v2_funct_1(k5_relat_1(X0,sK5)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.34/0.57    inference(subsumption_resolution,[],[f319,f58])).
% 1.34/0.57  fof(f319,plain,(
% 1.34/0.57    ( ! [X0] : (~r1_tarski(k2_relat_1(X0),k2_relat_1(sK6)) | v2_funct_1(X0) | ~v2_funct_1(k5_relat_1(X0,sK5)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(sK5)) )),
% 1.34/0.57    inference(subsumption_resolution,[],[f317,f59])).
% 1.34/0.57  fof(f317,plain,(
% 1.34/0.57    ( ! [X0] : (~r1_tarski(k2_relat_1(X0),k2_relat_1(sK6)) | v2_funct_1(X0) | ~v2_funct_1(k5_relat_1(X0,sK5)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5)) )),
% 1.34/0.57    inference(superposition,[],[f74,f63])).
% 1.34/0.57  fof(f74,plain,(
% 1.34/0.57    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | v2_funct_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.34/0.57    inference(cnf_transformation,[],[f19])).
% 1.34/0.57  fof(f19,plain,(
% 1.34/0.57    ! [X0] : (! [X1] : (v2_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.34/0.57    inference(flattening,[],[f18])).
% 1.34/0.57  fof(f18,plain,(
% 1.34/0.57    ! [X0] : (! [X1] : ((v2_funct_1(X1) | (~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.34/0.57    inference(ennf_transformation,[],[f8])).
% 1.34/0.57  fof(f8,axiom,(
% 1.34/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & v2_funct_1(k5_relat_1(X1,X0))) => v2_funct_1(X1))))),
% 1.34/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_funct_1)).
% 1.34/0.57  fof(f111,plain,(
% 1.34/0.57    ~sP0(sK5) | v2_funct_1(sK5)),
% 1.34/0.57    inference(resolution,[],[f109,f67])).
% 1.34/0.57  fof(f67,plain,(
% 1.34/0.57    ( ! [X0] : (~sP1(X0) | ~sP0(X0) | v2_funct_1(X0)) )),
% 1.34/0.57    inference(cnf_transformation,[],[f39])).
% 1.34/0.57  fof(f109,plain,(
% 1.34/0.57    sP1(sK5)),
% 1.34/0.57    inference(subsumption_resolution,[],[f107,f58])).
% 1.34/0.57  fof(f107,plain,(
% 1.34/0.57    sP1(sK5) | ~v1_relat_1(sK5)),
% 1.34/0.57    inference(resolution,[],[f73,f59])).
% 1.34/0.57  fof(f64,plain,(
% 1.34/0.57    ~v2_funct_1(sK5) | ~v2_funct_1(sK6)),
% 1.34/0.57    inference(cnf_transformation,[],[f38])).
% 1.34/0.57  fof(f395,plain,(
% 1.34/0.57    ~r2_hidden(sK8(sK5),k2_relat_1(sK6)) | spl12_12),
% 1.34/0.57    inference(subsumption_resolution,[],[f394,f60])).
% 1.34/0.57  fof(f394,plain,(
% 1.34/0.57    ~v1_relat_1(sK6) | ~r2_hidden(sK8(sK5),k2_relat_1(sK6)) | spl12_12),
% 1.34/0.57    inference(subsumption_resolution,[],[f393,f61])).
% 1.34/0.57  fof(f393,plain,(
% 1.34/0.57    ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | ~r2_hidden(sK8(sK5),k2_relat_1(sK6)) | spl12_12),
% 1.34/0.57    inference(resolution,[],[f387,f207])).
% 1.34/0.57  fof(f207,plain,(
% 1.34/0.57    ( ! [X6,X5] : (r2_hidden(sK11(X6,X5),k1_relat_1(X6)) | ~v1_funct_1(X6) | ~v1_relat_1(X6) | ~r2_hidden(X5,k2_relat_1(X6))) )),
% 1.34/0.57    inference(resolution,[],[f204,f90])).
% 1.34/0.57  fof(f90,plain,(
% 1.34/0.57    ( ! [X2,X0,X1] : (~sP3(X0,X1,X2) | r2_hidden(X1,k1_relat_1(X2))) )),
% 1.34/0.57    inference(cnf_transformation,[],[f57])).
% 1.34/0.57  fof(f387,plain,(
% 1.34/0.57    ~r2_hidden(sK11(sK6,sK8(sK5)),k1_relat_1(sK6)) | spl12_12),
% 1.34/0.57    inference(avatar_component_clause,[],[f385])).
% 1.34/0.57  fof(f327,plain,(
% 1.34/0.57    spl12_1),
% 1.34/0.57    inference(avatar_contradiction_clause,[],[f326])).
% 1.34/0.57  fof(f326,plain,(
% 1.34/0.57    $false | spl12_1),
% 1.34/0.57    inference(subsumption_resolution,[],[f325,f60])).
% 1.34/0.57  fof(f325,plain,(
% 1.34/0.57    ~v1_relat_1(sK6) | spl12_1),
% 1.34/0.57    inference(subsumption_resolution,[],[f324,f61])).
% 1.34/0.57  fof(f324,plain,(
% 1.34/0.57    ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | spl12_1),
% 1.34/0.57    inference(subsumption_resolution,[],[f323,f62])).
% 1.34/0.57  fof(f323,plain,(
% 1.34/0.57    ~v2_funct_1(k5_relat_1(sK6,sK5)) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | spl12_1),
% 1.34/0.57    inference(subsumption_resolution,[],[f322,f101])).
% 1.34/0.57  fof(f101,plain,(
% 1.34/0.57    ~v2_funct_1(sK6) | spl12_1),
% 1.34/0.57    inference(avatar_component_clause,[],[f99])).
% 1.34/0.57  fof(f99,plain,(
% 1.34/0.57    spl12_1 <=> v2_funct_1(sK6)),
% 1.34/0.57    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).
% 1.34/0.57  fof(f316,plain,(
% 1.34/0.57    spl12_10),
% 1.34/0.57    inference(avatar_contradiction_clause,[],[f315])).
% 1.34/0.57  fof(f315,plain,(
% 1.34/0.57    $false | spl12_10),
% 1.34/0.57    inference(subsumption_resolution,[],[f314,f60])).
% 1.34/0.57  fof(f314,plain,(
% 1.34/0.57    ~v1_relat_1(sK6) | spl12_10),
% 1.34/0.57    inference(subsumption_resolution,[],[f308,f58])).
% 1.34/0.57  fof(f308,plain,(
% 1.34/0.57    ~v1_relat_1(sK5) | ~v1_relat_1(sK6) | spl12_10),
% 1.34/0.57    inference(resolution,[],[f302,f78])).
% 1.34/0.57  fof(f78,plain,(
% 1.34/0.57    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.34/0.57    inference(cnf_transformation,[],[f25])).
% 1.34/0.57  fof(f25,plain,(
% 1.34/0.57    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.34/0.57    inference(flattening,[],[f24])).
% 1.34/0.57  fof(f24,plain,(
% 1.34/0.57    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.34/0.57    inference(ennf_transformation,[],[f3])).
% 1.34/0.57  fof(f3,axiom,(
% 1.34/0.57    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.34/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.34/0.57  fof(f302,plain,(
% 1.34/0.57    ~v1_relat_1(k5_relat_1(sK6,sK5)) | spl12_10),
% 1.34/0.57    inference(avatar_component_clause,[],[f300])).
% 1.34/0.57  fof(f262,plain,(
% 1.34/0.57    spl12_3 | spl12_8),
% 1.34/0.57    inference(avatar_contradiction_clause,[],[f261])).
% 1.34/0.57  fof(f261,plain,(
% 1.34/0.57    $false | (spl12_3 | spl12_8)),
% 1.34/0.57    inference(subsumption_resolution,[],[f260,f123])).
% 1.34/0.57  fof(f260,plain,(
% 1.34/0.57    ~r2_hidden(sK7(sK5),k2_relat_1(sK6)) | spl12_8),
% 1.34/0.57    inference(subsumption_resolution,[],[f259,f60])).
% 1.34/0.57  fof(f259,plain,(
% 1.34/0.57    ~v1_relat_1(sK6) | ~r2_hidden(sK7(sK5),k2_relat_1(sK6)) | spl12_8),
% 1.34/0.57    inference(subsumption_resolution,[],[f258,f61])).
% 1.34/0.57  fof(f258,plain,(
% 1.34/0.57    ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | ~r2_hidden(sK7(sK5),k2_relat_1(sK6)) | spl12_8),
% 1.34/0.57    inference(resolution,[],[f252,f207])).
% 1.34/0.57  fof(f252,plain,(
% 1.34/0.57    ~r2_hidden(sK11(sK6,sK7(sK5)),k1_relat_1(sK6)) | spl12_8),
% 1.34/0.57    inference(avatar_component_clause,[],[f250])).
% 1.34/0.57  fof(f120,plain,(
% 1.34/0.57    spl12_2 | ~spl12_3),
% 1.34/0.57    inference(avatar_split_clause,[],[f111,f117,f103])).
% 1.34/0.57  fof(f103,plain,(
% 1.34/0.57    spl12_2 <=> v2_funct_1(sK5)),
% 1.34/0.57    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).
% 1.34/0.57  fof(f106,plain,(
% 1.34/0.57    ~spl12_1 | ~spl12_2),
% 1.34/0.57    inference(avatar_split_clause,[],[f64,f103,f99])).
% 1.34/0.57  % SZS output end Proof for theBenchmark
% 1.34/0.57  % (2324)------------------------------
% 1.34/0.57  % (2324)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.57  % (2324)Termination reason: Refutation
% 1.34/0.57  
% 1.34/0.57  % (2324)Memory used [KB]: 11385
% 1.34/0.57  % (2324)Time elapsed: 0.163 s
% 1.34/0.57  % (2324)------------------------------
% 1.34/0.57  % (2324)------------------------------
% 1.34/0.59  % (2293)Success in time 0.231 s
%------------------------------------------------------------------------------
