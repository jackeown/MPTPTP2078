%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:39 EST 2020

% Result     : Theorem 6.51s
% Output     : Refutation 6.51s
% Verified   : 
% Statistics : Number of formulae       :  192 (1035 expanded)
%              Number of leaves         :   28 ( 334 expanded)
%              Depth                    :   31
%              Number of atoms          :  743 (6698 expanded)
%              Number of equality atoms :  112 (1071 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5507,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f97,f111,f410,f699,f728,f1104,f2012,f5346,f5506])).

fof(f5506,plain,
    ( spl11_6
    | ~ spl11_24
    | ~ spl11_25 ),
    inference(avatar_contradiction_clause,[],[f5505])).

fof(f5505,plain,
    ( $false
    | spl11_6
    | ~ spl11_24
    | ~ spl11_25 ),
    inference(subsumption_resolution,[],[f195,f5504])).

fof(f5504,plain,
    ( sP0(k5_relat_1(sK6,sK5))
    | ~ spl11_24
    | ~ spl11_25 ),
    inference(subsumption_resolution,[],[f742,f58])).

fof(f58,plain,(
    v2_funct_1(k5_relat_1(sK6,sK5)) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ( ~ v2_funct_1(sK5)
      | ~ v2_funct_1(sK6) )
    & k1_relat_1(sK5) = k2_relat_1(sK6)
    & v2_funct_1(k5_relat_1(sK6,sK5))
    & v1_funct_1(sK6)
    & v1_relat_1(sK6)
    & v1_funct_1(sK5)
    & v1_relat_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f13,f38,f37])).

fof(f37,plain,
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

fof(f38,plain,
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).

fof(f742,plain,
    ( ~ v2_funct_1(k5_relat_1(sK6,sK5))
    | sP0(k5_relat_1(sK6,sK5))
    | ~ spl11_24
    | ~ spl11_25 ),
    inference(resolution,[],[f740,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | ~ v2_funct_1(X0)
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ~ sP0(X0) )
        & ( sP0(X0)
          | ~ v2_funct_1(X0) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> sP0(X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f740,plain,
    ( sP1(k5_relat_1(sK6,sK5))
    | ~ spl11_24
    | ~ spl11_25 ),
    inference(subsumption_resolution,[],[f736,f683])).

fof(f683,plain,
    ( v1_relat_1(k5_relat_1(sK6,sK5))
    | ~ spl11_24 ),
    inference(avatar_component_clause,[],[f682])).

fof(f682,plain,
    ( spl11_24
  <=> v1_relat_1(k5_relat_1(sK6,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_24])])).

fof(f736,plain,
    ( sP1(k5_relat_1(sK6,sK5))
    | ~ v1_relat_1(k5_relat_1(sK6,sK5))
    | ~ spl11_25 ),
    inference(resolution,[],[f687,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | sP1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f17,f31,f30])).

fof(f30,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ! [X1,X2] :
          ( X1 = X2
          | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
          | ~ r2_hidden(X2,k1_relat_1(X0))
          | ~ r2_hidden(X1,k1_relat_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

fof(f687,plain,
    ( v1_funct_1(k5_relat_1(sK6,sK5))
    | ~ spl11_25 ),
    inference(avatar_component_clause,[],[f686])).

fof(f686,plain,
    ( spl11_25
  <=> v1_funct_1(k5_relat_1(sK6,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_25])])).

fof(f195,plain,
    ( ~ sP0(k5_relat_1(sK6,sK5))
    | spl11_6 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl11_6
  <=> sP0(k5_relat_1(sK6,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f5346,plain,
    ( spl11_3
    | ~ spl11_6
    | ~ spl11_37
    | ~ spl11_50 ),
    inference(avatar_contradiction_clause,[],[f5345])).

fof(f5345,plain,
    ( $false
    | spl11_3
    | ~ spl11_6
    | ~ spl11_37
    | ~ spl11_50 ),
    inference(subsumption_resolution,[],[f5344,f110])).

fof(f110,plain,
    ( ~ sP0(sK5)
    | spl11_3 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl11_3
  <=> sP0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f5344,plain,
    ( sP0(sK5)
    | spl11_3
    | ~ spl11_6
    | ~ spl11_37
    | ~ spl11_50 ),
    inference(trivial_inequality_removal,[],[f5342])).

fof(f5342,plain,
    ( sK7(sK5) != sK7(sK5)
    | sP0(sK5)
    | spl11_3
    | ~ spl11_6
    | ~ spl11_37
    | ~ spl11_50 ),
    inference(superposition,[],[f69,f5218])).

fof(f5218,plain,
    ( sK7(sK5) = sK8(sK5)
    | spl11_3
    | ~ spl11_6
    | ~ spl11_37
    | ~ spl11_50 ),
    inference(forward_demodulation,[],[f5193,f139])).

fof(f139,plain,
    ( sK7(sK5) = k1_funct_1(sK6,sK10(sK7(sK5),sK6))
    | spl11_3 ),
    inference(resolution,[],[f80,f133])).

fof(f133,plain,
    ( sP2(sK7(sK5),sK6)
    | spl11_3 ),
    inference(subsumption_resolution,[],[f130,f116])).

fof(f116,plain,(
    sP4(sK6) ),
    inference(subsumption_resolution,[],[f114,f56])).

fof(f56,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f39])).

fof(f114,plain,
    ( sP4(sK6)
    | ~ v1_relat_1(sK6) ),
    inference(resolution,[],[f82,f57])).

fof(f57,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f39])).

fof(f82,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | sP4(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( sP4(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f23,f35,f34,f33])).

fof(f33,plain,(
    ! [X2,X0] :
      ( sP2(X2,X0)
    <=> ? [X3] :
          ( k1_funct_1(X0,X3) = X2
          & r2_hidden(X3,k1_relat_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f34,plain,(
    ! [X0,X1] :
      ( sP3(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> sP2(X2,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> sP3(X0,X1) )
      | ~ sP4(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(f130,plain,
    ( sP2(sK7(sK5),sK6)
    | ~ sP4(sK6)
    | spl11_3 ),
    inference(resolution,[],[f127,f118])).

fof(f118,plain,
    ( r2_hidden(sK7(sK5),k2_relat_1(sK6))
    | spl11_3 ),
    inference(subsumption_resolution,[],[f117,f110])).

fof(f117,plain,
    ( r2_hidden(sK7(sK5),k2_relat_1(sK6))
    | sP0(sK5) ),
    inference(superposition,[],[f66,f59])).

fof(f59,plain,(
    k1_relat_1(sK5) = k2_relat_1(sK6) ),
    inference(cnf_transformation,[],[f39])).

fof(f66,plain,(
    ! [X0] :
      ( r2_hidden(sK7(X0),k1_relat_1(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f42,f43])).

fof(f43,plain,(
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

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f127,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_relat_1(X1))
      | sP2(X0,X1)
      | ~ sP4(X1) ) ),
    inference(resolution,[],[f75,f87])).

fof(f87,plain,(
    ! [X0] :
      ( sP3(X0,k2_relat_1(X0))
      | ~ sP4(X0) ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( sP3(X0,X1)
      | k2_relat_1(X0) != X1
      | ~ sP4(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ~ sP3(X0,X1) )
          & ( sP3(X0,X1)
            | k2_relat_1(X0) != X1 ) )
      | ~ sP4(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f75,plain,(
    ! [X0,X3,X1] :
      ( ~ sP3(X0,X1)
      | ~ r2_hidden(X3,X1)
      | sP2(X3,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( sP3(X0,X1)
        | ( ( ~ sP2(sK9(X0,X1),X0)
            | ~ r2_hidden(sK9(X0,X1),X1) )
          & ( sP2(sK9(X0,X1),X0)
            | r2_hidden(sK9(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ sP2(X3,X0) )
            & ( sP2(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP3(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f47,f48])).

fof(f48,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ sP2(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( sP2(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ sP2(sK9(X0,X1),X0)
          | ~ r2_hidden(sK9(X0,X1),X1) )
        & ( sP2(sK9(X0,X1),X0)
          | r2_hidden(sK9(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( sP3(X0,X1)
        | ? [X2] :
            ( ( ~ sP2(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( sP2(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ sP2(X3,X0) )
            & ( sP2(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP3(X0,X1) ) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( sP3(X0,X1)
        | ? [X2] :
            ( ( ~ sP2(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( sP2(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ sP2(X2,X0) )
            & ( sP2(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | ~ sP3(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ sP2(X0,X1)
      | k1_funct_1(X1,sK10(X0,X1)) = X0 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ! [X2] :
            ( k1_funct_1(X1,X2) != X0
            | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
      & ( ( k1_funct_1(X1,sK10(X0,X1)) = X0
          & r2_hidden(sK10(X0,X1),k1_relat_1(X1)) )
        | ~ sP2(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f51,f52])).

fof(f52,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( k1_funct_1(X1,X3) = X0
          & r2_hidden(X3,k1_relat_1(X1)) )
     => ( k1_funct_1(X1,sK10(X0,X1)) = X0
        & r2_hidden(sK10(X0,X1),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ! [X2] :
            ( k1_funct_1(X1,X2) != X0
            | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
      & ( ? [X3] :
            ( k1_funct_1(X1,X3) = X0
            & r2_hidden(X3,k1_relat_1(X1)) )
        | ~ sP2(X0,X1) ) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X2,X0] :
      ( ( sP2(X2,X0)
        | ! [X3] :
            ( k1_funct_1(X0,X3) != X2
            | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
      & ( ? [X3] :
            ( k1_funct_1(X0,X3) = X2
            & r2_hidden(X3,k1_relat_1(X0)) )
        | ~ sP2(X2,X0) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f5193,plain,
    ( sK8(sK5) = k1_funct_1(sK6,sK10(sK7(sK5),sK6))
    | spl11_3
    | ~ spl11_6
    | ~ spl11_37
    | ~ spl11_50 ),
    inference(backward_demodulation,[],[f140,f5190])).

fof(f5190,plain,
    ( sK10(sK7(sK5),sK6) = sK10(sK8(sK5),sK6)
    | spl11_3
    | ~ spl11_6
    | ~ spl11_37
    | ~ spl11_50 ),
    inference(subsumption_resolution,[],[f5189,f1099])).

fof(f1099,plain,
    ( r2_hidden(sK10(sK7(sK5),sK6),k1_relat_1(sK6))
    | ~ spl11_37 ),
    inference(avatar_component_clause,[],[f1098])).

fof(f1098,plain,
    ( spl11_37
  <=> r2_hidden(sK10(sK7(sK5),sK6),k1_relat_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_37])])).

fof(f5189,plain,
    ( ~ r2_hidden(sK10(sK7(sK5),sK6),k1_relat_1(sK6))
    | sK10(sK7(sK5),sK6) = sK10(sK8(sK5),sK6)
    | spl11_3
    | ~ spl11_6
    | ~ spl11_50 ),
    inference(trivial_inequality_removal,[],[f5185])).

fof(f5185,plain,
    ( k1_funct_1(sK5,sK7(sK5)) != k1_funct_1(sK5,sK7(sK5))
    | ~ r2_hidden(sK10(sK7(sK5),sK6),k1_relat_1(sK6))
    | sK10(sK7(sK5),sK6) = sK10(sK8(sK5),sK6)
    | spl11_3
    | ~ spl11_6
    | ~ spl11_50 ),
    inference(superposition,[],[f5096,f1076])).

fof(f1076,plain,
    ( k1_funct_1(sK5,sK7(sK5)) = k1_funct_1(k5_relat_1(sK6,sK5),sK10(sK7(sK5),sK6))
    | spl11_3 ),
    inference(subsumption_resolution,[],[f1072,f54])).

fof(f54,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f39])).

fof(f1072,plain,
    ( k1_funct_1(sK5,sK7(sK5)) = k1_funct_1(k5_relat_1(sK6,sK5),sK10(sK7(sK5),sK6))
    | ~ v1_relat_1(sK5)
    | spl11_3 ),
    inference(resolution,[],[f1059,f55])).

fof(f55,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f39])).

fof(f1059,plain,
    ( ! [X6] :
        ( ~ v1_funct_1(X6)
        | k1_funct_1(k5_relat_1(sK6,X6),sK10(sK7(sK5),sK6)) = k1_funct_1(X6,sK7(sK5))
        | ~ v1_relat_1(X6) )
    | spl11_3 ),
    inference(forward_demodulation,[],[f1058,f139])).

fof(f1058,plain,
    ( ! [X6] :
        ( ~ v1_funct_1(X6)
        | ~ v1_relat_1(X6)
        | k1_funct_1(k5_relat_1(sK6,X6),sK10(sK7(sK5),sK6)) = k1_funct_1(X6,k1_funct_1(sK6,sK10(sK7(sK5),sK6))) )
    | spl11_3 ),
    inference(subsumption_resolution,[],[f1057,f56])).

fof(f1057,plain,
    ( ! [X6] :
        ( ~ v1_funct_1(X6)
        | ~ v1_relat_1(X6)
        | ~ v1_relat_1(sK6)
        | k1_funct_1(k5_relat_1(sK6,X6),sK10(sK7(sK5),sK6)) = k1_funct_1(X6,k1_funct_1(sK6,sK10(sK7(sK5),sK6))) )
    | spl11_3 ),
    inference(subsumption_resolution,[],[f1040,f57])).

fof(f1040,plain,
    ( ! [X6] :
        ( ~ v1_funct_1(X6)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(sK6)
        | ~ v1_relat_1(sK6)
        | k1_funct_1(k5_relat_1(sK6,X6),sK10(sK7(sK5),sK6)) = k1_funct_1(X6,k1_funct_1(sK6,sK10(sK7(sK5),sK6))) )
    | spl11_3 ),
    inference(resolution,[],[f482,f133])).

fof(f482,plain,(
    ! [X8,X7,X9] :
      ( ~ sP2(X9,X7)
      | ~ v1_funct_1(X8)
      | ~ v1_relat_1(X8)
      | ~ v1_funct_1(X7)
      | ~ v1_relat_1(X7)
      | k1_funct_1(k5_relat_1(X7,X8),sK10(X9,X7)) = k1_funct_1(X8,k1_funct_1(X7,sK10(X9,X7))) ) ),
    inference(resolution,[],[f85,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK10(X0,X1),k1_relat_1(X1))
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(X1))
      | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
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
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

fof(f5096,plain,
    ( ! [X0] :
        ( k1_funct_1(sK5,sK7(sK5)) != k1_funct_1(k5_relat_1(sK6,sK5),X0)
        | ~ r2_hidden(X0,k1_relat_1(sK6))
        | sK10(sK8(sK5),sK6) = X0 )
    | spl11_3
    | ~ spl11_6
    | ~ spl11_50 ),
    inference(forward_demodulation,[],[f5095,f189])).

fof(f189,plain,(
    k1_relat_1(sK6) = k1_relat_1(k5_relat_1(sK6,sK5)) ),
    inference(forward_demodulation,[],[f186,f122])).

fof(f122,plain,(
    k10_relat_1(sK6,k2_relat_1(sK6)) = k1_relat_1(sK6) ),
    inference(resolution,[],[f61,f56])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f186,plain,(
    k10_relat_1(sK6,k2_relat_1(sK6)) = k1_relat_1(k5_relat_1(sK6,sK5)) ),
    inference(resolution,[],[f180,f56])).

fof(f180,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(X0,sK5)) = k10_relat_1(X0,k2_relat_1(sK6)) ) ),
    inference(forward_demodulation,[],[f176,f59])).

fof(f176,plain,(
    ! [X0] :
      ( k1_relat_1(k5_relat_1(X0,sK5)) = k10_relat_1(X0,k1_relat_1(sK5))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f62,f54])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f5095,plain,
    ( ! [X0] :
        ( k1_funct_1(sK5,sK7(sK5)) != k1_funct_1(k5_relat_1(sK6,sK5),X0)
        | sK10(sK8(sK5),sK6) = X0
        | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK6,sK5))) )
    | spl11_3
    | ~ spl11_6
    | ~ spl11_50 ),
    inference(subsumption_resolution,[],[f5094,f2003])).

fof(f2003,plain,
    ( r2_hidden(sK10(sK8(sK5),sK6),k1_relat_1(sK6))
    | ~ spl11_50 ),
    inference(avatar_component_clause,[],[f2002])).

fof(f2002,plain,
    ( spl11_50
  <=> r2_hidden(sK10(sK8(sK5),sK6),k1_relat_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_50])])).

fof(f5094,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK10(sK8(sK5),sK6),k1_relat_1(sK6))
        | k1_funct_1(sK5,sK7(sK5)) != k1_funct_1(k5_relat_1(sK6,sK5),X0)
        | sK10(sK8(sK5),sK6) = X0
        | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK6,sK5))) )
    | spl11_3
    | ~ spl11_6 ),
    inference(forward_demodulation,[],[f5093,f189])).

fof(f5093,plain,
    ( ! [X0] :
        ( k1_funct_1(sK5,sK7(sK5)) != k1_funct_1(k5_relat_1(sK6,sK5),X0)
        | sK10(sK8(sK5),sK6) = X0
        | ~ r2_hidden(sK10(sK8(sK5),sK6),k1_relat_1(k5_relat_1(sK6,sK5)))
        | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK6,sK5))) )
    | spl11_3
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f5090,f196])).

fof(f196,plain,
    ( sP0(k5_relat_1(sK6,sK5))
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f194])).

fof(f5090,plain,
    ( ! [X0] :
        ( k1_funct_1(sK5,sK7(sK5)) != k1_funct_1(k5_relat_1(sK6,sK5),X0)
        | sK10(sK8(sK5),sK6) = X0
        | ~ r2_hidden(sK10(sK8(sK5),sK6),k1_relat_1(k5_relat_1(sK6,sK5)))
        | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK6,sK5)))
        | ~ sP0(k5_relat_1(sK6,sK5)) )
    | spl11_3 ),
    inference(superposition,[],[f65,f1125])).

fof(f1125,plain,
    ( k1_funct_1(sK5,sK7(sK5)) = k1_funct_1(k5_relat_1(sK6,sK5),sK10(sK8(sK5),sK6))
    | spl11_3 ),
    inference(forward_demodulation,[],[f1124,f145])).

fof(f145,plain,
    ( k1_funct_1(sK5,sK7(sK5)) = k1_funct_1(sK5,sK8(sK5))
    | spl11_3 ),
    inference(resolution,[],[f68,f110])).

fof(f68,plain,(
    ! [X0] :
      ( sP0(X0)
      | k1_funct_1(X0,sK7(X0)) = k1_funct_1(X0,sK8(X0)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f1124,plain,
    ( k1_funct_1(sK5,sK8(sK5)) = k1_funct_1(k5_relat_1(sK6,sK5),sK10(sK8(sK5),sK6))
    | spl11_3 ),
    inference(subsumption_resolution,[],[f1120,f54])).

fof(f1120,plain,
    ( k1_funct_1(sK5,sK8(sK5)) = k1_funct_1(k5_relat_1(sK6,sK5),sK10(sK8(sK5),sK6))
    | ~ v1_relat_1(sK5)
    | spl11_3 ),
    inference(resolution,[],[f1062,f55])).

fof(f1062,plain,
    ( ! [X7] :
        ( ~ v1_funct_1(X7)
        | k1_funct_1(k5_relat_1(sK6,X7),sK10(sK8(sK5),sK6)) = k1_funct_1(X7,sK8(sK5))
        | ~ v1_relat_1(X7) )
    | spl11_3 ),
    inference(forward_demodulation,[],[f1061,f140])).

fof(f1061,plain,
    ( ! [X7] :
        ( ~ v1_funct_1(X7)
        | ~ v1_relat_1(X7)
        | k1_funct_1(k5_relat_1(sK6,X7),sK10(sK8(sK5),sK6)) = k1_funct_1(X7,k1_funct_1(sK6,sK10(sK8(sK5),sK6))) )
    | spl11_3 ),
    inference(subsumption_resolution,[],[f1060,f56])).

fof(f1060,plain,
    ( ! [X7] :
        ( ~ v1_funct_1(X7)
        | ~ v1_relat_1(X7)
        | ~ v1_relat_1(sK6)
        | k1_funct_1(k5_relat_1(sK6,X7),sK10(sK8(sK5),sK6)) = k1_funct_1(X7,k1_funct_1(sK6,sK10(sK8(sK5),sK6))) )
    | spl11_3 ),
    inference(subsumption_resolution,[],[f1041,f57])).

fof(f1041,plain,
    ( ! [X7] :
        ( ~ v1_funct_1(X7)
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(sK6)
        | ~ v1_relat_1(sK6)
        | k1_funct_1(k5_relat_1(sK6,X7),sK10(sK8(sK5),sK6)) = k1_funct_1(X7,k1_funct_1(sK6,sK10(sK8(sK5),sK6))) )
    | spl11_3 ),
    inference(resolution,[],[f482,f134])).

fof(f134,plain,
    ( sP2(sK8(sK5),sK6)
    | spl11_3 ),
    inference(subsumption_resolution,[],[f131,f116])).

fof(f131,plain,
    ( sP2(sK8(sK5),sK6)
    | ~ sP4(sK6)
    | spl11_3 ),
    inference(resolution,[],[f127,f120])).

fof(f120,plain,
    ( r2_hidden(sK8(sK5),k2_relat_1(sK6))
    | spl11_3 ),
    inference(subsumption_resolution,[],[f119,f110])).

fof(f119,plain,
    ( r2_hidden(sK8(sK5),k2_relat_1(sK6))
    | sP0(sK5) ),
    inference(superposition,[],[f67,f59])).

fof(f67,plain,(
    ! [X0] :
      ( r2_hidden(sK8(X0),k1_relat_1(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f65,plain,(
    ! [X4,X0,X3] :
      ( k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | X3 = X4
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f140,plain,
    ( sK8(sK5) = k1_funct_1(sK6,sK10(sK8(sK5),sK6))
    | spl11_3 ),
    inference(resolution,[],[f80,f134])).

fof(f69,plain,(
    ! [X0] :
      ( sK7(X0) != sK8(X0)
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f2012,plain,
    ( spl11_3
    | spl11_50 ),
    inference(avatar_contradiction_clause,[],[f2011])).

fof(f2011,plain,
    ( $false
    | spl11_3
    | spl11_50 ),
    inference(subsumption_resolution,[],[f2010,f134])).

fof(f2010,plain,
    ( ~ sP2(sK8(sK5),sK6)
    | spl11_50 ),
    inference(resolution,[],[f2004,f79])).

fof(f2004,plain,
    ( ~ r2_hidden(sK10(sK8(sK5),sK6),k1_relat_1(sK6))
    | spl11_50 ),
    inference(avatar_component_clause,[],[f2002])).

fof(f1104,plain,
    ( spl11_3
    | spl11_37 ),
    inference(avatar_contradiction_clause,[],[f1103])).

fof(f1103,plain,
    ( $false
    | spl11_3
    | spl11_37 ),
    inference(subsumption_resolution,[],[f1102,f133])).

fof(f1102,plain,
    ( ~ sP2(sK7(sK5),sK6)
    | spl11_37 ),
    inference(resolution,[],[f1100,f79])).

fof(f1100,plain,
    ( ~ r2_hidden(sK10(sK7(sK5),sK6),k1_relat_1(sK6))
    | spl11_37 ),
    inference(avatar_component_clause,[],[f1098])).

fof(f728,plain,(
    spl11_25 ),
    inference(avatar_contradiction_clause,[],[f727])).

fof(f727,plain,
    ( $false
    | spl11_25 ),
    inference(subsumption_resolution,[],[f726,f56])).

fof(f726,plain,
    ( ~ v1_relat_1(sK6)
    | spl11_25 ),
    inference(subsumption_resolution,[],[f725,f57])).

fof(f725,plain,
    ( ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | spl11_25 ),
    inference(subsumption_resolution,[],[f724,f54])).

fof(f724,plain,
    ( ~ v1_relat_1(sK5)
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | spl11_25 ),
    inference(subsumption_resolution,[],[f723,f55])).

fof(f723,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | spl11_25 ),
    inference(resolution,[],[f688,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).

fof(f688,plain,
    ( ~ v1_funct_1(k5_relat_1(sK6,sK5))
    | spl11_25 ),
    inference(avatar_component_clause,[],[f686])).

fof(f699,plain,(
    spl11_24 ),
    inference(avatar_contradiction_clause,[],[f698])).

fof(f698,plain,
    ( $false
    | spl11_24 ),
    inference(subsumption_resolution,[],[f697,f56])).

fof(f697,plain,
    ( ~ v1_relat_1(sK6)
    | spl11_24 ),
    inference(subsumption_resolution,[],[f691,f54])).

fof(f691,plain,
    ( ~ v1_relat_1(sK5)
    | ~ v1_relat_1(sK6)
    | spl11_24 ),
    inference(resolution,[],[f684,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f684,plain,
    ( ~ v1_relat_1(k5_relat_1(sK6,sK5))
    | spl11_24 ),
    inference(avatar_component_clause,[],[f682])).

fof(f410,plain,(
    spl11_1 ),
    inference(avatar_contradiction_clause,[],[f409])).

fof(f409,plain,
    ( $false
    | spl11_1 ),
    inference(subsumption_resolution,[],[f408,f56])).

fof(f408,plain,
    ( ~ v1_relat_1(sK6)
    | spl11_1 ),
    inference(subsumption_resolution,[],[f407,f57])).

fof(f407,plain,
    ( ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | spl11_1 ),
    inference(subsumption_resolution,[],[f406,f58])).

fof(f406,plain,
    ( ~ v2_funct_1(k5_relat_1(sK6,sK5))
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | spl11_1 ),
    inference(subsumption_resolution,[],[f405,f92])).

fof(f92,plain,
    ( ~ v2_funct_1(sK6)
    | spl11_1 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl11_1
  <=> v2_funct_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f405,plain,
    ( v2_funct_1(sK6)
    | ~ v2_funct_1(k5_relat_1(sK6,sK5))
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6) ),
    inference(resolution,[],[f388,f235])).

fof(f235,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(X0),k2_relat_1(sK6))
      | v2_funct_1(X0)
      | ~ v2_funct_1(k5_relat_1(X0,sK5))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f234,f54])).

fof(f234,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(X0),k2_relat_1(sK6))
      | v2_funct_1(X0)
      | ~ v2_funct_1(k5_relat_1(X0,sK5))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK5) ) ),
    inference(subsumption_resolution,[],[f232,f55])).

fof(f232,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(X0),k2_relat_1(sK6))
      | v2_funct_1(X0)
      | ~ v2_funct_1(k5_relat_1(X0,sK5))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(sK5)
      | ~ v1_relat_1(sK5) ) ),
    inference(superposition,[],[f72,f59])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
      | v2_funct_1(X1)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(X1)
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(X1)
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => v2_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_funct_1)).

fof(f388,plain,(
    r1_tarski(k2_relat_1(sK6),k2_relat_1(sK6)) ),
    inference(forward_demodulation,[],[f387,f59])).

fof(f387,plain,(
    r1_tarski(k2_relat_1(sK6),k1_relat_1(sK5)) ),
    inference(subsumption_resolution,[],[f386,f54])).

fof(f386,plain,
    ( r1_tarski(k2_relat_1(sK6),k1_relat_1(sK5))
    | ~ v1_relat_1(sK5) ),
    inference(subsumption_resolution,[],[f385,f55])).

fof(f385,plain,
    ( r1_tarski(k2_relat_1(sK6),k1_relat_1(sK5))
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5) ),
    inference(subsumption_resolution,[],[f384,f56])).

fof(f384,plain,
    ( r1_tarski(k2_relat_1(sK6),k1_relat_1(sK5))
    | ~ v1_relat_1(sK6)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5) ),
    inference(subsumption_resolution,[],[f383,f57])).

fof(f383,plain,
    ( r1_tarski(k2_relat_1(sK6),k1_relat_1(sK5))
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5) ),
    inference(trivial_inequality_removal,[],[f382])).

fof(f382,plain,
    ( k1_relat_1(sK6) != k1_relat_1(sK6)
    | r1_tarski(k2_relat_1(sK6),k1_relat_1(sK5))
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5) ),
    inference(superposition,[],[f71,f189])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
      | r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
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
         => ( k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0))
           => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_funct_1)).

fof(f111,plain,
    ( spl11_2
    | ~ spl11_3 ),
    inference(avatar_split_clause,[],[f102,f108,f94])).

fof(f94,plain,
    ( spl11_2
  <=> v2_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f102,plain,
    ( ~ sP0(sK5)
    | v2_funct_1(sK5) ),
    inference(resolution,[],[f100,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | ~ sP0(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f100,plain,(
    sP1(sK5) ),
    inference(subsumption_resolution,[],[f98,f54])).

fof(f98,plain,
    ( sP1(sK5)
    | ~ v1_relat_1(sK5) ),
    inference(resolution,[],[f70,f55])).

fof(f97,plain,
    ( ~ spl11_1
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f60,f94,f90])).

fof(f60,plain,
    ( ~ v2_funct_1(sK5)
    | ~ v2_funct_1(sK6) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n019.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 17:28:07 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (31636)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.51  % (31628)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (31633)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.54  % (31649)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.54  % (31630)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.54  % (31631)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.54  % (31635)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.55  % (31639)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.55  % (31632)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.55  % (31641)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.55  % (31647)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.55  % (31629)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.56  % (31652)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.41/0.56  % (31640)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.41/0.57  % (31650)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.41/0.57  % (31648)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.41/0.57  % (31637)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.70/0.58  % (31646)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.70/0.58  % (31638)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.70/0.58  % (31627)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.70/0.58  % (31645)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.70/0.59  % (31642)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.70/0.60  % (31643)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.70/0.60  % (31651)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.70/0.60  % (31634)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.70/0.60  % (31644)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.70/0.62  % (31636)Refutation not found, incomplete strategy% (31636)------------------------------
% 1.70/0.62  % (31636)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.64  % (31636)Termination reason: Refutation not found, incomplete strategy
% 1.70/0.64  
% 1.70/0.64  % (31636)Memory used [KB]: 6140
% 1.70/0.64  % (31636)Time elapsed: 0.196 s
% 1.70/0.64  % (31636)------------------------------
% 1.70/0.64  % (31636)------------------------------
% 4.03/0.93  % (31627)Time limit reached!
% 4.03/0.93  % (31627)------------------------------
% 4.03/0.93  % (31627)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.03/0.93  % (31627)Termination reason: Time limit
% 4.03/0.93  
% 4.03/0.93  % (31627)Memory used [KB]: 19573
% 4.03/0.93  % (31627)Time elapsed: 0.504 s
% 4.03/0.93  % (31627)------------------------------
% 4.03/0.93  % (31627)------------------------------
% 4.03/0.94  % (31640)Time limit reached!
% 4.03/0.94  % (31640)------------------------------
% 4.03/0.94  % (31640)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.03/0.94  % (31640)Termination reason: Time limit
% 4.03/0.94  
% 4.03/0.94  % (31640)Memory used [KB]: 19829
% 4.03/0.94  % (31640)Time elapsed: 0.516 s
% 4.03/0.94  % (31640)------------------------------
% 4.03/0.94  % (31640)------------------------------
% 4.03/0.95  % (31641)Time limit reached!
% 4.03/0.95  % (31641)------------------------------
% 4.03/0.95  % (31641)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.03/0.95  % (31641)Termination reason: Time limit
% 4.03/0.95  
% 4.03/0.95  % (31641)Memory used [KB]: 8315
% 4.03/0.95  % (31641)Time elapsed: 0.509 s
% 4.03/0.95  % (31641)------------------------------
% 4.03/0.95  % (31641)------------------------------
% 5.15/1.04  % (31633)Time limit reached!
% 5.15/1.04  % (31633)------------------------------
% 5.15/1.04  % (31633)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.43/1.05  % (31633)Termination reason: Time limit
% 5.43/1.05  
% 5.43/1.05  % (31633)Memory used [KB]: 20468
% 5.43/1.05  % (31633)Time elapsed: 0.616 s
% 5.43/1.05  % (31633)------------------------------
% 5.43/1.05  % (31633)------------------------------
% 6.51/1.21  % (31652)Refutation found. Thanks to Tanya!
% 6.51/1.21  % SZS status Theorem for theBenchmark
% 6.51/1.21  % SZS output start Proof for theBenchmark
% 6.51/1.21  fof(f5507,plain,(
% 6.51/1.21    $false),
% 6.51/1.21    inference(avatar_sat_refutation,[],[f97,f111,f410,f699,f728,f1104,f2012,f5346,f5506])).
% 6.51/1.21  fof(f5506,plain,(
% 6.51/1.21    spl11_6 | ~spl11_24 | ~spl11_25),
% 6.51/1.21    inference(avatar_contradiction_clause,[],[f5505])).
% 6.51/1.21  fof(f5505,plain,(
% 6.51/1.21    $false | (spl11_6 | ~spl11_24 | ~spl11_25)),
% 6.51/1.21    inference(subsumption_resolution,[],[f195,f5504])).
% 6.51/1.21  fof(f5504,plain,(
% 6.51/1.21    sP0(k5_relat_1(sK6,sK5)) | (~spl11_24 | ~spl11_25)),
% 6.51/1.21    inference(subsumption_resolution,[],[f742,f58])).
% 6.51/1.21  fof(f58,plain,(
% 6.51/1.21    v2_funct_1(k5_relat_1(sK6,sK5))),
% 6.51/1.21    inference(cnf_transformation,[],[f39])).
% 6.51/1.21  fof(f39,plain,(
% 6.51/1.21    ((~v2_funct_1(sK5) | ~v2_funct_1(sK6)) & k1_relat_1(sK5) = k2_relat_1(sK6) & v2_funct_1(k5_relat_1(sK6,sK5)) & v1_funct_1(sK6) & v1_relat_1(sK6)) & v1_funct_1(sK5) & v1_relat_1(sK5)),
% 6.51/1.21    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f13,f38,f37])).
% 6.51/1.21  fof(f37,plain,(
% 6.51/1.21    ? [X0] : (? [X1] : ((~v2_funct_1(X0) | ~v2_funct_1(X1)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(k5_relat_1(X1,X0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : ((~v2_funct_1(sK5) | ~v2_funct_1(X1)) & k2_relat_1(X1) = k1_relat_1(sK5) & v2_funct_1(k5_relat_1(X1,sK5)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK5) & v1_relat_1(sK5))),
% 6.51/1.21    introduced(choice_axiom,[])).
% 6.51/1.21  fof(f38,plain,(
% 6.51/1.21    ? [X1] : ((~v2_funct_1(sK5) | ~v2_funct_1(X1)) & k2_relat_1(X1) = k1_relat_1(sK5) & v2_funct_1(k5_relat_1(X1,sK5)) & v1_funct_1(X1) & v1_relat_1(X1)) => ((~v2_funct_1(sK5) | ~v2_funct_1(sK6)) & k1_relat_1(sK5) = k2_relat_1(sK6) & v2_funct_1(k5_relat_1(sK6,sK5)) & v1_funct_1(sK6) & v1_relat_1(sK6))),
% 6.51/1.21    introduced(choice_axiom,[])).
% 6.51/1.21  fof(f13,plain,(
% 6.51/1.21    ? [X0] : (? [X1] : ((~v2_funct_1(X0) | ~v2_funct_1(X1)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(k5_relat_1(X1,X0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 6.51/1.21    inference(flattening,[],[f12])).
% 6.51/1.21  fof(f12,plain,(
% 6.51/1.21    ? [X0] : (? [X1] : (((~v2_funct_1(X0) | ~v2_funct_1(X1)) & (k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(k5_relat_1(X1,X0)))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 6.51/1.21    inference(ennf_transformation,[],[f11])).
% 6.51/1.21  fof(f11,negated_conjecture,(
% 6.51/1.21    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 6.51/1.21    inference(negated_conjecture,[],[f10])).
% 6.51/1.21  fof(f10,conjecture,(
% 6.51/1.21    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 6.51/1.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).
% 6.51/1.21  fof(f742,plain,(
% 6.51/1.21    ~v2_funct_1(k5_relat_1(sK6,sK5)) | sP0(k5_relat_1(sK6,sK5)) | (~spl11_24 | ~spl11_25)),
% 6.51/1.21    inference(resolution,[],[f740,f63])).
% 6.51/1.21  fof(f63,plain,(
% 6.51/1.21    ( ! [X0] : (~sP1(X0) | ~v2_funct_1(X0) | sP0(X0)) )),
% 6.51/1.21    inference(cnf_transformation,[],[f40])).
% 6.51/1.21  fof(f40,plain,(
% 6.51/1.21    ! [X0] : (((v2_funct_1(X0) | ~sP0(X0)) & (sP0(X0) | ~v2_funct_1(X0))) | ~sP1(X0))),
% 6.51/1.21    inference(nnf_transformation,[],[f31])).
% 6.51/1.21  fof(f31,plain,(
% 6.51/1.21    ! [X0] : ((v2_funct_1(X0) <=> sP0(X0)) | ~sP1(X0))),
% 6.51/1.21    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 6.51/1.21  fof(f740,plain,(
% 6.51/1.21    sP1(k5_relat_1(sK6,sK5)) | (~spl11_24 | ~spl11_25)),
% 6.51/1.21    inference(subsumption_resolution,[],[f736,f683])).
% 6.51/1.21  fof(f683,plain,(
% 6.51/1.21    v1_relat_1(k5_relat_1(sK6,sK5)) | ~spl11_24),
% 6.51/1.21    inference(avatar_component_clause,[],[f682])).
% 6.51/1.21  fof(f682,plain,(
% 6.51/1.21    spl11_24 <=> v1_relat_1(k5_relat_1(sK6,sK5))),
% 6.51/1.21    introduced(avatar_definition,[new_symbols(naming,[spl11_24])])).
% 6.51/1.21  fof(f736,plain,(
% 6.51/1.21    sP1(k5_relat_1(sK6,sK5)) | ~v1_relat_1(k5_relat_1(sK6,sK5)) | ~spl11_25),
% 6.51/1.21    inference(resolution,[],[f687,f70])).
% 6.51/1.21  fof(f70,plain,(
% 6.51/1.21    ( ! [X0] : (~v1_funct_1(X0) | sP1(X0) | ~v1_relat_1(X0)) )),
% 6.51/1.21    inference(cnf_transformation,[],[f32])).
% 6.51/1.21  fof(f32,plain,(
% 6.51/1.21    ! [X0] : (sP1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.51/1.21    inference(definition_folding,[],[f17,f31,f30])).
% 6.51/1.21  fof(f30,plain,(
% 6.51/1.21    ! [X0] : (sP0(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))),
% 6.51/1.21    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 6.51/1.21  fof(f17,plain,(
% 6.51/1.21    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.51/1.21    inference(flattening,[],[f16])).
% 6.51/1.21  fof(f16,plain,(
% 6.51/1.21    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 6.51/1.21    inference(ennf_transformation,[],[f5])).
% 6.51/1.21  fof(f5,axiom,(
% 6.51/1.21    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 6.51/1.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).
% 6.51/1.21  fof(f687,plain,(
% 6.51/1.21    v1_funct_1(k5_relat_1(sK6,sK5)) | ~spl11_25),
% 6.51/1.21    inference(avatar_component_clause,[],[f686])).
% 6.51/1.21  fof(f686,plain,(
% 6.51/1.21    spl11_25 <=> v1_funct_1(k5_relat_1(sK6,sK5))),
% 6.51/1.21    introduced(avatar_definition,[new_symbols(naming,[spl11_25])])).
% 6.51/1.21  fof(f195,plain,(
% 6.51/1.21    ~sP0(k5_relat_1(sK6,sK5)) | spl11_6),
% 6.51/1.21    inference(avatar_component_clause,[],[f194])).
% 6.51/1.21  fof(f194,plain,(
% 6.51/1.21    spl11_6 <=> sP0(k5_relat_1(sK6,sK5))),
% 6.51/1.21    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).
% 6.51/1.21  fof(f5346,plain,(
% 6.51/1.21    spl11_3 | ~spl11_6 | ~spl11_37 | ~spl11_50),
% 6.51/1.21    inference(avatar_contradiction_clause,[],[f5345])).
% 6.51/1.21  fof(f5345,plain,(
% 6.51/1.21    $false | (spl11_3 | ~spl11_6 | ~spl11_37 | ~spl11_50)),
% 6.51/1.21    inference(subsumption_resolution,[],[f5344,f110])).
% 6.51/1.21  fof(f110,plain,(
% 6.51/1.21    ~sP0(sK5) | spl11_3),
% 6.51/1.21    inference(avatar_component_clause,[],[f108])).
% 6.51/1.21  fof(f108,plain,(
% 6.51/1.21    spl11_3 <=> sP0(sK5)),
% 6.51/1.21    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).
% 6.51/1.21  fof(f5344,plain,(
% 6.51/1.21    sP0(sK5) | (spl11_3 | ~spl11_6 | ~spl11_37 | ~spl11_50)),
% 6.51/1.21    inference(trivial_inequality_removal,[],[f5342])).
% 6.51/1.21  fof(f5342,plain,(
% 6.51/1.21    sK7(sK5) != sK7(sK5) | sP0(sK5) | (spl11_3 | ~spl11_6 | ~spl11_37 | ~spl11_50)),
% 6.51/1.21    inference(superposition,[],[f69,f5218])).
% 6.51/1.21  fof(f5218,plain,(
% 6.51/1.21    sK7(sK5) = sK8(sK5) | (spl11_3 | ~spl11_6 | ~spl11_37 | ~spl11_50)),
% 6.51/1.21    inference(forward_demodulation,[],[f5193,f139])).
% 6.51/1.21  fof(f139,plain,(
% 6.51/1.21    sK7(sK5) = k1_funct_1(sK6,sK10(sK7(sK5),sK6)) | spl11_3),
% 6.51/1.21    inference(resolution,[],[f80,f133])).
% 6.51/1.21  fof(f133,plain,(
% 6.51/1.21    sP2(sK7(sK5),sK6) | spl11_3),
% 6.51/1.21    inference(subsumption_resolution,[],[f130,f116])).
% 6.51/1.21  fof(f116,plain,(
% 6.51/1.21    sP4(sK6)),
% 6.51/1.21    inference(subsumption_resolution,[],[f114,f56])).
% 6.51/1.21  fof(f56,plain,(
% 6.51/1.21    v1_relat_1(sK6)),
% 6.51/1.21    inference(cnf_transformation,[],[f39])).
% 6.51/1.21  fof(f114,plain,(
% 6.51/1.21    sP4(sK6) | ~v1_relat_1(sK6)),
% 6.51/1.21    inference(resolution,[],[f82,f57])).
% 6.51/1.21  fof(f57,plain,(
% 6.51/1.21    v1_funct_1(sK6)),
% 6.51/1.21    inference(cnf_transformation,[],[f39])).
% 6.51/1.21  fof(f82,plain,(
% 6.51/1.21    ( ! [X0] : (~v1_funct_1(X0) | sP4(X0) | ~v1_relat_1(X0)) )),
% 6.51/1.21    inference(cnf_transformation,[],[f36])).
% 6.51/1.21  fof(f36,plain,(
% 6.51/1.21    ! [X0] : (sP4(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.51/1.21    inference(definition_folding,[],[f23,f35,f34,f33])).
% 6.51/1.21  fof(f33,plain,(
% 6.51/1.21    ! [X2,X0] : (sP2(X2,X0) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))),
% 6.51/1.21    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 6.51/1.21  fof(f34,plain,(
% 6.51/1.21    ! [X0,X1] : (sP3(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> sP2(X2,X0)))),
% 6.51/1.21    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 6.51/1.21  fof(f35,plain,(
% 6.51/1.21    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> sP3(X0,X1)) | ~sP4(X0))),
% 6.51/1.21    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 6.51/1.21  fof(f23,plain,(
% 6.51/1.21    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.51/1.21    inference(flattening,[],[f22])).
% 6.51/1.21  fof(f22,plain,(
% 6.51/1.21    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 6.51/1.21    inference(ennf_transformation,[],[f4])).
% 6.51/1.21  fof(f4,axiom,(
% 6.51/1.21    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 6.51/1.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 6.51/1.21  fof(f130,plain,(
% 6.51/1.21    sP2(sK7(sK5),sK6) | ~sP4(sK6) | spl11_3),
% 6.51/1.21    inference(resolution,[],[f127,f118])).
% 6.51/1.21  fof(f118,plain,(
% 6.51/1.21    r2_hidden(sK7(sK5),k2_relat_1(sK6)) | spl11_3),
% 6.51/1.21    inference(subsumption_resolution,[],[f117,f110])).
% 6.51/1.21  fof(f117,plain,(
% 6.51/1.21    r2_hidden(sK7(sK5),k2_relat_1(sK6)) | sP0(sK5)),
% 6.51/1.21    inference(superposition,[],[f66,f59])).
% 6.51/1.21  fof(f59,plain,(
% 6.51/1.21    k1_relat_1(sK5) = k2_relat_1(sK6)),
% 6.51/1.21    inference(cnf_transformation,[],[f39])).
% 6.51/1.21  fof(f66,plain,(
% 6.51/1.21    ( ! [X0] : (r2_hidden(sK7(X0),k1_relat_1(X0)) | sP0(X0)) )),
% 6.51/1.21    inference(cnf_transformation,[],[f44])).
% 6.51/1.21  fof(f44,plain,(
% 6.51/1.21    ! [X0] : ((sP0(X0) | (sK7(X0) != sK8(X0) & k1_funct_1(X0,sK7(X0)) = k1_funct_1(X0,sK8(X0)) & r2_hidden(sK8(X0),k1_relat_1(X0)) & r2_hidden(sK7(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X0)))),
% 6.51/1.21    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f42,f43])).
% 6.51/1.21  fof(f43,plain,(
% 6.51/1.21    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK7(X0) != sK8(X0) & k1_funct_1(X0,sK7(X0)) = k1_funct_1(X0,sK8(X0)) & r2_hidden(sK8(X0),k1_relat_1(X0)) & r2_hidden(sK7(X0),k1_relat_1(X0))))),
% 6.51/1.21    introduced(choice_axiom,[])).
% 6.51/1.21  fof(f42,plain,(
% 6.51/1.21    ! [X0] : ((sP0(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X0)))),
% 6.51/1.21    inference(rectify,[],[f41])).
% 6.51/1.21  fof(f41,plain,(
% 6.51/1.21    ! [X0] : ((sP0(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~sP0(X0)))),
% 6.51/1.21    inference(nnf_transformation,[],[f30])).
% 6.51/1.21  fof(f127,plain,(
% 6.51/1.21    ( ! [X0,X1] : (~r2_hidden(X0,k2_relat_1(X1)) | sP2(X0,X1) | ~sP4(X1)) )),
% 6.51/1.21    inference(resolution,[],[f75,f87])).
% 6.51/1.21  fof(f87,plain,(
% 6.51/1.21    ( ! [X0] : (sP3(X0,k2_relat_1(X0)) | ~sP4(X0)) )),
% 6.51/1.21    inference(equality_resolution,[],[f73])).
% 6.51/1.21  fof(f73,plain,(
% 6.51/1.21    ( ! [X0,X1] : (sP3(X0,X1) | k2_relat_1(X0) != X1 | ~sP4(X0)) )),
% 6.51/1.21    inference(cnf_transformation,[],[f45])).
% 6.51/1.21  fof(f45,plain,(
% 6.51/1.21    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ~sP3(X0,X1)) & (sP3(X0,X1) | k2_relat_1(X0) != X1)) | ~sP4(X0))),
% 6.51/1.21    inference(nnf_transformation,[],[f35])).
% 6.51/1.21  fof(f75,plain,(
% 6.51/1.21    ( ! [X0,X3,X1] : (~sP3(X0,X1) | ~r2_hidden(X3,X1) | sP2(X3,X0)) )),
% 6.51/1.21    inference(cnf_transformation,[],[f49])).
% 6.51/1.21  fof(f49,plain,(
% 6.51/1.21    ! [X0,X1] : ((sP3(X0,X1) | ((~sP2(sK9(X0,X1),X0) | ~r2_hidden(sK9(X0,X1),X1)) & (sP2(sK9(X0,X1),X0) | r2_hidden(sK9(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~sP2(X3,X0)) & (sP2(X3,X0) | ~r2_hidden(X3,X1))) | ~sP3(X0,X1)))),
% 6.51/1.21    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f47,f48])).
% 6.51/1.21  fof(f48,plain,(
% 6.51/1.21    ! [X1,X0] : (? [X2] : ((~sP2(X2,X0) | ~r2_hidden(X2,X1)) & (sP2(X2,X0) | r2_hidden(X2,X1))) => ((~sP2(sK9(X0,X1),X0) | ~r2_hidden(sK9(X0,X1),X1)) & (sP2(sK9(X0,X1),X0) | r2_hidden(sK9(X0,X1),X1))))),
% 6.51/1.21    introduced(choice_axiom,[])).
% 6.51/1.21  fof(f47,plain,(
% 6.51/1.21    ! [X0,X1] : ((sP3(X0,X1) | ? [X2] : ((~sP2(X2,X0) | ~r2_hidden(X2,X1)) & (sP2(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~sP2(X3,X0)) & (sP2(X3,X0) | ~r2_hidden(X3,X1))) | ~sP3(X0,X1)))),
% 6.51/1.21    inference(rectify,[],[f46])).
% 6.51/1.21  fof(f46,plain,(
% 6.51/1.21    ! [X0,X1] : ((sP3(X0,X1) | ? [X2] : ((~sP2(X2,X0) | ~r2_hidden(X2,X1)) & (sP2(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~sP2(X2,X0)) & (sP2(X2,X0) | ~r2_hidden(X2,X1))) | ~sP3(X0,X1)))),
% 6.51/1.21    inference(nnf_transformation,[],[f34])).
% 6.51/1.21  fof(f80,plain,(
% 6.51/1.21    ( ! [X0,X1] : (~sP2(X0,X1) | k1_funct_1(X1,sK10(X0,X1)) = X0) )),
% 6.51/1.21    inference(cnf_transformation,[],[f53])).
% 6.51/1.21  fof(f53,plain,(
% 6.51/1.21    ! [X0,X1] : ((sP2(X0,X1) | ! [X2] : (k1_funct_1(X1,X2) != X0 | ~r2_hidden(X2,k1_relat_1(X1)))) & ((k1_funct_1(X1,sK10(X0,X1)) = X0 & r2_hidden(sK10(X0,X1),k1_relat_1(X1))) | ~sP2(X0,X1)))),
% 6.51/1.21    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f51,f52])).
% 6.51/1.21  fof(f52,plain,(
% 6.51/1.21    ! [X1,X0] : (? [X3] : (k1_funct_1(X1,X3) = X0 & r2_hidden(X3,k1_relat_1(X1))) => (k1_funct_1(X1,sK10(X0,X1)) = X0 & r2_hidden(sK10(X0,X1),k1_relat_1(X1))))),
% 6.51/1.21    introduced(choice_axiom,[])).
% 6.51/1.21  fof(f51,plain,(
% 6.51/1.21    ! [X0,X1] : ((sP2(X0,X1) | ! [X2] : (k1_funct_1(X1,X2) != X0 | ~r2_hidden(X2,k1_relat_1(X1)))) & (? [X3] : (k1_funct_1(X1,X3) = X0 & r2_hidden(X3,k1_relat_1(X1))) | ~sP2(X0,X1)))),
% 6.51/1.21    inference(rectify,[],[f50])).
% 6.51/1.21  fof(f50,plain,(
% 6.51/1.21    ! [X2,X0] : ((sP2(X2,X0) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~sP2(X2,X0)))),
% 6.51/1.21    inference(nnf_transformation,[],[f33])).
% 6.51/1.21  fof(f5193,plain,(
% 6.51/1.21    sK8(sK5) = k1_funct_1(sK6,sK10(sK7(sK5),sK6)) | (spl11_3 | ~spl11_6 | ~spl11_37 | ~spl11_50)),
% 6.51/1.21    inference(backward_demodulation,[],[f140,f5190])).
% 6.51/1.21  fof(f5190,plain,(
% 6.51/1.21    sK10(sK7(sK5),sK6) = sK10(sK8(sK5),sK6) | (spl11_3 | ~spl11_6 | ~spl11_37 | ~spl11_50)),
% 6.51/1.21    inference(subsumption_resolution,[],[f5189,f1099])).
% 6.51/1.21  fof(f1099,plain,(
% 6.51/1.21    r2_hidden(sK10(sK7(sK5),sK6),k1_relat_1(sK6)) | ~spl11_37),
% 6.51/1.21    inference(avatar_component_clause,[],[f1098])).
% 6.51/1.21  fof(f1098,plain,(
% 6.51/1.21    spl11_37 <=> r2_hidden(sK10(sK7(sK5),sK6),k1_relat_1(sK6))),
% 6.51/1.21    introduced(avatar_definition,[new_symbols(naming,[spl11_37])])).
% 6.51/1.21  fof(f5189,plain,(
% 6.51/1.21    ~r2_hidden(sK10(sK7(sK5),sK6),k1_relat_1(sK6)) | sK10(sK7(sK5),sK6) = sK10(sK8(sK5),sK6) | (spl11_3 | ~spl11_6 | ~spl11_50)),
% 6.51/1.21    inference(trivial_inequality_removal,[],[f5185])).
% 6.51/1.21  fof(f5185,plain,(
% 6.51/1.21    k1_funct_1(sK5,sK7(sK5)) != k1_funct_1(sK5,sK7(sK5)) | ~r2_hidden(sK10(sK7(sK5),sK6),k1_relat_1(sK6)) | sK10(sK7(sK5),sK6) = sK10(sK8(sK5),sK6) | (spl11_3 | ~spl11_6 | ~spl11_50)),
% 6.51/1.21    inference(superposition,[],[f5096,f1076])).
% 6.51/1.21  fof(f1076,plain,(
% 6.51/1.21    k1_funct_1(sK5,sK7(sK5)) = k1_funct_1(k5_relat_1(sK6,sK5),sK10(sK7(sK5),sK6)) | spl11_3),
% 6.51/1.21    inference(subsumption_resolution,[],[f1072,f54])).
% 6.51/1.21  fof(f54,plain,(
% 6.51/1.21    v1_relat_1(sK5)),
% 6.51/1.21    inference(cnf_transformation,[],[f39])).
% 6.51/1.21  fof(f1072,plain,(
% 6.51/1.21    k1_funct_1(sK5,sK7(sK5)) = k1_funct_1(k5_relat_1(sK6,sK5),sK10(sK7(sK5),sK6)) | ~v1_relat_1(sK5) | spl11_3),
% 6.51/1.21    inference(resolution,[],[f1059,f55])).
% 6.51/1.21  fof(f55,plain,(
% 6.51/1.21    v1_funct_1(sK5)),
% 6.51/1.21    inference(cnf_transformation,[],[f39])).
% 6.51/1.21  fof(f1059,plain,(
% 6.51/1.21    ( ! [X6] : (~v1_funct_1(X6) | k1_funct_1(k5_relat_1(sK6,X6),sK10(sK7(sK5),sK6)) = k1_funct_1(X6,sK7(sK5)) | ~v1_relat_1(X6)) ) | spl11_3),
% 6.51/1.21    inference(forward_demodulation,[],[f1058,f139])).
% 6.51/1.21  fof(f1058,plain,(
% 6.51/1.21    ( ! [X6] : (~v1_funct_1(X6) | ~v1_relat_1(X6) | k1_funct_1(k5_relat_1(sK6,X6),sK10(sK7(sK5),sK6)) = k1_funct_1(X6,k1_funct_1(sK6,sK10(sK7(sK5),sK6)))) ) | spl11_3),
% 6.51/1.21    inference(subsumption_resolution,[],[f1057,f56])).
% 6.51/1.21  fof(f1057,plain,(
% 6.51/1.21    ( ! [X6] : (~v1_funct_1(X6) | ~v1_relat_1(X6) | ~v1_relat_1(sK6) | k1_funct_1(k5_relat_1(sK6,X6),sK10(sK7(sK5),sK6)) = k1_funct_1(X6,k1_funct_1(sK6,sK10(sK7(sK5),sK6)))) ) | spl11_3),
% 6.51/1.21    inference(subsumption_resolution,[],[f1040,f57])).
% 6.51/1.21  fof(f1040,plain,(
% 6.51/1.21    ( ! [X6] : (~v1_funct_1(X6) | ~v1_relat_1(X6) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | k1_funct_1(k5_relat_1(sK6,X6),sK10(sK7(sK5),sK6)) = k1_funct_1(X6,k1_funct_1(sK6,sK10(sK7(sK5),sK6)))) ) | spl11_3),
% 6.51/1.21    inference(resolution,[],[f482,f133])).
% 6.51/1.21  fof(f482,plain,(
% 6.51/1.21    ( ! [X8,X7,X9] : (~sP2(X9,X7) | ~v1_funct_1(X8) | ~v1_relat_1(X8) | ~v1_funct_1(X7) | ~v1_relat_1(X7) | k1_funct_1(k5_relat_1(X7,X8),sK10(X9,X7)) = k1_funct_1(X8,k1_funct_1(X7,sK10(X9,X7)))) )),
% 6.51/1.21    inference(resolution,[],[f85,f79])).
% 6.51/1.21  fof(f79,plain,(
% 6.51/1.21    ( ! [X0,X1] : (r2_hidden(sK10(X0,X1),k1_relat_1(X1)) | ~sP2(X0,X1)) )),
% 6.51/1.21    inference(cnf_transformation,[],[f53])).
% 6.51/1.21  fof(f85,plain,(
% 6.51/1.21    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(X1)) | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 6.51/1.21    inference(cnf_transformation,[],[f27])).
% 6.51/1.21  fof(f27,plain,(
% 6.51/1.21    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 6.51/1.21    inference(flattening,[],[f26])).
% 6.51/1.21  fof(f26,plain,(
% 6.51/1.21    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 6.51/1.21    inference(ennf_transformation,[],[f7])).
% 6.51/1.21  fof(f7,axiom,(
% 6.51/1.21    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)))))),
% 6.51/1.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).
% 6.51/1.21  fof(f5096,plain,(
% 6.51/1.21    ( ! [X0] : (k1_funct_1(sK5,sK7(sK5)) != k1_funct_1(k5_relat_1(sK6,sK5),X0) | ~r2_hidden(X0,k1_relat_1(sK6)) | sK10(sK8(sK5),sK6) = X0) ) | (spl11_3 | ~spl11_6 | ~spl11_50)),
% 6.51/1.21    inference(forward_demodulation,[],[f5095,f189])).
% 6.51/1.21  fof(f189,plain,(
% 6.51/1.21    k1_relat_1(sK6) = k1_relat_1(k5_relat_1(sK6,sK5))),
% 6.51/1.21    inference(forward_demodulation,[],[f186,f122])).
% 6.51/1.21  fof(f122,plain,(
% 6.51/1.21    k10_relat_1(sK6,k2_relat_1(sK6)) = k1_relat_1(sK6)),
% 6.51/1.21    inference(resolution,[],[f61,f56])).
% 6.51/1.21  fof(f61,plain,(
% 6.51/1.21    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 6.51/1.21    inference(cnf_transformation,[],[f14])).
% 6.51/1.21  fof(f14,plain,(
% 6.51/1.21    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 6.51/1.21    inference(ennf_transformation,[],[f2])).
% 6.51/1.21  fof(f2,axiom,(
% 6.51/1.21    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 6.51/1.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 6.51/1.21  fof(f186,plain,(
% 6.51/1.21    k10_relat_1(sK6,k2_relat_1(sK6)) = k1_relat_1(k5_relat_1(sK6,sK5))),
% 6.51/1.21    inference(resolution,[],[f180,f56])).
% 6.51/1.21  fof(f180,plain,(
% 6.51/1.21    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(k5_relat_1(X0,sK5)) = k10_relat_1(X0,k2_relat_1(sK6))) )),
% 6.51/1.21    inference(forward_demodulation,[],[f176,f59])).
% 6.51/1.21  fof(f176,plain,(
% 6.51/1.21    ( ! [X0] : (k1_relat_1(k5_relat_1(X0,sK5)) = k10_relat_1(X0,k1_relat_1(sK5)) | ~v1_relat_1(X0)) )),
% 6.51/1.21    inference(resolution,[],[f62,f54])).
% 6.51/1.21  fof(f62,plain,(
% 6.51/1.21    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 6.51/1.21    inference(cnf_transformation,[],[f15])).
% 6.51/1.21  fof(f15,plain,(
% 6.51/1.21    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 6.51/1.21    inference(ennf_transformation,[],[f3])).
% 6.51/1.21  fof(f3,axiom,(
% 6.51/1.21    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 6.51/1.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 6.51/1.21  fof(f5095,plain,(
% 6.51/1.21    ( ! [X0] : (k1_funct_1(sK5,sK7(sK5)) != k1_funct_1(k5_relat_1(sK6,sK5),X0) | sK10(sK8(sK5),sK6) = X0 | ~r2_hidden(X0,k1_relat_1(k5_relat_1(sK6,sK5)))) ) | (spl11_3 | ~spl11_6 | ~spl11_50)),
% 6.51/1.21    inference(subsumption_resolution,[],[f5094,f2003])).
% 6.51/1.21  fof(f2003,plain,(
% 6.51/1.21    r2_hidden(sK10(sK8(sK5),sK6),k1_relat_1(sK6)) | ~spl11_50),
% 6.51/1.21    inference(avatar_component_clause,[],[f2002])).
% 6.51/1.21  fof(f2002,plain,(
% 6.51/1.21    spl11_50 <=> r2_hidden(sK10(sK8(sK5),sK6),k1_relat_1(sK6))),
% 6.51/1.21    introduced(avatar_definition,[new_symbols(naming,[spl11_50])])).
% 6.51/1.21  fof(f5094,plain,(
% 6.51/1.21    ( ! [X0] : (~r2_hidden(sK10(sK8(sK5),sK6),k1_relat_1(sK6)) | k1_funct_1(sK5,sK7(sK5)) != k1_funct_1(k5_relat_1(sK6,sK5),X0) | sK10(sK8(sK5),sK6) = X0 | ~r2_hidden(X0,k1_relat_1(k5_relat_1(sK6,sK5)))) ) | (spl11_3 | ~spl11_6)),
% 6.51/1.21    inference(forward_demodulation,[],[f5093,f189])).
% 6.51/1.21  fof(f5093,plain,(
% 6.51/1.21    ( ! [X0] : (k1_funct_1(sK5,sK7(sK5)) != k1_funct_1(k5_relat_1(sK6,sK5),X0) | sK10(sK8(sK5),sK6) = X0 | ~r2_hidden(sK10(sK8(sK5),sK6),k1_relat_1(k5_relat_1(sK6,sK5))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(sK6,sK5)))) ) | (spl11_3 | ~spl11_6)),
% 6.51/1.21    inference(subsumption_resolution,[],[f5090,f196])).
% 6.51/1.21  fof(f196,plain,(
% 6.51/1.21    sP0(k5_relat_1(sK6,sK5)) | ~spl11_6),
% 6.51/1.21    inference(avatar_component_clause,[],[f194])).
% 6.51/1.21  fof(f5090,plain,(
% 6.51/1.21    ( ! [X0] : (k1_funct_1(sK5,sK7(sK5)) != k1_funct_1(k5_relat_1(sK6,sK5),X0) | sK10(sK8(sK5),sK6) = X0 | ~r2_hidden(sK10(sK8(sK5),sK6),k1_relat_1(k5_relat_1(sK6,sK5))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(sK6,sK5))) | ~sP0(k5_relat_1(sK6,sK5))) ) | spl11_3),
% 6.51/1.21    inference(superposition,[],[f65,f1125])).
% 6.51/1.21  fof(f1125,plain,(
% 6.51/1.21    k1_funct_1(sK5,sK7(sK5)) = k1_funct_1(k5_relat_1(sK6,sK5),sK10(sK8(sK5),sK6)) | spl11_3),
% 6.51/1.21    inference(forward_demodulation,[],[f1124,f145])).
% 6.51/1.21  fof(f145,plain,(
% 6.51/1.21    k1_funct_1(sK5,sK7(sK5)) = k1_funct_1(sK5,sK8(sK5)) | spl11_3),
% 6.51/1.21    inference(resolution,[],[f68,f110])).
% 6.51/1.21  fof(f68,plain,(
% 6.51/1.21    ( ! [X0] : (sP0(X0) | k1_funct_1(X0,sK7(X0)) = k1_funct_1(X0,sK8(X0))) )),
% 6.51/1.21    inference(cnf_transformation,[],[f44])).
% 6.51/1.21  fof(f1124,plain,(
% 6.51/1.21    k1_funct_1(sK5,sK8(sK5)) = k1_funct_1(k5_relat_1(sK6,sK5),sK10(sK8(sK5),sK6)) | spl11_3),
% 6.51/1.21    inference(subsumption_resolution,[],[f1120,f54])).
% 6.51/1.21  fof(f1120,plain,(
% 6.51/1.21    k1_funct_1(sK5,sK8(sK5)) = k1_funct_1(k5_relat_1(sK6,sK5),sK10(sK8(sK5),sK6)) | ~v1_relat_1(sK5) | spl11_3),
% 6.51/1.21    inference(resolution,[],[f1062,f55])).
% 6.51/1.21  fof(f1062,plain,(
% 6.51/1.21    ( ! [X7] : (~v1_funct_1(X7) | k1_funct_1(k5_relat_1(sK6,X7),sK10(sK8(sK5),sK6)) = k1_funct_1(X7,sK8(sK5)) | ~v1_relat_1(X7)) ) | spl11_3),
% 6.51/1.21    inference(forward_demodulation,[],[f1061,f140])).
% 6.51/1.21  fof(f1061,plain,(
% 6.51/1.21    ( ! [X7] : (~v1_funct_1(X7) | ~v1_relat_1(X7) | k1_funct_1(k5_relat_1(sK6,X7),sK10(sK8(sK5),sK6)) = k1_funct_1(X7,k1_funct_1(sK6,sK10(sK8(sK5),sK6)))) ) | spl11_3),
% 6.51/1.21    inference(subsumption_resolution,[],[f1060,f56])).
% 6.51/1.21  fof(f1060,plain,(
% 6.51/1.21    ( ! [X7] : (~v1_funct_1(X7) | ~v1_relat_1(X7) | ~v1_relat_1(sK6) | k1_funct_1(k5_relat_1(sK6,X7),sK10(sK8(sK5),sK6)) = k1_funct_1(X7,k1_funct_1(sK6,sK10(sK8(sK5),sK6)))) ) | spl11_3),
% 6.51/1.21    inference(subsumption_resolution,[],[f1041,f57])).
% 6.51/1.21  fof(f1041,plain,(
% 6.51/1.21    ( ! [X7] : (~v1_funct_1(X7) | ~v1_relat_1(X7) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | k1_funct_1(k5_relat_1(sK6,X7),sK10(sK8(sK5),sK6)) = k1_funct_1(X7,k1_funct_1(sK6,sK10(sK8(sK5),sK6)))) ) | spl11_3),
% 6.51/1.21    inference(resolution,[],[f482,f134])).
% 6.51/1.21  fof(f134,plain,(
% 6.51/1.21    sP2(sK8(sK5),sK6) | spl11_3),
% 6.51/1.21    inference(subsumption_resolution,[],[f131,f116])).
% 6.51/1.21  fof(f131,plain,(
% 6.51/1.21    sP2(sK8(sK5),sK6) | ~sP4(sK6) | spl11_3),
% 6.51/1.21    inference(resolution,[],[f127,f120])).
% 6.51/1.21  fof(f120,plain,(
% 6.51/1.21    r2_hidden(sK8(sK5),k2_relat_1(sK6)) | spl11_3),
% 6.51/1.21    inference(subsumption_resolution,[],[f119,f110])).
% 6.51/1.21  fof(f119,plain,(
% 6.51/1.21    r2_hidden(sK8(sK5),k2_relat_1(sK6)) | sP0(sK5)),
% 6.51/1.21    inference(superposition,[],[f67,f59])).
% 6.51/1.21  fof(f67,plain,(
% 6.51/1.21    ( ! [X0] : (r2_hidden(sK8(X0),k1_relat_1(X0)) | sP0(X0)) )),
% 6.51/1.21    inference(cnf_transformation,[],[f44])).
% 6.51/1.21  fof(f65,plain,(
% 6.51/1.21    ( ! [X4,X0,X3] : (k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | X3 = X4 | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0)) | ~sP0(X0)) )),
% 6.51/1.21    inference(cnf_transformation,[],[f44])).
% 6.51/1.21  fof(f140,plain,(
% 6.51/1.21    sK8(sK5) = k1_funct_1(sK6,sK10(sK8(sK5),sK6)) | spl11_3),
% 6.51/1.21    inference(resolution,[],[f80,f134])).
% 6.51/1.21  fof(f69,plain,(
% 6.51/1.21    ( ! [X0] : (sK7(X0) != sK8(X0) | sP0(X0)) )),
% 6.51/1.21    inference(cnf_transformation,[],[f44])).
% 6.51/1.21  fof(f2012,plain,(
% 6.51/1.21    spl11_3 | spl11_50),
% 6.51/1.21    inference(avatar_contradiction_clause,[],[f2011])).
% 6.51/1.21  fof(f2011,plain,(
% 6.51/1.21    $false | (spl11_3 | spl11_50)),
% 6.51/1.21    inference(subsumption_resolution,[],[f2010,f134])).
% 6.51/1.21  fof(f2010,plain,(
% 6.51/1.21    ~sP2(sK8(sK5),sK6) | spl11_50),
% 6.51/1.21    inference(resolution,[],[f2004,f79])).
% 6.51/1.21  fof(f2004,plain,(
% 6.51/1.21    ~r2_hidden(sK10(sK8(sK5),sK6),k1_relat_1(sK6)) | spl11_50),
% 6.51/1.21    inference(avatar_component_clause,[],[f2002])).
% 6.51/1.21  fof(f1104,plain,(
% 6.51/1.21    spl11_3 | spl11_37),
% 6.51/1.21    inference(avatar_contradiction_clause,[],[f1103])).
% 6.51/1.21  fof(f1103,plain,(
% 6.51/1.21    $false | (spl11_3 | spl11_37)),
% 6.51/1.21    inference(subsumption_resolution,[],[f1102,f133])).
% 6.51/1.21  fof(f1102,plain,(
% 6.51/1.21    ~sP2(sK7(sK5),sK6) | spl11_37),
% 6.51/1.21    inference(resolution,[],[f1100,f79])).
% 6.51/1.21  fof(f1100,plain,(
% 6.51/1.21    ~r2_hidden(sK10(sK7(sK5),sK6),k1_relat_1(sK6)) | spl11_37),
% 6.51/1.21    inference(avatar_component_clause,[],[f1098])).
% 6.51/1.21  fof(f728,plain,(
% 6.51/1.21    spl11_25),
% 6.51/1.21    inference(avatar_contradiction_clause,[],[f727])).
% 6.51/1.21  fof(f727,plain,(
% 6.51/1.21    $false | spl11_25),
% 6.51/1.21    inference(subsumption_resolution,[],[f726,f56])).
% 6.51/1.21  fof(f726,plain,(
% 6.51/1.21    ~v1_relat_1(sK6) | spl11_25),
% 6.51/1.21    inference(subsumption_resolution,[],[f725,f57])).
% 6.51/1.21  fof(f725,plain,(
% 6.51/1.21    ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | spl11_25),
% 6.51/1.21    inference(subsumption_resolution,[],[f724,f54])).
% 6.51/1.21  fof(f724,plain,(
% 6.51/1.21    ~v1_relat_1(sK5) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | spl11_25),
% 6.51/1.21    inference(subsumption_resolution,[],[f723,f55])).
% 6.51/1.21  fof(f723,plain,(
% 6.51/1.21    ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | spl11_25),
% 6.51/1.21    inference(resolution,[],[f688,f84])).
% 6.51/1.21  fof(f84,plain,(
% 6.51/1.21    ( ! [X0,X1] : (v1_funct_1(k5_relat_1(X0,X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.51/1.21    inference(cnf_transformation,[],[f25])).
% 6.51/1.21  fof(f25,plain,(
% 6.51/1.21    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.51/1.21    inference(flattening,[],[f24])).
% 6.51/1.21  fof(f24,plain,(
% 6.51/1.21    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 6.51/1.21    inference(ennf_transformation,[],[f6])).
% 6.51/1.21  fof(f6,axiom,(
% 6.51/1.21    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1) & v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))))),
% 6.51/1.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).
% 6.51/1.21  fof(f688,plain,(
% 6.51/1.21    ~v1_funct_1(k5_relat_1(sK6,sK5)) | spl11_25),
% 6.51/1.21    inference(avatar_component_clause,[],[f686])).
% 6.51/1.21  fof(f699,plain,(
% 6.51/1.21    spl11_24),
% 6.51/1.21    inference(avatar_contradiction_clause,[],[f698])).
% 6.51/1.21  fof(f698,plain,(
% 6.51/1.21    $false | spl11_24),
% 6.51/1.21    inference(subsumption_resolution,[],[f697,f56])).
% 6.51/1.21  fof(f697,plain,(
% 6.51/1.21    ~v1_relat_1(sK6) | spl11_24),
% 6.51/1.21    inference(subsumption_resolution,[],[f691,f54])).
% 6.51/1.21  fof(f691,plain,(
% 6.51/1.21    ~v1_relat_1(sK5) | ~v1_relat_1(sK6) | spl11_24),
% 6.51/1.21    inference(resolution,[],[f684,f86])).
% 6.51/1.21  fof(f86,plain,(
% 6.51/1.21    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 6.51/1.21    inference(cnf_transformation,[],[f29])).
% 6.51/1.21  fof(f29,plain,(
% 6.51/1.21    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 6.51/1.21    inference(flattening,[],[f28])).
% 6.51/1.21  fof(f28,plain,(
% 6.51/1.21    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 6.51/1.21    inference(ennf_transformation,[],[f1])).
% 6.51/1.21  fof(f1,axiom,(
% 6.51/1.21    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 6.51/1.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 6.51/1.21  fof(f684,plain,(
% 6.51/1.21    ~v1_relat_1(k5_relat_1(sK6,sK5)) | spl11_24),
% 6.51/1.21    inference(avatar_component_clause,[],[f682])).
% 6.51/1.21  fof(f410,plain,(
% 6.51/1.21    spl11_1),
% 6.51/1.21    inference(avatar_contradiction_clause,[],[f409])).
% 6.51/1.21  fof(f409,plain,(
% 6.51/1.21    $false | spl11_1),
% 6.51/1.21    inference(subsumption_resolution,[],[f408,f56])).
% 6.51/1.21  fof(f408,plain,(
% 6.51/1.21    ~v1_relat_1(sK6) | spl11_1),
% 6.51/1.21    inference(subsumption_resolution,[],[f407,f57])).
% 6.51/1.21  fof(f407,plain,(
% 6.51/1.21    ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | spl11_1),
% 6.51/1.21    inference(subsumption_resolution,[],[f406,f58])).
% 6.51/1.21  fof(f406,plain,(
% 6.51/1.21    ~v2_funct_1(k5_relat_1(sK6,sK5)) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | spl11_1),
% 6.51/1.21    inference(subsumption_resolution,[],[f405,f92])).
% 6.51/1.21  fof(f92,plain,(
% 6.51/1.21    ~v2_funct_1(sK6) | spl11_1),
% 6.51/1.21    inference(avatar_component_clause,[],[f90])).
% 6.51/1.21  fof(f90,plain,(
% 6.51/1.21    spl11_1 <=> v2_funct_1(sK6)),
% 6.51/1.21    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 6.51/1.21  fof(f405,plain,(
% 6.51/1.21    v2_funct_1(sK6) | ~v2_funct_1(k5_relat_1(sK6,sK5)) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6)),
% 6.51/1.21    inference(resolution,[],[f388,f235])).
% 6.51/1.21  fof(f235,plain,(
% 6.51/1.21    ( ! [X0] : (~r1_tarski(k2_relat_1(X0),k2_relat_1(sK6)) | v2_funct_1(X0) | ~v2_funct_1(k5_relat_1(X0,sK5)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.51/1.21    inference(subsumption_resolution,[],[f234,f54])).
% 6.51/1.21  fof(f234,plain,(
% 6.51/1.21    ( ! [X0] : (~r1_tarski(k2_relat_1(X0),k2_relat_1(sK6)) | v2_funct_1(X0) | ~v2_funct_1(k5_relat_1(X0,sK5)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(sK5)) )),
% 6.51/1.21    inference(subsumption_resolution,[],[f232,f55])).
% 6.51/1.21  fof(f232,plain,(
% 6.51/1.21    ( ! [X0] : (~r1_tarski(k2_relat_1(X0),k2_relat_1(sK6)) | v2_funct_1(X0) | ~v2_funct_1(k5_relat_1(X0,sK5)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5)) )),
% 6.51/1.21    inference(superposition,[],[f72,f59])).
% 6.51/1.21  fof(f72,plain,(
% 6.51/1.21    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | v2_funct_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.51/1.21    inference(cnf_transformation,[],[f21])).
% 6.51/1.21  fof(f21,plain,(
% 6.51/1.21    ! [X0] : (! [X1] : (v2_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.51/1.21    inference(flattening,[],[f20])).
% 6.51/1.21  fof(f20,plain,(
% 6.51/1.21    ! [X0] : (! [X1] : ((v2_funct_1(X1) | (~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 6.51/1.21    inference(ennf_transformation,[],[f9])).
% 6.51/1.21  fof(f9,axiom,(
% 6.51/1.21    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & v2_funct_1(k5_relat_1(X1,X0))) => v2_funct_1(X1))))),
% 6.51/1.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_funct_1)).
% 6.51/1.21  fof(f388,plain,(
% 6.51/1.21    r1_tarski(k2_relat_1(sK6),k2_relat_1(sK6))),
% 6.51/1.21    inference(forward_demodulation,[],[f387,f59])).
% 6.51/1.21  fof(f387,plain,(
% 6.51/1.21    r1_tarski(k2_relat_1(sK6),k1_relat_1(sK5))),
% 6.51/1.21    inference(subsumption_resolution,[],[f386,f54])).
% 6.51/1.21  fof(f386,plain,(
% 6.51/1.21    r1_tarski(k2_relat_1(sK6),k1_relat_1(sK5)) | ~v1_relat_1(sK5)),
% 6.51/1.21    inference(subsumption_resolution,[],[f385,f55])).
% 6.51/1.21  fof(f385,plain,(
% 6.51/1.21    r1_tarski(k2_relat_1(sK6),k1_relat_1(sK5)) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5)),
% 6.51/1.21    inference(subsumption_resolution,[],[f384,f56])).
% 6.51/1.21  fof(f384,plain,(
% 6.51/1.21    r1_tarski(k2_relat_1(sK6),k1_relat_1(sK5)) | ~v1_relat_1(sK6) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5)),
% 6.51/1.21    inference(subsumption_resolution,[],[f383,f57])).
% 6.51/1.21  fof(f383,plain,(
% 6.51/1.21    r1_tarski(k2_relat_1(sK6),k1_relat_1(sK5)) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5)),
% 6.51/1.21    inference(trivial_inequality_removal,[],[f382])).
% 6.51/1.21  fof(f382,plain,(
% 6.51/1.21    k1_relat_1(sK6) != k1_relat_1(sK6) | r1_tarski(k2_relat_1(sK6),k1_relat_1(sK5)) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5)),
% 6.51/1.21    inference(superposition,[],[f71,f189])).
% 6.51/1.21  fof(f71,plain,(
% 6.51/1.21    ( ! [X0,X1] : (k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0)) | r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.51/1.21    inference(cnf_transformation,[],[f19])).
% 6.51/1.21  fof(f19,plain,(
% 6.51/1.21    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.51/1.21    inference(flattening,[],[f18])).
% 6.51/1.21  fof(f18,plain,(
% 6.51/1.21    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 6.51/1.21    inference(ennf_transformation,[],[f8])).
% 6.51/1.21  fof(f8,axiom,(
% 6.51/1.21    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0)) => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)))))),
% 6.51/1.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_funct_1)).
% 6.51/1.21  fof(f111,plain,(
% 6.51/1.21    spl11_2 | ~spl11_3),
% 6.51/1.21    inference(avatar_split_clause,[],[f102,f108,f94])).
% 6.51/1.21  fof(f94,plain,(
% 6.51/1.21    spl11_2 <=> v2_funct_1(sK5)),
% 6.51/1.21    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 6.51/1.21  fof(f102,plain,(
% 6.51/1.21    ~sP0(sK5) | v2_funct_1(sK5)),
% 6.51/1.21    inference(resolution,[],[f100,f64])).
% 6.51/1.21  fof(f64,plain,(
% 6.51/1.21    ( ! [X0] : (~sP1(X0) | ~sP0(X0) | v2_funct_1(X0)) )),
% 6.51/1.21    inference(cnf_transformation,[],[f40])).
% 6.51/1.21  fof(f100,plain,(
% 6.51/1.21    sP1(sK5)),
% 6.51/1.21    inference(subsumption_resolution,[],[f98,f54])).
% 6.51/1.21  fof(f98,plain,(
% 6.51/1.21    sP1(sK5) | ~v1_relat_1(sK5)),
% 6.51/1.21    inference(resolution,[],[f70,f55])).
% 6.51/1.21  fof(f97,plain,(
% 6.51/1.21    ~spl11_1 | ~spl11_2),
% 6.51/1.21    inference(avatar_split_clause,[],[f60,f94,f90])).
% 6.51/1.21  fof(f60,plain,(
% 6.51/1.21    ~v2_funct_1(sK5) | ~v2_funct_1(sK6)),
% 6.51/1.21    inference(cnf_transformation,[],[f39])).
% 6.51/1.21  % SZS output end Proof for theBenchmark
% 6.51/1.21  % (31652)------------------------------
% 6.51/1.21  % (31652)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.51/1.21  % (31652)Termination reason: Refutation
% 6.51/1.21  
% 6.51/1.21  % (31652)Memory used [KB]: 19957
% 6.51/1.21  % (31652)Time elapsed: 0.744 s
% 6.51/1.21  % (31652)------------------------------
% 6.51/1.21  % (31652)------------------------------
% 6.51/1.21  % (31626)Success in time 0.849 s
%------------------------------------------------------------------------------
