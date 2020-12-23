%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:38 EST 2020

% Result     : Theorem 10.34s
% Output     : Refutation 10.34s
% Verified   : 
% Statistics : Number of formulae       :  193 (1046 expanded)
%              Number of leaves         :   30 ( 337 expanded)
%              Depth                    :   29
%              Number of atoms          :  707 (6635 expanded)
%              Number of equality atoms :  116 (1084 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6882,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f101,f115,f244,f631,f660,f1611,f1640,f6670,f6685,f6827,f6881])).

fof(f6881,plain,
    ( spl11_6
    | ~ spl11_19
    | ~ spl11_20 ),
    inference(avatar_contradiction_clause,[],[f6880])).

fof(f6880,plain,
    ( $false
    | spl11_6
    | ~ spl11_19
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f200,f6849])).

fof(f6849,plain,
    ( sP0(k5_relat_1(sK6,sK5))
    | ~ spl11_19
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f669,f58])).

fof(f58,plain,(
    v2_funct_1(k5_relat_1(sK6,sK5)) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ( ~ v2_funct_1(sK5)
      | ~ v2_funct_1(sK6) )
    & k1_relat_1(sK5) = k2_relat_1(sK6)
    & v2_funct_1(k5_relat_1(sK6,sK5))
    & v1_funct_1(sK6)
    & v1_relat_1(sK6)
    & v1_funct_1(sK5)
    & v1_relat_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f13,f36,f35])).

fof(f35,plain,
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

fof(f36,plain,
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

fof(f669,plain,
    ( ~ v2_funct_1(k5_relat_1(sK6,sK5))
    | sP0(k5_relat_1(sK6,sK5))
    | ~ spl11_19
    | ~ spl11_20 ),
    inference(resolution,[],[f667,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | ~ v2_funct_1(X0)
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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

fof(f667,plain,
    ( sP1(k5_relat_1(sK6,sK5))
    | ~ spl11_19
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f665,f615])).

fof(f615,plain,
    ( v1_relat_1(k5_relat_1(sK6,sK5))
    | ~ spl11_19 ),
    inference(avatar_component_clause,[],[f614])).

fof(f614,plain,
    ( spl11_19
  <=> v1_relat_1(k5_relat_1(sK6,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_19])])).

fof(f665,plain,
    ( sP1(k5_relat_1(sK6,sK5))
    | ~ v1_relat_1(k5_relat_1(sK6,sK5))
    | ~ spl11_20 ),
    inference(resolution,[],[f619,f70])).

fof(f70,plain,(
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

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f619,plain,
    ( v1_funct_1(k5_relat_1(sK6,sK5))
    | ~ spl11_20 ),
    inference(avatar_component_clause,[],[f618])).

fof(f618,plain,
    ( spl11_20
  <=> v1_funct_1(k5_relat_1(sK6,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).

fof(f200,plain,
    ( ~ sP0(k5_relat_1(sK6,sK5))
    | spl11_6 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl11_6
  <=> sP0(k5_relat_1(sK6,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f6827,plain,
    ( spl11_3
    | ~ spl11_6
    | ~ spl11_27
    | spl11_29
    | ~ spl11_30 ),
    inference(avatar_contradiction_clause,[],[f6826])).

fof(f6826,plain,
    ( $false
    | spl11_3
    | ~ spl11_6
    | ~ spl11_27
    | spl11_29
    | ~ spl11_30 ),
    inference(subsumption_resolution,[],[f6825,f1627])).

fof(f1627,plain,
    ( sK10(sK7(sK5),sK6) != sK10(sK8(sK5),sK6)
    | spl11_29 ),
    inference(avatar_component_clause,[],[f1626])).

fof(f1626,plain,
    ( spl11_29
  <=> sK10(sK7(sK5),sK6) = sK10(sK8(sK5),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_29])])).

fof(f6825,plain,
    ( sK10(sK7(sK5),sK6) = sK10(sK8(sK5),sK6)
    | spl11_3
    | ~ spl11_6
    | ~ spl11_27
    | ~ spl11_30 ),
    inference(subsumption_resolution,[],[f6823,f1603])).

fof(f1603,plain,
    ( r2_hidden(sK10(sK7(sK5),sK6),k1_relat_1(sK6))
    | ~ spl11_27 ),
    inference(avatar_component_clause,[],[f1602])).

fof(f1602,plain,
    ( spl11_27
  <=> r2_hidden(sK10(sK7(sK5),sK6),k1_relat_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_27])])).

fof(f6823,plain,
    ( ~ r2_hidden(sK10(sK7(sK5),sK6),k1_relat_1(sK6))
    | sK10(sK7(sK5),sK6) = sK10(sK8(sK5),sK6)
    | spl11_3
    | ~ spl11_6
    | ~ spl11_30 ),
    inference(trivial_inequality_removal,[],[f6819])).

fof(f6819,plain,
    ( k1_funct_1(sK5,sK7(sK5)) != k1_funct_1(sK5,sK7(sK5))
    | ~ r2_hidden(sK10(sK7(sK5),sK6),k1_relat_1(sK6))
    | sK10(sK7(sK5),sK6) = sK10(sK8(sK5),sK6)
    | spl11_3
    | ~ spl11_6
    | ~ spl11_30 ),
    inference(superposition,[],[f6686,f452])).

fof(f452,plain,
    ( k1_funct_1(sK5,sK7(sK5)) = k1_funct_1(k5_relat_1(sK6,sK5),sK10(sK7(sK5),sK6))
    | spl11_3 ),
    inference(forward_demodulation,[],[f445,f144])).

fof(f144,plain,
    ( sK7(sK5) = k1_funct_1(sK6,sK10(sK7(sK5),sK6))
    | spl11_3 ),
    inference(resolution,[],[f79,f138])).

fof(f138,plain,
    ( sP2(sK7(sK5),sK6)
    | spl11_3 ),
    inference(subsumption_resolution,[],[f135,f120])).

fof(f120,plain,(
    sP4(sK6) ),
    inference(subsumption_resolution,[],[f118,f56])).

fof(f56,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f37])).

fof(f118,plain,
    ( sP4(sK6)
    | ~ v1_relat_1(sK6) ),
    inference(resolution,[],[f81,f57])).

fof(f57,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f37])).

fof(f81,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | sP4(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( sP4(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f21,f33,f32,f31])).

fof(f31,plain,(
    ! [X2,X0] :
      ( sP2(X2,X0)
    <=> ? [X3] :
          ( k1_funct_1(X0,X3) = X2
          & r2_hidden(X3,k1_relat_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f32,plain,(
    ! [X0,X1] :
      ( sP3(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> sP2(X2,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> sP3(X0,X1) )
      | ~ sP4(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(f135,plain,
    ( sP2(sK7(sK5),sK6)
    | ~ sP4(sK6)
    | spl11_3 ),
    inference(resolution,[],[f131,f122])).

fof(f122,plain,
    ( r2_hidden(sK7(sK5),k2_relat_1(sK6))
    | spl11_3 ),
    inference(subsumption_resolution,[],[f121,f114])).

fof(f114,plain,
    ( ~ sP0(sK5)
    | spl11_3 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl11_3
  <=> sP0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f121,plain,
    ( r2_hidden(sK7(sK5),k2_relat_1(sK6))
    | sP0(sK5) ),
    inference(superposition,[],[f66,f59])).

fof(f59,plain,(
    k1_relat_1(sK5) = k2_relat_1(sK6) ),
    inference(cnf_transformation,[],[f37])).

fof(f66,plain,(
    ! [X0] :
      ( r2_hidden(sK7(X0),k1_relat_1(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f40,f41])).

fof(f41,plain,(
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

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f39,plain,(
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

fof(f131,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_relat_1(X1))
      | sP2(X0,X1)
      | ~ sP4(X1) ) ),
    inference(resolution,[],[f74,f89])).

fof(f89,plain,(
    ! [X0] :
      ( sP3(X0,k2_relat_1(X0))
      | ~ sP4(X0) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( sP3(X0,X1)
      | k2_relat_1(X0) != X1
      | ~ sP4(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ~ sP3(X0,X1) )
          & ( sP3(X0,X1)
            | k2_relat_1(X0) != X1 ) )
      | ~ sP4(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( ~ sP3(X0,X1)
      | ~ r2_hidden(X3,X1)
      | sP2(X3,X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f45,f46])).

fof(f46,plain,(
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

fof(f45,plain,(
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
    inference(rectify,[],[f44])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ sP2(X0,X1)
      | k1_funct_1(X1,sK10(X0,X1)) = X0 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ! [X2] :
            ( k1_funct_1(X1,X2) != X0
            | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
      & ( ( k1_funct_1(X1,sK10(X0,X1)) = X0
          & r2_hidden(sK10(X0,X1),k1_relat_1(X1)) )
        | ~ sP2(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f49,f50])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( k1_funct_1(X1,X3) = X0
          & r2_hidden(X3,k1_relat_1(X1)) )
     => ( k1_funct_1(X1,sK10(X0,X1)) = X0
        & r2_hidden(sK10(X0,X1),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ! [X2] :
            ( k1_funct_1(X1,X2) != X0
            | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
      & ( ? [X3] :
            ( k1_funct_1(X1,X3) = X0
            & r2_hidden(X3,k1_relat_1(X1)) )
        | ~ sP2(X0,X1) ) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X2,X0] :
      ( ( sP2(X2,X0)
        | ! [X3] :
            ( k1_funct_1(X0,X3) != X2
            | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
      & ( ? [X3] :
            ( k1_funct_1(X0,X3) = X2
            & r2_hidden(X3,k1_relat_1(X0)) )
        | ~ sP2(X2,X0) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f445,plain,
    ( k1_funct_1(sK5,k1_funct_1(sK6,sK10(sK7(sK5),sK6))) = k1_funct_1(k5_relat_1(sK6,sK5),sK10(sK7(sK5),sK6))
    | spl11_3 ),
    inference(resolution,[],[f417,f138])).

fof(f417,plain,(
    ! [X1] :
      ( ~ sP2(X1,sK6)
      | k1_funct_1(sK5,k1_funct_1(sK6,sK10(X1,sK6))) = k1_funct_1(k5_relat_1(sK6,sK5),sK10(X1,sK6)) ) ),
    inference(resolution,[],[f400,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK10(X0,X1),k1_relat_1(X1))
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f400,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK6))
      | k1_funct_1(k5_relat_1(sK6,sK5),X0) = k1_funct_1(sK5,k1_funct_1(sK6,X0)) ) ),
    inference(subsumption_resolution,[],[f399,f54])).

fof(f54,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f37])).

fof(f399,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK6))
      | k1_funct_1(k5_relat_1(sK6,sK5),X0) = k1_funct_1(sK5,k1_funct_1(sK6,X0))
      | ~ v1_relat_1(sK5) ) ),
    inference(subsumption_resolution,[],[f398,f55])).

fof(f55,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f37])).

fof(f398,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK6))
      | k1_funct_1(k5_relat_1(sK6,sK5),X0) = k1_funct_1(sK5,k1_funct_1(sK6,X0))
      | ~ v1_funct_1(sK5)
      | ~ v1_relat_1(sK5) ) ),
    inference(subsumption_resolution,[],[f397,f56])).

fof(f397,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK6))
      | k1_funct_1(k5_relat_1(sK6,sK5),X0) = k1_funct_1(sK5,k1_funct_1(sK6,X0))
      | ~ v1_relat_1(sK6)
      | ~ v1_funct_1(sK5)
      | ~ v1_relat_1(sK5) ) ),
    inference(subsumption_resolution,[],[f396,f57])).

fof(f396,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK6))
      | k1_funct_1(k5_relat_1(sK6,sK5),X0) = k1_funct_1(sK5,k1_funct_1(sK6,X0))
      | ~ v1_funct_1(sK6)
      | ~ v1_relat_1(sK6)
      | ~ v1_funct_1(sK5)
      | ~ v1_relat_1(sK5) ) ),
    inference(superposition,[],[f84,f194])).

fof(f194,plain,(
    k1_relat_1(sK6) = k1_relat_1(k5_relat_1(sK6,sK5)) ),
    inference(forward_demodulation,[],[f191,f126])).

fof(f126,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f191,plain,(
    k10_relat_1(sK6,k2_relat_1(sK6)) = k1_relat_1(k5_relat_1(sK6,sK5)) ),
    inference(resolution,[],[f185,f56])).

fof(f185,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(X0,sK5)) = k10_relat_1(X0,k2_relat_1(sK6)) ) ),
    inference(forward_demodulation,[],[f181,f59])).

fof(f181,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
           => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).

fof(f6686,plain,
    ( ! [X0] :
        ( k1_funct_1(sK5,sK7(sK5)) != k1_funct_1(k5_relat_1(sK6,sK5),X0)
        | ~ r2_hidden(X0,k1_relat_1(sK6))
        | sK10(sK8(sK5),sK6) = X0 )
    | spl11_3
    | ~ spl11_6
    | ~ spl11_30 ),
    inference(subsumption_resolution,[],[f473,f1631])).

fof(f1631,plain,
    ( r2_hidden(sK10(sK8(sK5),sK6),k1_relat_1(sK6))
    | ~ spl11_30 ),
    inference(avatar_component_clause,[],[f1630])).

fof(f1630,plain,
    ( spl11_30
  <=> r2_hidden(sK10(sK8(sK5),sK6),k1_relat_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_30])])).

fof(f473,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK6))
        | ~ r2_hidden(sK10(sK8(sK5),sK6),k1_relat_1(sK6))
        | k1_funct_1(sK5,sK7(sK5)) != k1_funct_1(k5_relat_1(sK6,sK5),X0)
        | sK10(sK8(sK5),sK6) = X0 )
    | spl11_3
    | ~ spl11_6 ),
    inference(forward_demodulation,[],[f472,f194])).

fof(f472,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK10(sK8(sK5),sK6),k1_relat_1(sK6))
        | k1_funct_1(sK5,sK7(sK5)) != k1_funct_1(k5_relat_1(sK6,sK5),X0)
        | sK10(sK8(sK5),sK6) = X0
        | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK6,sK5))) )
    | spl11_3
    | ~ spl11_6 ),
    inference(forward_demodulation,[],[f471,f194])).

fof(f471,plain,
    ( ! [X0] :
        ( k1_funct_1(sK5,sK7(sK5)) != k1_funct_1(k5_relat_1(sK6,sK5),X0)
        | sK10(sK8(sK5),sK6) = X0
        | ~ r2_hidden(sK10(sK8(sK5),sK6),k1_relat_1(k5_relat_1(sK6,sK5)))
        | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK6,sK5))) )
    | spl11_3
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f468,f201])).

fof(f201,plain,
    ( sP0(k5_relat_1(sK6,sK5))
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f199])).

fof(f468,plain,
    ( ! [X0] :
        ( k1_funct_1(sK5,sK7(sK5)) != k1_funct_1(k5_relat_1(sK6,sK5),X0)
        | sK10(sK8(sK5),sK6) = X0
        | ~ r2_hidden(sK10(sK8(sK5),sK6),k1_relat_1(k5_relat_1(sK6,sK5)))
        | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK6,sK5)))
        | ~ sP0(k5_relat_1(sK6,sK5)) )
    | spl11_3 ),
    inference(superposition,[],[f65,f454])).

fof(f454,plain,
    ( k1_funct_1(sK5,sK7(sK5)) = k1_funct_1(k5_relat_1(sK6,sK5),sK10(sK8(sK5),sK6))
    | spl11_3 ),
    inference(forward_demodulation,[],[f453,f150])).

fof(f150,plain,
    ( k1_funct_1(sK5,sK7(sK5)) = k1_funct_1(sK5,sK8(sK5))
    | spl11_3 ),
    inference(resolution,[],[f68,f114])).

fof(f68,plain,(
    ! [X0] :
      ( sP0(X0)
      | k1_funct_1(X0,sK7(X0)) = k1_funct_1(X0,sK8(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f453,plain,
    ( k1_funct_1(sK5,sK8(sK5)) = k1_funct_1(k5_relat_1(sK6,sK5),sK10(sK8(sK5),sK6))
    | spl11_3 ),
    inference(forward_demodulation,[],[f446,f145])).

fof(f145,plain,
    ( sK8(sK5) = k1_funct_1(sK6,sK10(sK8(sK5),sK6))
    | spl11_3 ),
    inference(resolution,[],[f79,f139])).

fof(f139,plain,
    ( sP2(sK8(sK5),sK6)
    | spl11_3 ),
    inference(subsumption_resolution,[],[f136,f120])).

fof(f136,plain,
    ( sP2(sK8(sK5),sK6)
    | ~ sP4(sK6)
    | spl11_3 ),
    inference(resolution,[],[f131,f124])).

fof(f124,plain,
    ( r2_hidden(sK8(sK5),k2_relat_1(sK6))
    | spl11_3 ),
    inference(subsumption_resolution,[],[f123,f114])).

fof(f123,plain,
    ( r2_hidden(sK8(sK5),k2_relat_1(sK6))
    | sP0(sK5) ),
    inference(superposition,[],[f67,f59])).

fof(f67,plain,(
    ! [X0] :
      ( r2_hidden(sK8(X0),k1_relat_1(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f446,plain,
    ( k1_funct_1(sK5,k1_funct_1(sK6,sK10(sK8(sK5),sK6))) = k1_funct_1(k5_relat_1(sK6,sK5),sK10(sK8(sK5),sK6))
    | spl11_3 ),
    inference(resolution,[],[f417,f139])).

fof(f65,plain,(
    ! [X4,X0,X3] :
      ( k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | X3 = X4
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f6685,plain,
    ( spl11_3
    | ~ spl11_29
    | spl11_31 ),
    inference(avatar_contradiction_clause,[],[f6684])).

fof(f6684,plain,
    ( $false
    | spl11_3
    | ~ spl11_29
    | spl11_31 ),
    inference(subsumption_resolution,[],[f1636,f6677])).

fof(f6677,plain,
    ( sK7(sK5) = sK8(sK5)
    | spl11_3
    | ~ spl11_29 ),
    inference(forward_demodulation,[],[f6672,f144])).

fof(f6672,plain,
    ( sK8(sK5) = k1_funct_1(sK6,sK10(sK7(sK5),sK6))
    | spl11_3
    | ~ spl11_29 ),
    inference(backward_demodulation,[],[f145,f1628])).

fof(f1628,plain,
    ( sK10(sK7(sK5),sK6) = sK10(sK8(sK5),sK6)
    | ~ spl11_29 ),
    inference(avatar_component_clause,[],[f1626])).

fof(f1636,plain,
    ( sK7(sK5) != sK8(sK5)
    | spl11_31 ),
    inference(avatar_component_clause,[],[f1634])).

fof(f1634,plain,
    ( spl11_31
  <=> sK7(sK5) = sK8(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_31])])).

fof(f6670,plain,
    ( spl11_3
    | ~ spl11_31 ),
    inference(avatar_contradiction_clause,[],[f6669])).

fof(f6669,plain,
    ( $false
    | spl11_3
    | ~ spl11_31 ),
    inference(subsumption_resolution,[],[f6668,f114])).

fof(f6668,plain,
    ( sP0(sK5)
    | ~ spl11_31 ),
    inference(trivial_inequality_removal,[],[f6666])).

fof(f6666,plain,
    ( sK7(sK5) != sK7(sK5)
    | sP0(sK5)
    | ~ spl11_31 ),
    inference(superposition,[],[f69,f1635])).

fof(f1635,plain,
    ( sK7(sK5) = sK8(sK5)
    | ~ spl11_31 ),
    inference(avatar_component_clause,[],[f1634])).

fof(f69,plain,(
    ! [X0] :
      ( sK7(X0) != sK8(X0)
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f1640,plain,
    ( spl11_3
    | spl11_30 ),
    inference(avatar_contradiction_clause,[],[f1639])).

fof(f1639,plain,
    ( $false
    | spl11_3
    | spl11_30 ),
    inference(subsumption_resolution,[],[f1638,f139])).

fof(f1638,plain,
    ( ~ sP2(sK8(sK5),sK6)
    | spl11_30 ),
    inference(resolution,[],[f1632,f78])).

fof(f1632,plain,
    ( ~ r2_hidden(sK10(sK8(sK5),sK6),k1_relat_1(sK6))
    | spl11_30 ),
    inference(avatar_component_clause,[],[f1630])).

fof(f1611,plain,
    ( spl11_3
    | spl11_27 ),
    inference(avatar_contradiction_clause,[],[f1610])).

fof(f1610,plain,
    ( $false
    | spl11_3
    | spl11_27 ),
    inference(subsumption_resolution,[],[f1609,f138])).

fof(f1609,plain,
    ( ~ sP2(sK7(sK5),sK6)
    | spl11_27 ),
    inference(resolution,[],[f1604,f78])).

fof(f1604,plain,
    ( ~ r2_hidden(sK10(sK7(sK5),sK6),k1_relat_1(sK6))
    | spl11_27 ),
    inference(avatar_component_clause,[],[f1602])).

fof(f660,plain,(
    spl11_20 ),
    inference(avatar_contradiction_clause,[],[f659])).

fof(f659,plain,
    ( $false
    | spl11_20 ),
    inference(subsumption_resolution,[],[f658,f56])).

fof(f658,plain,
    ( ~ v1_relat_1(sK6)
    | spl11_20 ),
    inference(subsumption_resolution,[],[f657,f57])).

fof(f657,plain,
    ( ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | spl11_20 ),
    inference(subsumption_resolution,[],[f656,f54])).

fof(f656,plain,
    ( ~ v1_relat_1(sK5)
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | spl11_20 ),
    inference(subsumption_resolution,[],[f655,f55])).

fof(f655,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | spl11_20 ),
    inference(resolution,[],[f620,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funct_1)).

fof(f620,plain,
    ( ~ v1_funct_1(k5_relat_1(sK6,sK5))
    | spl11_20 ),
    inference(avatar_component_clause,[],[f618])).

fof(f631,plain,(
    spl11_19 ),
    inference(avatar_contradiction_clause,[],[f630])).

fof(f630,plain,
    ( $false
    | spl11_19 ),
    inference(subsumption_resolution,[],[f629,f56])).

fof(f629,plain,
    ( ~ v1_relat_1(sK6)
    | spl11_19 ),
    inference(subsumption_resolution,[],[f623,f54])).

fof(f623,plain,
    ( ~ v1_relat_1(sK5)
    | ~ v1_relat_1(sK6)
    | spl11_19 ),
    inference(resolution,[],[f616,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f616,plain,
    ( ~ v1_relat_1(k5_relat_1(sK6,sK5))
    | spl11_19 ),
    inference(avatar_component_clause,[],[f614])).

fof(f244,plain,(
    spl11_1 ),
    inference(avatar_contradiction_clause,[],[f243])).

fof(f243,plain,
    ( $false
    | spl11_1 ),
    inference(subsumption_resolution,[],[f242,f56])).

fof(f242,plain,
    ( ~ v1_relat_1(sK6)
    | spl11_1 ),
    inference(subsumption_resolution,[],[f241,f57])).

fof(f241,plain,
    ( ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | spl11_1 ),
    inference(subsumption_resolution,[],[f240,f58])).

fof(f240,plain,
    ( ~ v2_funct_1(k5_relat_1(sK6,sK5))
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | spl11_1 ),
    inference(subsumption_resolution,[],[f239,f96])).

fof(f96,plain,
    ( ~ v2_funct_1(sK6)
    | spl11_1 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl11_1
  <=> v2_funct_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f239,plain,
    ( v2_funct_1(sK6)
    | ~ v2_funct_1(k5_relat_1(sK6,sK5))
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6) ),
    inference(resolution,[],[f231,f91])).

fof(f91,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
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

fof(f231,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(X0),k2_relat_1(sK6))
      | v2_funct_1(X0)
      | ~ v2_funct_1(k5_relat_1(X0,sK5))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f230,f54])).

fof(f230,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(X0),k2_relat_1(sK6))
      | v2_funct_1(X0)
      | ~ v2_funct_1(k5_relat_1(X0,sK5))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK5) ) ),
    inference(subsumption_resolution,[],[f228,f55])).

fof(f228,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(X0),k2_relat_1(sK6))
      | v2_funct_1(X0)
      | ~ v2_funct_1(k5_relat_1(X0,sK5))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(sK5)
      | ~ v1_relat_1(sK5) ) ),
    inference(superposition,[],[f71,f59])).

fof(f71,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_funct_1)).

fof(f115,plain,
    ( spl11_2
    | ~ spl11_3 ),
    inference(avatar_split_clause,[],[f106,f112,f98])).

fof(f98,plain,
    ( spl11_2
  <=> v2_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f106,plain,
    ( ~ sP0(sK5)
    | v2_funct_1(sK5) ),
    inference(resolution,[],[f104,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | ~ sP0(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f104,plain,(
    sP1(sK5) ),
    inference(subsumption_resolution,[],[f102,f54])).

fof(f102,plain,
    ( sP1(sK5)
    | ~ v1_relat_1(sK5) ),
    inference(resolution,[],[f70,f55])).

fof(f101,plain,
    ( ~ spl11_1
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f60,f98,f94])).

fof(f60,plain,
    ( ~ v2_funct_1(sK5)
    | ~ v2_funct_1(sK6) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:04:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.46  % (12889)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.48  % (12899)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.49  % (12885)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.50  % (12896)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (12888)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.51  % (12894)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.51  % (12901)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.51  % (12883)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.51  % (12904)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.52  % (12886)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.52  % (12891)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.52  % (12890)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.52  % (12898)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.52  % (12905)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.53  % (12906)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.53  % (12900)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.53  % (12903)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.45/0.54  % (12887)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.45/0.54  % (12897)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.45/0.54  % (12893)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.45/0.54  % (12907)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.45/0.54  % (12895)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.45/0.54  % (12902)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.45/0.55  % (12884)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.45/0.55  % (12892)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.57/0.58  % (12908)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 2.50/0.69  % (12892)Refutation not found, incomplete strategy% (12892)------------------------------
% 2.50/0.69  % (12892)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.50/0.69  % (12892)Termination reason: Refutation not found, incomplete strategy
% 2.50/0.69  
% 2.50/0.69  % (12892)Memory used [KB]: 6140
% 2.50/0.69  % (12892)Time elapsed: 0.262 s
% 2.50/0.69  % (12892)------------------------------
% 2.50/0.69  % (12892)------------------------------
% 3.94/0.92  % (12897)Time limit reached!
% 3.94/0.92  % (12897)------------------------------
% 3.94/0.92  % (12897)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.94/0.92  % (12897)Termination reason: Time limit
% 3.94/0.92  % (12897)Termination phase: Saturation
% 3.94/0.92  
% 3.94/0.92  % (12897)Memory used [KB]: 8955
% 3.94/0.92  % (12897)Time elapsed: 0.500 s
% 3.94/0.92  % (12897)------------------------------
% 3.94/0.92  % (12897)------------------------------
% 4.53/0.95  % (12883)Time limit reached!
% 4.53/0.95  % (12883)------------------------------
% 4.53/0.95  % (12883)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.53/0.95  % (12883)Termination reason: Time limit
% 4.53/0.95  
% 4.53/0.95  % (12883)Memory used [KB]: 21364
% 4.53/0.95  % (12883)Time elapsed: 0.536 s
% 4.53/0.95  % (12883)------------------------------
% 4.53/0.95  % (12883)------------------------------
% 4.53/0.97  % (12896)Time limit reached!
% 4.53/0.97  % (12896)------------------------------
% 4.53/0.97  % (12896)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.53/0.97  % (12896)Termination reason: Time limit
% 4.53/0.97  
% 4.53/0.97  % (12896)Memory used [KB]: 24946
% 4.53/0.97  % (12896)Time elapsed: 0.537 s
% 4.53/0.97  % (12896)------------------------------
% 4.53/0.97  % (12896)------------------------------
% 4.91/1.02  % (12889)Time limit reached!
% 4.91/1.02  % (12889)------------------------------
% 4.91/1.02  % (12889)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.91/1.02  % (12889)Termination reason: Time limit
% 4.91/1.02  
% 4.91/1.02  % (12889)Memory used [KB]: 19573
% 4.91/1.02  % (12889)Time elapsed: 0.612 s
% 4.91/1.02  % (12889)------------------------------
% 4.91/1.02  % (12889)------------------------------
% 7.20/1.32  % (12891)Time limit reached!
% 7.20/1.32  % (12891)------------------------------
% 7.20/1.32  % (12891)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.20/1.32  % (12891)Termination reason: Time limit
% 7.20/1.32  
% 7.20/1.32  % (12891)Memory used [KB]: 17398
% 7.20/1.32  % (12891)Time elapsed: 0.915 s
% 7.20/1.32  % (12891)------------------------------
% 7.20/1.32  % (12891)------------------------------
% 8.09/1.41  % (12884)Time limit reached!
% 8.09/1.41  % (12884)------------------------------
% 8.09/1.41  % (12884)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.09/1.41  % (12884)Termination reason: Time limit
% 8.09/1.41  
% 8.09/1.41  % (12884)Memory used [KB]: 19189
% 8.09/1.41  % (12884)Time elapsed: 1.002 s
% 8.09/1.41  % (12884)------------------------------
% 8.09/1.41  % (12884)------------------------------
% 9.37/1.54  % (12887)Time limit reached!
% 9.37/1.54  % (12887)------------------------------
% 9.37/1.54  % (12887)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.37/1.54  % (12887)Termination reason: Time limit
% 9.37/1.54  % (12887)Termination phase: Saturation
% 9.37/1.54  
% 9.37/1.54  % (12887)Memory used [KB]: 12537
% 9.37/1.54  % (12887)Time elapsed: 1.100 s
% 9.37/1.54  % (12887)------------------------------
% 9.37/1.54  % (12887)------------------------------
% 10.34/1.66  % (12908)Refutation found. Thanks to Tanya!
% 10.34/1.66  % SZS status Theorem for theBenchmark
% 10.34/1.66  % SZS output start Proof for theBenchmark
% 10.34/1.68  fof(f6882,plain,(
% 10.34/1.68    $false),
% 10.34/1.68    inference(avatar_sat_refutation,[],[f101,f115,f244,f631,f660,f1611,f1640,f6670,f6685,f6827,f6881])).
% 10.34/1.68  fof(f6881,plain,(
% 10.34/1.68    spl11_6 | ~spl11_19 | ~spl11_20),
% 10.34/1.68    inference(avatar_contradiction_clause,[],[f6880])).
% 10.34/1.68  fof(f6880,plain,(
% 10.34/1.68    $false | (spl11_6 | ~spl11_19 | ~spl11_20)),
% 10.34/1.68    inference(subsumption_resolution,[],[f200,f6849])).
% 10.34/1.68  fof(f6849,plain,(
% 10.34/1.68    sP0(k5_relat_1(sK6,sK5)) | (~spl11_19 | ~spl11_20)),
% 10.34/1.68    inference(subsumption_resolution,[],[f669,f58])).
% 10.34/1.68  fof(f58,plain,(
% 10.34/1.68    v2_funct_1(k5_relat_1(sK6,sK5))),
% 10.34/1.68    inference(cnf_transformation,[],[f37])).
% 10.34/1.68  fof(f37,plain,(
% 10.34/1.68    ((~v2_funct_1(sK5) | ~v2_funct_1(sK6)) & k1_relat_1(sK5) = k2_relat_1(sK6) & v2_funct_1(k5_relat_1(sK6,sK5)) & v1_funct_1(sK6) & v1_relat_1(sK6)) & v1_funct_1(sK5) & v1_relat_1(sK5)),
% 10.34/1.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f13,f36,f35])).
% 10.34/1.68  fof(f35,plain,(
% 10.34/1.68    ? [X0] : (? [X1] : ((~v2_funct_1(X0) | ~v2_funct_1(X1)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(k5_relat_1(X1,X0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : ((~v2_funct_1(sK5) | ~v2_funct_1(X1)) & k2_relat_1(X1) = k1_relat_1(sK5) & v2_funct_1(k5_relat_1(X1,sK5)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK5) & v1_relat_1(sK5))),
% 10.34/1.68    introduced(choice_axiom,[])).
% 10.34/1.68  fof(f36,plain,(
% 10.34/1.68    ? [X1] : ((~v2_funct_1(sK5) | ~v2_funct_1(X1)) & k2_relat_1(X1) = k1_relat_1(sK5) & v2_funct_1(k5_relat_1(X1,sK5)) & v1_funct_1(X1) & v1_relat_1(X1)) => ((~v2_funct_1(sK5) | ~v2_funct_1(sK6)) & k1_relat_1(sK5) = k2_relat_1(sK6) & v2_funct_1(k5_relat_1(sK6,sK5)) & v1_funct_1(sK6) & v1_relat_1(sK6))),
% 10.34/1.68    introduced(choice_axiom,[])).
% 10.34/1.68  fof(f13,plain,(
% 10.34/1.68    ? [X0] : (? [X1] : ((~v2_funct_1(X0) | ~v2_funct_1(X1)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(k5_relat_1(X1,X0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 10.34/1.68    inference(flattening,[],[f12])).
% 10.34/1.68  fof(f12,plain,(
% 10.34/1.68    ? [X0] : (? [X1] : (((~v2_funct_1(X0) | ~v2_funct_1(X1)) & (k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(k5_relat_1(X1,X0)))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 10.34/1.68    inference(ennf_transformation,[],[f11])).
% 10.34/1.68  fof(f11,negated_conjecture,(
% 10.34/1.68    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 10.34/1.68    inference(negated_conjecture,[],[f10])).
% 10.34/1.68  fof(f10,conjecture,(
% 10.34/1.68    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 10.34/1.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).
% 10.34/1.68  fof(f669,plain,(
% 10.34/1.68    ~v2_funct_1(k5_relat_1(sK6,sK5)) | sP0(k5_relat_1(sK6,sK5)) | (~spl11_19 | ~spl11_20)),
% 10.34/1.68    inference(resolution,[],[f667,f63])).
% 10.34/1.68  fof(f63,plain,(
% 10.34/1.68    ( ! [X0] : (~sP1(X0) | ~v2_funct_1(X0) | sP0(X0)) )),
% 10.34/1.68    inference(cnf_transformation,[],[f38])).
% 10.34/1.68  fof(f38,plain,(
% 10.34/1.68    ! [X0] : (((v2_funct_1(X0) | ~sP0(X0)) & (sP0(X0) | ~v2_funct_1(X0))) | ~sP1(X0))),
% 10.34/1.68    inference(nnf_transformation,[],[f29])).
% 10.34/1.68  fof(f29,plain,(
% 10.34/1.68    ! [X0] : ((v2_funct_1(X0) <=> sP0(X0)) | ~sP1(X0))),
% 10.34/1.68    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 10.34/1.68  fof(f667,plain,(
% 10.34/1.68    sP1(k5_relat_1(sK6,sK5)) | (~spl11_19 | ~spl11_20)),
% 10.34/1.68    inference(subsumption_resolution,[],[f665,f615])).
% 10.34/1.68  fof(f615,plain,(
% 10.34/1.68    v1_relat_1(k5_relat_1(sK6,sK5)) | ~spl11_19),
% 10.34/1.68    inference(avatar_component_clause,[],[f614])).
% 10.34/1.68  fof(f614,plain,(
% 10.34/1.68    spl11_19 <=> v1_relat_1(k5_relat_1(sK6,sK5))),
% 10.34/1.68    introduced(avatar_definition,[new_symbols(naming,[spl11_19])])).
% 10.34/1.68  fof(f665,plain,(
% 10.34/1.68    sP1(k5_relat_1(sK6,sK5)) | ~v1_relat_1(k5_relat_1(sK6,sK5)) | ~spl11_20),
% 10.34/1.68    inference(resolution,[],[f619,f70])).
% 10.34/1.68  fof(f70,plain,(
% 10.34/1.68    ( ! [X0] : (~v1_funct_1(X0) | sP1(X0) | ~v1_relat_1(X0)) )),
% 10.34/1.68    inference(cnf_transformation,[],[f30])).
% 10.34/1.68  fof(f30,plain,(
% 10.34/1.68    ! [X0] : (sP1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 10.34/1.68    inference(definition_folding,[],[f17,f29,f28])).
% 10.34/1.68  fof(f28,plain,(
% 10.34/1.68    ! [X0] : (sP0(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))),
% 10.34/1.68    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 10.34/1.68  fof(f17,plain,(
% 10.34/1.68    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 10.34/1.68    inference(flattening,[],[f16])).
% 10.34/1.68  fof(f16,plain,(
% 10.34/1.68    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 10.34/1.68    inference(ennf_transformation,[],[f6])).
% 10.34/1.68  fof(f6,axiom,(
% 10.34/1.68    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 10.34/1.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).
% 10.34/1.68  fof(f619,plain,(
% 10.34/1.68    v1_funct_1(k5_relat_1(sK6,sK5)) | ~spl11_20),
% 10.34/1.68    inference(avatar_component_clause,[],[f618])).
% 10.34/1.68  fof(f618,plain,(
% 10.34/1.68    spl11_20 <=> v1_funct_1(k5_relat_1(sK6,sK5))),
% 10.34/1.68    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).
% 10.34/1.68  fof(f200,plain,(
% 10.34/1.68    ~sP0(k5_relat_1(sK6,sK5)) | spl11_6),
% 10.34/1.68    inference(avatar_component_clause,[],[f199])).
% 10.34/1.68  fof(f199,plain,(
% 10.34/1.68    spl11_6 <=> sP0(k5_relat_1(sK6,sK5))),
% 10.34/1.68    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).
% 10.34/1.68  fof(f6827,plain,(
% 10.34/1.68    spl11_3 | ~spl11_6 | ~spl11_27 | spl11_29 | ~spl11_30),
% 10.34/1.68    inference(avatar_contradiction_clause,[],[f6826])).
% 10.34/1.68  fof(f6826,plain,(
% 10.34/1.68    $false | (spl11_3 | ~spl11_6 | ~spl11_27 | spl11_29 | ~spl11_30)),
% 10.34/1.68    inference(subsumption_resolution,[],[f6825,f1627])).
% 10.34/1.68  fof(f1627,plain,(
% 10.34/1.68    sK10(sK7(sK5),sK6) != sK10(sK8(sK5),sK6) | spl11_29),
% 10.34/1.68    inference(avatar_component_clause,[],[f1626])).
% 10.34/1.68  fof(f1626,plain,(
% 10.34/1.68    spl11_29 <=> sK10(sK7(sK5),sK6) = sK10(sK8(sK5),sK6)),
% 10.34/1.68    introduced(avatar_definition,[new_symbols(naming,[spl11_29])])).
% 10.34/1.68  fof(f6825,plain,(
% 10.34/1.68    sK10(sK7(sK5),sK6) = sK10(sK8(sK5),sK6) | (spl11_3 | ~spl11_6 | ~spl11_27 | ~spl11_30)),
% 10.34/1.68    inference(subsumption_resolution,[],[f6823,f1603])).
% 10.34/1.68  fof(f1603,plain,(
% 10.34/1.68    r2_hidden(sK10(sK7(sK5),sK6),k1_relat_1(sK6)) | ~spl11_27),
% 10.34/1.68    inference(avatar_component_clause,[],[f1602])).
% 10.34/1.68  fof(f1602,plain,(
% 10.34/1.68    spl11_27 <=> r2_hidden(sK10(sK7(sK5),sK6),k1_relat_1(sK6))),
% 10.34/1.68    introduced(avatar_definition,[new_symbols(naming,[spl11_27])])).
% 10.34/1.68  fof(f6823,plain,(
% 10.34/1.68    ~r2_hidden(sK10(sK7(sK5),sK6),k1_relat_1(sK6)) | sK10(sK7(sK5),sK6) = sK10(sK8(sK5),sK6) | (spl11_3 | ~spl11_6 | ~spl11_30)),
% 10.34/1.68    inference(trivial_inequality_removal,[],[f6819])).
% 10.34/1.68  fof(f6819,plain,(
% 10.34/1.68    k1_funct_1(sK5,sK7(sK5)) != k1_funct_1(sK5,sK7(sK5)) | ~r2_hidden(sK10(sK7(sK5),sK6),k1_relat_1(sK6)) | sK10(sK7(sK5),sK6) = sK10(sK8(sK5),sK6) | (spl11_3 | ~spl11_6 | ~spl11_30)),
% 10.34/1.68    inference(superposition,[],[f6686,f452])).
% 10.34/1.68  fof(f452,plain,(
% 10.34/1.68    k1_funct_1(sK5,sK7(sK5)) = k1_funct_1(k5_relat_1(sK6,sK5),sK10(sK7(sK5),sK6)) | spl11_3),
% 10.34/1.68    inference(forward_demodulation,[],[f445,f144])).
% 10.34/1.68  fof(f144,plain,(
% 10.34/1.68    sK7(sK5) = k1_funct_1(sK6,sK10(sK7(sK5),sK6)) | spl11_3),
% 10.34/1.68    inference(resolution,[],[f79,f138])).
% 10.34/1.68  fof(f138,plain,(
% 10.34/1.68    sP2(sK7(sK5),sK6) | spl11_3),
% 10.34/1.68    inference(subsumption_resolution,[],[f135,f120])).
% 10.34/1.68  fof(f120,plain,(
% 10.34/1.68    sP4(sK6)),
% 10.34/1.68    inference(subsumption_resolution,[],[f118,f56])).
% 10.34/1.68  fof(f56,plain,(
% 10.34/1.68    v1_relat_1(sK6)),
% 10.34/1.68    inference(cnf_transformation,[],[f37])).
% 10.34/1.68  fof(f118,plain,(
% 10.34/1.68    sP4(sK6) | ~v1_relat_1(sK6)),
% 10.34/1.68    inference(resolution,[],[f81,f57])).
% 10.34/1.68  fof(f57,plain,(
% 10.34/1.68    v1_funct_1(sK6)),
% 10.34/1.68    inference(cnf_transformation,[],[f37])).
% 10.34/1.68  fof(f81,plain,(
% 10.34/1.68    ( ! [X0] : (~v1_funct_1(X0) | sP4(X0) | ~v1_relat_1(X0)) )),
% 10.34/1.68    inference(cnf_transformation,[],[f34])).
% 10.34/1.68  fof(f34,plain,(
% 10.34/1.68    ! [X0] : (sP4(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 10.34/1.68    inference(definition_folding,[],[f21,f33,f32,f31])).
% 10.34/1.68  fof(f31,plain,(
% 10.34/1.68    ! [X2,X0] : (sP2(X2,X0) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))),
% 10.34/1.68    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 10.34/1.68  fof(f32,plain,(
% 10.34/1.68    ! [X0,X1] : (sP3(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> sP2(X2,X0)))),
% 10.34/1.68    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 10.34/1.68  fof(f33,plain,(
% 10.34/1.68    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> sP3(X0,X1)) | ~sP4(X0))),
% 10.34/1.68    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 10.34/1.68  fof(f21,plain,(
% 10.34/1.68    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 10.34/1.68    inference(flattening,[],[f20])).
% 10.34/1.68  fof(f20,plain,(
% 10.34/1.68    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 10.34/1.68    inference(ennf_transformation,[],[f5])).
% 10.34/1.68  fof(f5,axiom,(
% 10.34/1.68    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 10.34/1.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 10.34/1.68  fof(f135,plain,(
% 10.34/1.68    sP2(sK7(sK5),sK6) | ~sP4(sK6) | spl11_3),
% 10.34/1.68    inference(resolution,[],[f131,f122])).
% 10.34/1.68  fof(f122,plain,(
% 10.34/1.68    r2_hidden(sK7(sK5),k2_relat_1(sK6)) | spl11_3),
% 10.34/1.68    inference(subsumption_resolution,[],[f121,f114])).
% 10.34/1.68  fof(f114,plain,(
% 10.34/1.68    ~sP0(sK5) | spl11_3),
% 10.34/1.68    inference(avatar_component_clause,[],[f112])).
% 10.34/1.68  fof(f112,plain,(
% 10.34/1.68    spl11_3 <=> sP0(sK5)),
% 10.34/1.68    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).
% 10.34/1.68  fof(f121,plain,(
% 10.34/1.68    r2_hidden(sK7(sK5),k2_relat_1(sK6)) | sP0(sK5)),
% 10.34/1.68    inference(superposition,[],[f66,f59])).
% 10.34/1.68  fof(f59,plain,(
% 10.34/1.68    k1_relat_1(sK5) = k2_relat_1(sK6)),
% 10.34/1.68    inference(cnf_transformation,[],[f37])).
% 10.34/1.68  fof(f66,plain,(
% 10.34/1.68    ( ! [X0] : (r2_hidden(sK7(X0),k1_relat_1(X0)) | sP0(X0)) )),
% 10.34/1.68    inference(cnf_transformation,[],[f42])).
% 10.34/1.68  fof(f42,plain,(
% 10.34/1.68    ! [X0] : ((sP0(X0) | (sK7(X0) != sK8(X0) & k1_funct_1(X0,sK7(X0)) = k1_funct_1(X0,sK8(X0)) & r2_hidden(sK8(X0),k1_relat_1(X0)) & r2_hidden(sK7(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X0)))),
% 10.34/1.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f40,f41])).
% 10.34/1.68  fof(f41,plain,(
% 10.34/1.68    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK7(X0) != sK8(X0) & k1_funct_1(X0,sK7(X0)) = k1_funct_1(X0,sK8(X0)) & r2_hidden(sK8(X0),k1_relat_1(X0)) & r2_hidden(sK7(X0),k1_relat_1(X0))))),
% 10.34/1.68    introduced(choice_axiom,[])).
% 10.34/1.68  fof(f40,plain,(
% 10.34/1.68    ! [X0] : ((sP0(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X0)))),
% 10.34/1.68    inference(rectify,[],[f39])).
% 10.34/1.68  fof(f39,plain,(
% 10.34/1.68    ! [X0] : ((sP0(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~sP0(X0)))),
% 10.34/1.68    inference(nnf_transformation,[],[f28])).
% 10.34/1.68  fof(f131,plain,(
% 10.34/1.68    ( ! [X0,X1] : (~r2_hidden(X0,k2_relat_1(X1)) | sP2(X0,X1) | ~sP4(X1)) )),
% 10.34/1.68    inference(resolution,[],[f74,f89])).
% 10.34/1.68  fof(f89,plain,(
% 10.34/1.68    ( ! [X0] : (sP3(X0,k2_relat_1(X0)) | ~sP4(X0)) )),
% 10.34/1.68    inference(equality_resolution,[],[f72])).
% 10.34/1.68  fof(f72,plain,(
% 10.34/1.68    ( ! [X0,X1] : (sP3(X0,X1) | k2_relat_1(X0) != X1 | ~sP4(X0)) )),
% 10.34/1.68    inference(cnf_transformation,[],[f43])).
% 10.34/1.68  fof(f43,plain,(
% 10.34/1.68    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ~sP3(X0,X1)) & (sP3(X0,X1) | k2_relat_1(X0) != X1)) | ~sP4(X0))),
% 10.34/1.68    inference(nnf_transformation,[],[f33])).
% 10.34/1.68  fof(f74,plain,(
% 10.34/1.68    ( ! [X0,X3,X1] : (~sP3(X0,X1) | ~r2_hidden(X3,X1) | sP2(X3,X0)) )),
% 10.34/1.68    inference(cnf_transformation,[],[f47])).
% 10.34/1.68  fof(f47,plain,(
% 10.34/1.68    ! [X0,X1] : ((sP3(X0,X1) | ((~sP2(sK9(X0,X1),X0) | ~r2_hidden(sK9(X0,X1),X1)) & (sP2(sK9(X0,X1),X0) | r2_hidden(sK9(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~sP2(X3,X0)) & (sP2(X3,X0) | ~r2_hidden(X3,X1))) | ~sP3(X0,X1)))),
% 10.34/1.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f45,f46])).
% 10.34/1.68  fof(f46,plain,(
% 10.34/1.68    ! [X1,X0] : (? [X2] : ((~sP2(X2,X0) | ~r2_hidden(X2,X1)) & (sP2(X2,X0) | r2_hidden(X2,X1))) => ((~sP2(sK9(X0,X1),X0) | ~r2_hidden(sK9(X0,X1),X1)) & (sP2(sK9(X0,X1),X0) | r2_hidden(sK9(X0,X1),X1))))),
% 10.34/1.68    introduced(choice_axiom,[])).
% 10.34/1.68  fof(f45,plain,(
% 10.34/1.68    ! [X0,X1] : ((sP3(X0,X1) | ? [X2] : ((~sP2(X2,X0) | ~r2_hidden(X2,X1)) & (sP2(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~sP2(X3,X0)) & (sP2(X3,X0) | ~r2_hidden(X3,X1))) | ~sP3(X0,X1)))),
% 10.34/1.68    inference(rectify,[],[f44])).
% 10.34/1.68  fof(f44,plain,(
% 10.34/1.68    ! [X0,X1] : ((sP3(X0,X1) | ? [X2] : ((~sP2(X2,X0) | ~r2_hidden(X2,X1)) & (sP2(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~sP2(X2,X0)) & (sP2(X2,X0) | ~r2_hidden(X2,X1))) | ~sP3(X0,X1)))),
% 10.34/1.68    inference(nnf_transformation,[],[f32])).
% 10.34/1.68  fof(f79,plain,(
% 10.34/1.68    ( ! [X0,X1] : (~sP2(X0,X1) | k1_funct_1(X1,sK10(X0,X1)) = X0) )),
% 10.34/1.68    inference(cnf_transformation,[],[f51])).
% 10.34/1.68  fof(f51,plain,(
% 10.34/1.68    ! [X0,X1] : ((sP2(X0,X1) | ! [X2] : (k1_funct_1(X1,X2) != X0 | ~r2_hidden(X2,k1_relat_1(X1)))) & ((k1_funct_1(X1,sK10(X0,X1)) = X0 & r2_hidden(sK10(X0,X1),k1_relat_1(X1))) | ~sP2(X0,X1)))),
% 10.34/1.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f49,f50])).
% 10.34/1.68  fof(f50,plain,(
% 10.34/1.68    ! [X1,X0] : (? [X3] : (k1_funct_1(X1,X3) = X0 & r2_hidden(X3,k1_relat_1(X1))) => (k1_funct_1(X1,sK10(X0,X1)) = X0 & r2_hidden(sK10(X0,X1),k1_relat_1(X1))))),
% 10.34/1.68    introduced(choice_axiom,[])).
% 10.34/1.68  fof(f49,plain,(
% 10.34/1.68    ! [X0,X1] : ((sP2(X0,X1) | ! [X2] : (k1_funct_1(X1,X2) != X0 | ~r2_hidden(X2,k1_relat_1(X1)))) & (? [X3] : (k1_funct_1(X1,X3) = X0 & r2_hidden(X3,k1_relat_1(X1))) | ~sP2(X0,X1)))),
% 10.34/1.68    inference(rectify,[],[f48])).
% 10.34/1.68  fof(f48,plain,(
% 10.34/1.68    ! [X2,X0] : ((sP2(X2,X0) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~sP2(X2,X0)))),
% 10.34/1.68    inference(nnf_transformation,[],[f31])).
% 10.34/1.68  fof(f445,plain,(
% 10.34/1.68    k1_funct_1(sK5,k1_funct_1(sK6,sK10(sK7(sK5),sK6))) = k1_funct_1(k5_relat_1(sK6,sK5),sK10(sK7(sK5),sK6)) | spl11_3),
% 10.34/1.68    inference(resolution,[],[f417,f138])).
% 10.34/1.68  fof(f417,plain,(
% 10.34/1.68    ( ! [X1] : (~sP2(X1,sK6) | k1_funct_1(sK5,k1_funct_1(sK6,sK10(X1,sK6))) = k1_funct_1(k5_relat_1(sK6,sK5),sK10(X1,sK6))) )),
% 10.34/1.68    inference(resolution,[],[f400,f78])).
% 10.34/1.68  fof(f78,plain,(
% 10.34/1.68    ( ! [X0,X1] : (r2_hidden(sK10(X0,X1),k1_relat_1(X1)) | ~sP2(X0,X1)) )),
% 10.34/1.68    inference(cnf_transformation,[],[f51])).
% 10.34/1.68  fof(f400,plain,(
% 10.34/1.68    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK6)) | k1_funct_1(k5_relat_1(sK6,sK5),X0) = k1_funct_1(sK5,k1_funct_1(sK6,X0))) )),
% 10.34/1.68    inference(subsumption_resolution,[],[f399,f54])).
% 10.34/1.68  fof(f54,plain,(
% 10.34/1.68    v1_relat_1(sK5)),
% 10.34/1.68    inference(cnf_transformation,[],[f37])).
% 10.34/1.68  fof(f399,plain,(
% 10.34/1.68    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK6)) | k1_funct_1(k5_relat_1(sK6,sK5),X0) = k1_funct_1(sK5,k1_funct_1(sK6,X0)) | ~v1_relat_1(sK5)) )),
% 10.34/1.68    inference(subsumption_resolution,[],[f398,f55])).
% 10.34/1.68  fof(f55,plain,(
% 10.34/1.68    v1_funct_1(sK5)),
% 10.34/1.68    inference(cnf_transformation,[],[f37])).
% 10.34/1.68  fof(f398,plain,(
% 10.34/1.68    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK6)) | k1_funct_1(k5_relat_1(sK6,sK5),X0) = k1_funct_1(sK5,k1_funct_1(sK6,X0)) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5)) )),
% 10.34/1.68    inference(subsumption_resolution,[],[f397,f56])).
% 10.34/1.68  fof(f397,plain,(
% 10.34/1.68    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK6)) | k1_funct_1(k5_relat_1(sK6,sK5),X0) = k1_funct_1(sK5,k1_funct_1(sK6,X0)) | ~v1_relat_1(sK6) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5)) )),
% 10.34/1.68    inference(subsumption_resolution,[],[f396,f57])).
% 10.34/1.68  fof(f396,plain,(
% 10.34/1.68    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK6)) | k1_funct_1(k5_relat_1(sK6,sK5),X0) = k1_funct_1(sK5,k1_funct_1(sK6,X0)) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5)) )),
% 10.34/1.68    inference(superposition,[],[f84,f194])).
% 10.34/1.68  fof(f194,plain,(
% 10.34/1.68    k1_relat_1(sK6) = k1_relat_1(k5_relat_1(sK6,sK5))),
% 10.34/1.68    inference(forward_demodulation,[],[f191,f126])).
% 10.34/1.68  fof(f126,plain,(
% 10.34/1.68    k10_relat_1(sK6,k2_relat_1(sK6)) = k1_relat_1(sK6)),
% 10.34/1.68    inference(resolution,[],[f61,f56])).
% 10.34/1.68  fof(f61,plain,(
% 10.34/1.68    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 10.34/1.68    inference(cnf_transformation,[],[f14])).
% 10.34/1.68  fof(f14,plain,(
% 10.34/1.68    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 10.34/1.68    inference(ennf_transformation,[],[f3])).
% 10.34/1.68  fof(f3,axiom,(
% 10.34/1.68    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 10.34/1.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 10.34/1.68  fof(f191,plain,(
% 10.34/1.68    k10_relat_1(sK6,k2_relat_1(sK6)) = k1_relat_1(k5_relat_1(sK6,sK5))),
% 10.34/1.68    inference(resolution,[],[f185,f56])).
% 10.34/1.68  fof(f185,plain,(
% 10.34/1.68    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(k5_relat_1(X0,sK5)) = k10_relat_1(X0,k2_relat_1(sK6))) )),
% 10.34/1.68    inference(forward_demodulation,[],[f181,f59])).
% 10.34/1.68  fof(f181,plain,(
% 10.34/1.68    ( ! [X0] : (k1_relat_1(k5_relat_1(X0,sK5)) = k10_relat_1(X0,k1_relat_1(sK5)) | ~v1_relat_1(X0)) )),
% 10.34/1.68    inference(resolution,[],[f62,f54])).
% 10.34/1.68  fof(f62,plain,(
% 10.34/1.68    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 10.34/1.68    inference(cnf_transformation,[],[f15])).
% 10.34/1.68  fof(f15,plain,(
% 10.34/1.68    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 10.34/1.68    inference(ennf_transformation,[],[f4])).
% 10.34/1.68  fof(f4,axiom,(
% 10.34/1.68    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 10.34/1.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 10.34/1.68  fof(f84,plain,(
% 10.34/1.68    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 10.34/1.68    inference(cnf_transformation,[],[f25])).
% 10.34/1.68  fof(f25,plain,(
% 10.34/1.68    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 10.34/1.68    inference(flattening,[],[f24])).
% 10.34/1.68  fof(f24,plain,(
% 10.34/1.68    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 10.34/1.68    inference(ennf_transformation,[],[f8])).
% 10.34/1.68  fof(f8,axiom,(
% 10.34/1.68    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)))))),
% 10.34/1.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).
% 10.34/1.68  fof(f6686,plain,(
% 10.34/1.68    ( ! [X0] : (k1_funct_1(sK5,sK7(sK5)) != k1_funct_1(k5_relat_1(sK6,sK5),X0) | ~r2_hidden(X0,k1_relat_1(sK6)) | sK10(sK8(sK5),sK6) = X0) ) | (spl11_3 | ~spl11_6 | ~spl11_30)),
% 10.34/1.68    inference(subsumption_resolution,[],[f473,f1631])).
% 10.34/1.68  fof(f1631,plain,(
% 10.34/1.68    r2_hidden(sK10(sK8(sK5),sK6),k1_relat_1(sK6)) | ~spl11_30),
% 10.34/1.68    inference(avatar_component_clause,[],[f1630])).
% 10.34/1.68  fof(f1630,plain,(
% 10.34/1.68    spl11_30 <=> r2_hidden(sK10(sK8(sK5),sK6),k1_relat_1(sK6))),
% 10.34/1.68    introduced(avatar_definition,[new_symbols(naming,[spl11_30])])).
% 10.34/1.68  fof(f473,plain,(
% 10.34/1.68    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK6)) | ~r2_hidden(sK10(sK8(sK5),sK6),k1_relat_1(sK6)) | k1_funct_1(sK5,sK7(sK5)) != k1_funct_1(k5_relat_1(sK6,sK5),X0) | sK10(sK8(sK5),sK6) = X0) ) | (spl11_3 | ~spl11_6)),
% 10.34/1.68    inference(forward_demodulation,[],[f472,f194])).
% 10.34/1.68  fof(f472,plain,(
% 10.34/1.68    ( ! [X0] : (~r2_hidden(sK10(sK8(sK5),sK6),k1_relat_1(sK6)) | k1_funct_1(sK5,sK7(sK5)) != k1_funct_1(k5_relat_1(sK6,sK5),X0) | sK10(sK8(sK5),sK6) = X0 | ~r2_hidden(X0,k1_relat_1(k5_relat_1(sK6,sK5)))) ) | (spl11_3 | ~spl11_6)),
% 10.34/1.68    inference(forward_demodulation,[],[f471,f194])).
% 10.34/1.68  fof(f471,plain,(
% 10.34/1.68    ( ! [X0] : (k1_funct_1(sK5,sK7(sK5)) != k1_funct_1(k5_relat_1(sK6,sK5),X0) | sK10(sK8(sK5),sK6) = X0 | ~r2_hidden(sK10(sK8(sK5),sK6),k1_relat_1(k5_relat_1(sK6,sK5))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(sK6,sK5)))) ) | (spl11_3 | ~spl11_6)),
% 10.34/1.68    inference(subsumption_resolution,[],[f468,f201])).
% 10.34/1.68  fof(f201,plain,(
% 10.34/1.68    sP0(k5_relat_1(sK6,sK5)) | ~spl11_6),
% 10.34/1.68    inference(avatar_component_clause,[],[f199])).
% 10.34/1.68  fof(f468,plain,(
% 10.34/1.68    ( ! [X0] : (k1_funct_1(sK5,sK7(sK5)) != k1_funct_1(k5_relat_1(sK6,sK5),X0) | sK10(sK8(sK5),sK6) = X0 | ~r2_hidden(sK10(sK8(sK5),sK6),k1_relat_1(k5_relat_1(sK6,sK5))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(sK6,sK5))) | ~sP0(k5_relat_1(sK6,sK5))) ) | spl11_3),
% 10.34/1.68    inference(superposition,[],[f65,f454])).
% 10.34/1.68  fof(f454,plain,(
% 10.34/1.68    k1_funct_1(sK5,sK7(sK5)) = k1_funct_1(k5_relat_1(sK6,sK5),sK10(sK8(sK5),sK6)) | spl11_3),
% 10.34/1.68    inference(forward_demodulation,[],[f453,f150])).
% 10.34/1.68  fof(f150,plain,(
% 10.34/1.68    k1_funct_1(sK5,sK7(sK5)) = k1_funct_1(sK5,sK8(sK5)) | spl11_3),
% 10.34/1.68    inference(resolution,[],[f68,f114])).
% 10.34/1.68  fof(f68,plain,(
% 10.34/1.68    ( ! [X0] : (sP0(X0) | k1_funct_1(X0,sK7(X0)) = k1_funct_1(X0,sK8(X0))) )),
% 10.34/1.68    inference(cnf_transformation,[],[f42])).
% 10.34/1.68  fof(f453,plain,(
% 10.34/1.68    k1_funct_1(sK5,sK8(sK5)) = k1_funct_1(k5_relat_1(sK6,sK5),sK10(sK8(sK5),sK6)) | spl11_3),
% 10.34/1.68    inference(forward_demodulation,[],[f446,f145])).
% 10.34/1.68  fof(f145,plain,(
% 10.34/1.68    sK8(sK5) = k1_funct_1(sK6,sK10(sK8(sK5),sK6)) | spl11_3),
% 10.34/1.68    inference(resolution,[],[f79,f139])).
% 10.34/1.68  fof(f139,plain,(
% 10.34/1.68    sP2(sK8(sK5),sK6) | spl11_3),
% 10.34/1.68    inference(subsumption_resolution,[],[f136,f120])).
% 10.34/1.68  fof(f136,plain,(
% 10.34/1.68    sP2(sK8(sK5),sK6) | ~sP4(sK6) | spl11_3),
% 10.34/1.68    inference(resolution,[],[f131,f124])).
% 10.34/1.68  fof(f124,plain,(
% 10.34/1.68    r2_hidden(sK8(sK5),k2_relat_1(sK6)) | spl11_3),
% 10.34/1.68    inference(subsumption_resolution,[],[f123,f114])).
% 10.34/1.68  fof(f123,plain,(
% 10.34/1.68    r2_hidden(sK8(sK5),k2_relat_1(sK6)) | sP0(sK5)),
% 10.34/1.68    inference(superposition,[],[f67,f59])).
% 10.34/1.68  fof(f67,plain,(
% 10.34/1.68    ( ! [X0] : (r2_hidden(sK8(X0),k1_relat_1(X0)) | sP0(X0)) )),
% 10.34/1.68    inference(cnf_transformation,[],[f42])).
% 10.34/1.68  fof(f446,plain,(
% 10.34/1.68    k1_funct_1(sK5,k1_funct_1(sK6,sK10(sK8(sK5),sK6))) = k1_funct_1(k5_relat_1(sK6,sK5),sK10(sK8(sK5),sK6)) | spl11_3),
% 10.34/1.68    inference(resolution,[],[f417,f139])).
% 10.34/1.68  fof(f65,plain,(
% 10.34/1.68    ( ! [X4,X0,X3] : (k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | X3 = X4 | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0)) | ~sP0(X0)) )),
% 10.34/1.68    inference(cnf_transformation,[],[f42])).
% 10.34/1.68  fof(f6685,plain,(
% 10.34/1.68    spl11_3 | ~spl11_29 | spl11_31),
% 10.34/1.68    inference(avatar_contradiction_clause,[],[f6684])).
% 10.34/1.68  fof(f6684,plain,(
% 10.34/1.68    $false | (spl11_3 | ~spl11_29 | spl11_31)),
% 10.34/1.68    inference(subsumption_resolution,[],[f1636,f6677])).
% 10.34/1.68  fof(f6677,plain,(
% 10.34/1.68    sK7(sK5) = sK8(sK5) | (spl11_3 | ~spl11_29)),
% 10.34/1.68    inference(forward_demodulation,[],[f6672,f144])).
% 10.34/1.68  fof(f6672,plain,(
% 10.34/1.68    sK8(sK5) = k1_funct_1(sK6,sK10(sK7(sK5),sK6)) | (spl11_3 | ~spl11_29)),
% 10.34/1.68    inference(backward_demodulation,[],[f145,f1628])).
% 10.34/1.68  fof(f1628,plain,(
% 10.34/1.68    sK10(sK7(sK5),sK6) = sK10(sK8(sK5),sK6) | ~spl11_29),
% 10.34/1.68    inference(avatar_component_clause,[],[f1626])).
% 10.34/1.68  fof(f1636,plain,(
% 10.34/1.68    sK7(sK5) != sK8(sK5) | spl11_31),
% 10.34/1.68    inference(avatar_component_clause,[],[f1634])).
% 10.34/1.68  fof(f1634,plain,(
% 10.34/1.68    spl11_31 <=> sK7(sK5) = sK8(sK5)),
% 10.34/1.68    introduced(avatar_definition,[new_symbols(naming,[spl11_31])])).
% 10.34/1.68  fof(f6670,plain,(
% 10.34/1.68    spl11_3 | ~spl11_31),
% 10.34/1.68    inference(avatar_contradiction_clause,[],[f6669])).
% 10.34/1.68  fof(f6669,plain,(
% 10.34/1.68    $false | (spl11_3 | ~spl11_31)),
% 10.34/1.68    inference(subsumption_resolution,[],[f6668,f114])).
% 10.34/1.68  fof(f6668,plain,(
% 10.34/1.68    sP0(sK5) | ~spl11_31),
% 10.34/1.68    inference(trivial_inequality_removal,[],[f6666])).
% 10.34/1.68  fof(f6666,plain,(
% 10.34/1.68    sK7(sK5) != sK7(sK5) | sP0(sK5) | ~spl11_31),
% 10.34/1.68    inference(superposition,[],[f69,f1635])).
% 10.34/1.68  fof(f1635,plain,(
% 10.34/1.68    sK7(sK5) = sK8(sK5) | ~spl11_31),
% 10.34/1.68    inference(avatar_component_clause,[],[f1634])).
% 10.34/1.68  fof(f69,plain,(
% 10.34/1.68    ( ! [X0] : (sK7(X0) != sK8(X0) | sP0(X0)) )),
% 10.34/1.68    inference(cnf_transformation,[],[f42])).
% 10.34/1.68  fof(f1640,plain,(
% 10.34/1.68    spl11_3 | spl11_30),
% 10.34/1.68    inference(avatar_contradiction_clause,[],[f1639])).
% 10.34/1.68  fof(f1639,plain,(
% 10.34/1.68    $false | (spl11_3 | spl11_30)),
% 10.34/1.68    inference(subsumption_resolution,[],[f1638,f139])).
% 10.34/1.68  fof(f1638,plain,(
% 10.34/1.68    ~sP2(sK8(sK5),sK6) | spl11_30),
% 10.34/1.68    inference(resolution,[],[f1632,f78])).
% 10.34/1.68  fof(f1632,plain,(
% 10.34/1.68    ~r2_hidden(sK10(sK8(sK5),sK6),k1_relat_1(sK6)) | spl11_30),
% 10.34/1.68    inference(avatar_component_clause,[],[f1630])).
% 10.34/1.68  fof(f1611,plain,(
% 10.34/1.68    spl11_3 | spl11_27),
% 10.34/1.68    inference(avatar_contradiction_clause,[],[f1610])).
% 10.34/1.68  fof(f1610,plain,(
% 10.34/1.68    $false | (spl11_3 | spl11_27)),
% 10.34/1.68    inference(subsumption_resolution,[],[f1609,f138])).
% 10.34/1.68  fof(f1609,plain,(
% 10.34/1.68    ~sP2(sK7(sK5),sK6) | spl11_27),
% 10.34/1.68    inference(resolution,[],[f1604,f78])).
% 10.34/1.68  fof(f1604,plain,(
% 10.34/1.68    ~r2_hidden(sK10(sK7(sK5),sK6),k1_relat_1(sK6)) | spl11_27),
% 10.34/1.68    inference(avatar_component_clause,[],[f1602])).
% 10.34/1.68  fof(f660,plain,(
% 10.34/1.68    spl11_20),
% 10.34/1.68    inference(avatar_contradiction_clause,[],[f659])).
% 10.34/1.68  fof(f659,plain,(
% 10.34/1.68    $false | spl11_20),
% 10.34/1.68    inference(subsumption_resolution,[],[f658,f56])).
% 10.34/1.68  fof(f658,plain,(
% 10.34/1.68    ~v1_relat_1(sK6) | spl11_20),
% 10.34/1.68    inference(subsumption_resolution,[],[f657,f57])).
% 10.34/1.68  fof(f657,plain,(
% 10.34/1.68    ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | spl11_20),
% 10.34/1.68    inference(subsumption_resolution,[],[f656,f54])).
% 10.34/1.68  fof(f656,plain,(
% 10.34/1.68    ~v1_relat_1(sK5) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | spl11_20),
% 10.34/1.68    inference(subsumption_resolution,[],[f655,f55])).
% 10.34/1.68  fof(f655,plain,(
% 10.34/1.68    ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | spl11_20),
% 10.34/1.68    inference(resolution,[],[f620,f83])).
% 10.34/1.68  fof(f83,plain,(
% 10.34/1.68    ( ! [X0,X1] : (v1_funct_1(k5_relat_1(X0,X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 10.34/1.68    inference(cnf_transformation,[],[f23])).
% 10.34/1.68  fof(f23,plain,(
% 10.34/1.68    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 10.34/1.68    inference(flattening,[],[f22])).
% 10.34/1.68  fof(f22,plain,(
% 10.34/1.68    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 10.34/1.68    inference(ennf_transformation,[],[f7])).
% 10.34/1.68  fof(f7,axiom,(
% 10.34/1.68    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1) & v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))))),
% 10.34/1.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funct_1)).
% 10.34/1.68  fof(f620,plain,(
% 10.34/1.68    ~v1_funct_1(k5_relat_1(sK6,sK5)) | spl11_20),
% 10.34/1.68    inference(avatar_component_clause,[],[f618])).
% 10.34/1.68  fof(f631,plain,(
% 10.34/1.68    spl11_19),
% 10.34/1.68    inference(avatar_contradiction_clause,[],[f630])).
% 10.34/1.68  fof(f630,plain,(
% 10.34/1.68    $false | spl11_19),
% 10.34/1.68    inference(subsumption_resolution,[],[f629,f56])).
% 10.34/1.68  fof(f629,plain,(
% 10.34/1.68    ~v1_relat_1(sK6) | spl11_19),
% 10.34/1.68    inference(subsumption_resolution,[],[f623,f54])).
% 10.34/1.68  fof(f623,plain,(
% 10.34/1.68    ~v1_relat_1(sK5) | ~v1_relat_1(sK6) | spl11_19),
% 10.34/1.68    inference(resolution,[],[f616,f85])).
% 10.34/1.68  fof(f85,plain,(
% 10.34/1.68    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 10.34/1.68    inference(cnf_transformation,[],[f27])).
% 10.34/1.68  fof(f27,plain,(
% 10.34/1.68    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 10.34/1.68    inference(flattening,[],[f26])).
% 10.34/1.68  fof(f26,plain,(
% 10.34/1.68    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 10.34/1.68    inference(ennf_transformation,[],[f2])).
% 10.34/1.68  fof(f2,axiom,(
% 10.34/1.68    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 10.34/1.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 10.34/1.68  fof(f616,plain,(
% 10.34/1.68    ~v1_relat_1(k5_relat_1(sK6,sK5)) | spl11_19),
% 10.34/1.68    inference(avatar_component_clause,[],[f614])).
% 10.34/1.68  fof(f244,plain,(
% 10.34/1.68    spl11_1),
% 10.34/1.68    inference(avatar_contradiction_clause,[],[f243])).
% 10.34/1.68  fof(f243,plain,(
% 10.34/1.68    $false | spl11_1),
% 10.34/1.68    inference(subsumption_resolution,[],[f242,f56])).
% 10.34/1.68  fof(f242,plain,(
% 10.34/1.68    ~v1_relat_1(sK6) | spl11_1),
% 10.34/1.68    inference(subsumption_resolution,[],[f241,f57])).
% 10.34/1.68  fof(f241,plain,(
% 10.34/1.68    ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | spl11_1),
% 10.34/1.68    inference(subsumption_resolution,[],[f240,f58])).
% 10.34/1.68  fof(f240,plain,(
% 10.34/1.68    ~v2_funct_1(k5_relat_1(sK6,sK5)) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | spl11_1),
% 10.34/1.68    inference(subsumption_resolution,[],[f239,f96])).
% 10.34/1.68  fof(f96,plain,(
% 10.34/1.68    ~v2_funct_1(sK6) | spl11_1),
% 10.34/1.68    inference(avatar_component_clause,[],[f94])).
% 10.34/1.68  fof(f94,plain,(
% 10.34/1.68    spl11_1 <=> v2_funct_1(sK6)),
% 10.34/1.68    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 10.34/1.68  fof(f239,plain,(
% 10.34/1.68    v2_funct_1(sK6) | ~v2_funct_1(k5_relat_1(sK6,sK5)) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6)),
% 10.34/1.68    inference(resolution,[],[f231,f91])).
% 10.34/1.68  fof(f91,plain,(
% 10.34/1.68    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 10.34/1.68    inference(equality_resolution,[],[f87])).
% 10.34/1.68  fof(f87,plain,(
% 10.34/1.68    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 10.34/1.68    inference(cnf_transformation,[],[f53])).
% 10.34/1.68  fof(f53,plain,(
% 10.34/1.68    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 10.34/1.68    inference(flattening,[],[f52])).
% 10.34/1.68  fof(f52,plain,(
% 10.34/1.68    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 10.34/1.68    inference(nnf_transformation,[],[f1])).
% 10.34/1.68  fof(f1,axiom,(
% 10.34/1.68    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 10.34/1.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 10.34/1.68  fof(f231,plain,(
% 10.34/1.68    ( ! [X0] : (~r1_tarski(k2_relat_1(X0),k2_relat_1(sK6)) | v2_funct_1(X0) | ~v2_funct_1(k5_relat_1(X0,sK5)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 10.34/1.68    inference(subsumption_resolution,[],[f230,f54])).
% 10.34/1.68  fof(f230,plain,(
% 10.34/1.68    ( ! [X0] : (~r1_tarski(k2_relat_1(X0),k2_relat_1(sK6)) | v2_funct_1(X0) | ~v2_funct_1(k5_relat_1(X0,sK5)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(sK5)) )),
% 10.34/1.68    inference(subsumption_resolution,[],[f228,f55])).
% 10.34/1.68  fof(f228,plain,(
% 10.34/1.68    ( ! [X0] : (~r1_tarski(k2_relat_1(X0),k2_relat_1(sK6)) | v2_funct_1(X0) | ~v2_funct_1(k5_relat_1(X0,sK5)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5)) )),
% 10.34/1.68    inference(superposition,[],[f71,f59])).
% 10.34/1.68  fof(f71,plain,(
% 10.34/1.68    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | v2_funct_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 10.34/1.68    inference(cnf_transformation,[],[f19])).
% 10.34/1.68  fof(f19,plain,(
% 10.34/1.68    ! [X0] : (! [X1] : (v2_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 10.34/1.68    inference(flattening,[],[f18])).
% 10.34/1.68  fof(f18,plain,(
% 10.34/1.68    ! [X0] : (! [X1] : ((v2_funct_1(X1) | (~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 10.34/1.68    inference(ennf_transformation,[],[f9])).
% 10.34/1.68  fof(f9,axiom,(
% 10.34/1.68    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & v2_funct_1(k5_relat_1(X1,X0))) => v2_funct_1(X1))))),
% 10.34/1.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_funct_1)).
% 10.34/1.68  fof(f115,plain,(
% 10.34/1.68    spl11_2 | ~spl11_3),
% 10.34/1.68    inference(avatar_split_clause,[],[f106,f112,f98])).
% 10.34/1.68  fof(f98,plain,(
% 10.34/1.68    spl11_2 <=> v2_funct_1(sK5)),
% 10.34/1.68    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 10.34/1.68  fof(f106,plain,(
% 10.34/1.68    ~sP0(sK5) | v2_funct_1(sK5)),
% 10.34/1.68    inference(resolution,[],[f104,f64])).
% 10.34/1.68  fof(f64,plain,(
% 10.34/1.68    ( ! [X0] : (~sP1(X0) | ~sP0(X0) | v2_funct_1(X0)) )),
% 10.34/1.68    inference(cnf_transformation,[],[f38])).
% 10.34/1.68  fof(f104,plain,(
% 10.34/1.68    sP1(sK5)),
% 10.34/1.68    inference(subsumption_resolution,[],[f102,f54])).
% 10.34/1.68  fof(f102,plain,(
% 10.34/1.68    sP1(sK5) | ~v1_relat_1(sK5)),
% 10.34/1.68    inference(resolution,[],[f70,f55])).
% 10.34/1.68  fof(f101,plain,(
% 10.34/1.68    ~spl11_1 | ~spl11_2),
% 10.34/1.68    inference(avatar_split_clause,[],[f60,f98,f94])).
% 10.34/1.68  fof(f60,plain,(
% 10.34/1.68    ~v2_funct_1(sK5) | ~v2_funct_1(sK6)),
% 10.34/1.68    inference(cnf_transformation,[],[f37])).
% 10.34/1.68  % SZS output end Proof for theBenchmark
% 10.34/1.68  % (12908)------------------------------
% 10.34/1.68  % (12908)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.34/1.68  % (12908)Termination reason: Refutation
% 10.34/1.68  
% 10.34/1.68  % (12908)Memory used [KB]: 23283
% 10.34/1.68  % (12908)Time elapsed: 1.222 s
% 10.34/1.68  % (12908)------------------------------
% 10.34/1.68  % (12908)------------------------------
% 10.34/1.68  % (12882)Success in time 1.327 s
%------------------------------------------------------------------------------
