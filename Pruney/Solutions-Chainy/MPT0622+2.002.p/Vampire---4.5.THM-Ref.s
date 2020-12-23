%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:01 EST 2020

% Result     : Theorem 1.39s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 392 expanded)
%              Number of leaves         :   29 ( 138 expanded)
%              Depth                    :   13
%              Number of atoms          :  441 (1302 expanded)
%              Number of equality atoms :   70 ( 398 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f472,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f96,f98,f102,f116,f121,f123,f125,f152,f158,f263,f264,f324,f332,f349,f351,f361,f424,f437,f453,f471])).

fof(f471,plain,(
    ~ spl6_39 ),
    inference(avatar_contradiction_clause,[],[f454])).

fof(f454,plain,
    ( $false
    | ~ spl6_39 ),
    inference(subsumption_resolution,[],[f24,f356])).

fof(f356,plain,
    ( sK1 = sK2
    | ~ spl6_39 ),
    inference(avatar_component_clause,[],[f354])).

fof(f354,plain,
    ( spl6_39
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f24,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & k1_tarski(X0) = k2_relat_1(X2)
          & k1_tarski(X0) = k2_relat_1(X1)
          & k1_relat_1(X1) = k1_relat_1(X2)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & k1_tarski(X0) = k2_relat_1(X2)
          & k1_tarski(X0) = k2_relat_1(X1)
          & k1_relat_1(X1) = k1_relat_1(X2)
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ( ( k1_tarski(X0) = k2_relat_1(X2)
                & k1_tarski(X0) = k2_relat_1(X1)
                & k1_relat_1(X1) = k1_relat_1(X2) )
             => X1 = X2 ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( ( k1_tarski(X0) = k2_relat_1(X2)
              & k1_tarski(X0) = k2_relat_1(X1)
              & k1_relat_1(X1) = k1_relat_1(X2) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_funct_1)).

fof(f453,plain,
    ( ~ spl6_5
    | spl6_40
    | spl6_47 ),
    inference(avatar_contradiction_clause,[],[f451])).

fof(f451,plain,
    ( $false
    | ~ spl6_5
    | spl6_40
    | spl6_47 ),
    inference(unit_resulting_resolution,[],[f360,f436,f95])).

fof(f95,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(sK2,X0),k1_relat_1(sK1))
        | r1_tarski(sK2,X0) )
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl6_5
  <=> ! [X0] :
        ( r2_hidden(sK3(sK2,X0),k1_relat_1(sK1))
        | r1_tarski(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f436,plain,
    ( ~ r2_hidden(sK3(sK2,sK1),k1_relat_1(sK1))
    | spl6_47 ),
    inference(avatar_component_clause,[],[f434])).

fof(f434,plain,
    ( spl6_47
  <=> r2_hidden(sK3(sK2,sK1),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).

fof(f360,plain,
    ( ~ r1_tarski(sK2,sK1)
    | spl6_40 ),
    inference(avatar_component_clause,[],[f358])).

fof(f358,plain,
    ( spl6_40
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f437,plain,
    ( ~ spl6_47
    | spl6_40
    | ~ spl6_10
    | ~ spl6_45 ),
    inference(avatar_split_clause,[],[f431,f422,f150,f358,f434])).

fof(f150,plain,
    ( spl6_10
  <=> ! [X0] :
        ( r2_hidden(k4_tarski(X0,sK0),sK1)
        | ~ r2_hidden(X0,k1_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f422,plain,
    ( spl6_45
  <=> ! [X2] :
        ( ~ r2_hidden(k4_tarski(sK3(sK2,X2),sK0),X2)
        | r1_tarski(sK2,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).

fof(f431,plain,
    ( r1_tarski(sK2,sK1)
    | ~ r2_hidden(sK3(sK2,sK1),k1_relat_1(sK1))
    | ~ spl6_10
    | ~ spl6_45 ),
    inference(resolution,[],[f423,f151])).

fof(f151,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,sK0),sK1)
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f150])).

fof(f423,plain,
    ( ! [X2] :
        ( ~ r2_hidden(k4_tarski(sK3(sK2,X2),sK0),X2)
        | r1_tarski(sK2,X2) )
    | ~ spl6_45 ),
    inference(avatar_component_clause,[],[f422])).

fof(f424,plain,
    ( ~ spl6_3
    | spl6_45
    | ~ spl6_5
    | ~ spl6_27 ),
    inference(avatar_split_clause,[],[f415,f260,f94,f422,f86])).

fof(f86,plain,
    ( spl6_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f260,plain,
    ( spl6_27
  <=> ! [X3] :
        ( sK0 = sK4(sK2,X3)
        | ~ r2_hidden(sK3(sK2,X3),k1_relat_1(sK1))
        | r1_tarski(sK2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f415,plain,
    ( ! [X2] :
        ( ~ r2_hidden(k4_tarski(sK3(sK2,X2),sK0),X2)
        | ~ v1_relat_1(sK2)
        | r1_tarski(sK2,X2) )
    | ~ spl6_5
    | ~ spl6_27 ),
    inference(duplicate_literal_removal,[],[f412])).

fof(f412,plain,
    ( ! [X2] :
        ( ~ r2_hidden(k4_tarski(sK3(sK2,X2),sK0),X2)
        | ~ v1_relat_1(sK2)
        | r1_tarski(sK2,X2)
        | r1_tarski(sK2,X2) )
    | ~ spl6_5
    | ~ spl6_27 ),
    inference(superposition,[],[f30,f410])).

fof(f410,plain,
    ( ! [X0] :
        ( sK0 = sK4(sK2,X0)
        | r1_tarski(sK2,X0) )
    | ~ spl6_5
    | ~ spl6_27 ),
    inference(duplicate_literal_removal,[],[f409])).

fof(f409,plain,
    ( ! [X0] :
        ( sK0 = sK4(sK2,X0)
        | r1_tarski(sK2,X0)
        | r1_tarski(sK2,X0) )
    | ~ spl6_5
    | ~ spl6_27 ),
    inference(resolution,[],[f261,f95])).

fof(f261,plain,
    ( ! [X3] :
        ( ~ r2_hidden(sK3(sK2,X3),k1_relat_1(sK1))
        | sK0 = sK4(sK2,X3)
        | r1_tarski(sK2,X3) )
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f260])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)
      | ~ v1_relat_1(X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

fof(f361,plain,
    ( spl6_39
    | ~ spl6_40
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f352,f346,f358,f354])).

fof(f346,plain,
    ( spl6_38
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f352,plain,
    ( ~ r1_tarski(sK2,sK1)
    | sK1 = sK2
    | ~ spl6_38 ),
    inference(resolution,[],[f348,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f348,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl6_38 ),
    inference(avatar_component_clause,[],[f346])).

fof(f351,plain,
    ( ~ spl6_6
    | ~ spl6_8
    | spl6_38
    | spl6_37 ),
    inference(avatar_split_clause,[],[f350,f342,f346,f113,f106])).

fof(f106,plain,
    ( spl6_6
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f113,plain,
    ( spl6_8
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f342,plain,
    ( spl6_37
  <=> r2_hidden(sK3(sK1,sK2),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f350,plain,
    ( r1_tarski(sK1,sK2)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl6_37 ),
    inference(resolution,[],[f344,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),k1_relat_1(X0))
      | r1_tarski(X0,X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(X0,X1)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK3(X0,X1),k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f29,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
      | ~ v1_relat_1(X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f344,plain,
    ( ~ r2_hidden(sK3(sK1,sK2),k1_relat_1(sK1))
    | spl6_37 ),
    inference(avatar_component_clause,[],[f342])).

fof(f349,plain,
    ( ~ spl6_37
    | spl6_38
    | ~ spl6_11
    | ~ spl6_35 ),
    inference(avatar_split_clause,[],[f340,f330,f156,f346,f342])).

fof(f156,plain,
    ( spl6_11
  <=> ! [X1] :
        ( ~ r2_hidden(X1,k1_relat_1(sK1))
        | r2_hidden(k4_tarski(X1,sK0),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f330,plain,
    ( spl6_35
  <=> ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK3(sK1,X0),sK0),X0)
        | r1_tarski(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f340,plain,
    ( r1_tarski(sK1,sK2)
    | ~ r2_hidden(sK3(sK1,sK2),k1_relat_1(sK1))
    | ~ spl6_11
    | ~ spl6_35 ),
    inference(resolution,[],[f331,f157])).

fof(f157,plain,
    ( ! [X1] :
        ( r2_hidden(k4_tarski(X1,sK0),sK2)
        | ~ r2_hidden(X1,k1_relat_1(sK1)) )
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f156])).

fof(f331,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK3(sK1,X0),sK0),X0)
        | r1_tarski(sK1,X0) )
    | ~ spl6_35 ),
    inference(avatar_component_clause,[],[f330])).

fof(f332,plain,
    ( ~ spl6_6
    | spl6_35
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f328,f322,f330,f106])).

fof(f322,plain,
    ( spl6_34
  <=> ! [X0] :
        ( sK0 = sK4(sK1,X0)
        | r1_tarski(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f328,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK3(sK1,X0),sK0),X0)
        | ~ v1_relat_1(sK1)
        | r1_tarski(sK1,X0) )
    | ~ spl6_34 ),
    inference(duplicate_literal_removal,[],[f325])).

fof(f325,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK3(sK1,X0),sK0),X0)
        | ~ v1_relat_1(sK1)
        | r1_tarski(sK1,X0)
        | r1_tarski(sK1,X0) )
    | ~ spl6_34 ),
    inference(superposition,[],[f30,f323])).

fof(f323,plain,
    ( ! [X0] :
        ( sK0 = sK4(sK1,X0)
        | r1_tarski(sK1,X0) )
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f322])).

fof(f324,plain,
    ( ~ spl6_6
    | ~ spl6_8
    | spl6_34
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f320,f256,f322,f113,f106])).

fof(f256,plain,
    ( spl6_26
  <=> ! [X2] :
        ( sK0 = sK4(sK1,X2)
        | ~ r2_hidden(sK3(sK1,X2),k1_relat_1(sK1))
        | r1_tarski(sK1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f320,plain,
    ( ! [X0] :
        ( sK0 = sK4(sK1,X0)
        | r1_tarski(sK1,X0)
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl6_26 ),
    inference(duplicate_literal_removal,[],[f319])).

fof(f319,plain,
    ( ! [X0] :
        ( sK0 = sK4(sK1,X0)
        | r1_tarski(sK1,X0)
        | r1_tarski(sK1,X0)
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl6_26 ),
    inference(resolution,[],[f257,f75])).

fof(f257,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK3(sK1,X2),k1_relat_1(sK1))
        | sK0 = sK4(sK1,X2)
        | r1_tarski(sK1,X2) )
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f256])).

fof(f264,plain,
    ( ~ spl6_3
    | ~ spl6_4
    | spl6_27
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f251,f119,f260,f90,f86])).

fof(f90,plain,
    ( spl6_4
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f119,plain,
    ( spl6_9
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f251,plain,
    ( ! [X5] :
        ( sK0 = sK4(sK2,X5)
        | ~ r2_hidden(sK3(sK2,X5),k1_relat_1(sK1))
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2)
        | r1_tarski(sK2,X5) )
    | ~ spl6_9 ),
    inference(superposition,[],[f128,f134])).

fof(f134,plain,(
    ! [X0,X1] :
      ( sK4(X0,X1) = k1_funct_1(X0,sK3(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r1_tarski(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f132])).

fof(f132,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | sK4(X0,X1) = k1_funct_1(X0,sK3(X0,X1))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f42,f29])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f128,plain,
    ( ! [X0] :
        ( sK0 = k1_funct_1(sK2,X0)
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl6_9 ),
    inference(resolution,[],[f120,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK1))
      | sK0 = X0 ) ),
    inference(superposition,[],[f56,f49])).

fof(f49,plain,(
    k2_relat_1(sK1) = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f22,f47])).

fof(f47,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f27,f46])).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f31,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f40,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f40,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f31,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f27,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f22,plain,(
    k1_tarski(sK0) = k2_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f56,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k3_enumset1(X0,X0,X0,X0,X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f37,f47])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f120,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK1))
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f119])).

fof(f263,plain,
    ( ~ spl6_6
    | ~ spl6_8
    | spl6_26
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f250,f110,f256,f113,f106])).

fof(f110,plain,
    ( spl6_7
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | sK0 = k1_funct_1(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f250,plain,
    ( ! [X4] :
        ( sK0 = sK4(sK1,X4)
        | ~ r2_hidden(sK3(sK1,X4),k1_relat_1(sK1))
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1)
        | r1_tarski(sK1,X4) )
    | ~ spl6_7 ),
    inference(superposition,[],[f111,f134])).

fof(f111,plain,
    ( ! [X0] :
        ( sK0 = k1_funct_1(sK1,X0)
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f110])).

fof(f158,plain,
    ( ~ spl6_3
    | ~ spl6_4
    | spl6_11
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f154,f119,f156,f90,f86])).

fof(f154,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_relat_1(sK1))
        | r2_hidden(k4_tarski(X1,sK0),sK2)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl6_9 ),
    inference(duplicate_literal_removal,[],[f153])).

fof(f153,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_relat_1(sK1))
        | r2_hidden(k4_tarski(X1,sK0),sK2)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2)
        | ~ r2_hidden(X1,k1_relat_1(sK1)) )
    | ~ spl6_9 ),
    inference(forward_demodulation,[],[f144,f21])).

fof(f21,plain,(
    k1_relat_1(sK1) = k1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f13])).

% (24591)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
fof(f144,plain,
    ( ! [X1] :
        ( r2_hidden(k4_tarski(X1,sK0),sK2)
        | ~ v1_funct_1(sK2)
        | ~ r2_hidden(X1,k1_relat_1(sK2))
        | ~ v1_relat_1(sK2)
        | ~ r2_hidden(X1,k1_relat_1(sK1)) )
    | ~ spl6_9 ),
    inference(superposition,[],[f59,f128])).

fof(f59,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | k1_funct_1(X2,X0) != X1
      | r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f152,plain,
    ( ~ spl6_6
    | ~ spl6_8
    | spl6_10
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f145,f110,f150,f113,f106])).

fof(f145,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,sK0),sK1)
        | ~ v1_funct_1(sK1)
        | ~ r2_hidden(X0,k1_relat_1(sK1))
        | ~ v1_relat_1(sK1) )
    | ~ spl6_7 ),
    inference(duplicate_literal_removal,[],[f143])).

fof(f143,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,sK0),sK1)
        | ~ v1_funct_1(sK1)
        | ~ r2_hidden(X0,k1_relat_1(sK1))
        | ~ v1_relat_1(sK1)
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl6_7 ),
    inference(superposition,[],[f59,f111])).

fof(f125,plain,(
    spl6_8 ),
    inference(avatar_contradiction_clause,[],[f124])).

fof(f124,plain,
    ( $false
    | spl6_8 ),
    inference(subsumption_resolution,[],[f26,f115])).

fof(f115,plain,
    ( ~ v1_funct_1(sK1)
    | spl6_8 ),
    inference(avatar_component_clause,[],[f113])).

fof(f26,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f123,plain,(
    spl6_6 ),
    inference(avatar_contradiction_clause,[],[f122])).

fof(f122,plain,
    ( $false
    | spl6_6 ),
    inference(subsumption_resolution,[],[f25,f108])).

fof(f108,plain,
    ( ~ v1_relat_1(sK1)
    | spl6_6 ),
    inference(avatar_component_clause,[],[f106])).

fof(f25,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f121,plain,
    ( ~ spl6_3
    | ~ spl6_4
    | spl6_9 ),
    inference(avatar_split_clause,[],[f117,f119,f90,f86])).

fof(f117,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK1))
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(forward_demodulation,[],[f104,f21])).

fof(f104,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK1))
      | ~ v1_funct_1(sK2)
      | ~ r2_hidden(X0,k1_relat_1(sK2))
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f32,f61])).

fof(f61,plain,(
    k2_relat_1(sK1) = k2_relat_1(sK2) ),
    inference(superposition,[],[f49,f48])).

fof(f48,plain,(
    k2_relat_1(sK2) = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f23,f47])).

fof(f23,plain,(
    k1_tarski(sK0) = k2_relat_1(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

fof(f116,plain,
    ( ~ spl6_6
    | spl6_7
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f103,f113,f110,f106])).

fof(f103,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK1)
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_relat_1(sK1)
      | sK0 = k1_funct_1(sK1,X0) ) ),
    inference(resolution,[],[f32,f67])).

fof(f102,plain,(
    spl6_4 ),
    inference(avatar_contradiction_clause,[],[f101])).

fof(f101,plain,
    ( $false
    | spl6_4 ),
    inference(subsumption_resolution,[],[f20,f92])).

fof(f92,plain,
    ( ~ v1_funct_1(sK2)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f90])).

fof(f20,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f98,plain,(
    spl6_3 ),
    inference(avatar_contradiction_clause,[],[f97])).

fof(f97,plain,
    ( $false
    | spl6_3 ),
    inference(subsumption_resolution,[],[f19,f88])).

fof(f88,plain,
    ( ~ v1_relat_1(sK2)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f86])).

fof(f19,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f96,plain,
    ( ~ spl6_3
    | ~ spl6_4
    | spl6_5 ),
    inference(avatar_split_clause,[],[f84,f94,f90,f86])).

fof(f84,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK2,X0),k1_relat_1(sK1))
      | r1_tarski(sK2,X0)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f75,f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:35:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.50  % (24593)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.50  % (24605)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.51  % (24586)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (24586)Refutation not found, incomplete strategy% (24586)------------------------------
% 0.21/0.51  % (24586)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (24586)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (24586)Memory used [KB]: 1791
% 0.21/0.51  % (24586)Time elapsed: 0.101 s
% 0.21/0.51  % (24586)------------------------------
% 0.21/0.51  % (24586)------------------------------
% 0.21/0.51  % (24585)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (24595)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.51  % (24610)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.52  % (24597)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.26/0.52  % (24601)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.26/0.52  % (24609)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.26/0.52  % (24596)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.26/0.52  % (24602)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.26/0.52  % (24584)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.26/0.52  % (24583)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.26/0.52  % (24588)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.26/0.52  % (24589)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.26/0.53  % (24594)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.26/0.53  % (24603)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.26/0.53  % (24607)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.26/0.53  % (24587)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.26/0.53  % (24612)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.26/0.53  % (24608)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.26/0.53  % (24582)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.26/0.53  % (24612)Refutation not found, incomplete strategy% (24612)------------------------------
% 1.26/0.53  % (24612)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.53  % (24612)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.53  
% 1.26/0.53  % (24612)Memory used [KB]: 1663
% 1.26/0.53  % (24612)Time elapsed: 0.130 s
% 1.26/0.53  % (24612)------------------------------
% 1.26/0.53  % (24612)------------------------------
% 1.39/0.54  % (24600)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.39/0.54  % (24604)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.39/0.54  % (24590)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.39/0.54  % (24606)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.39/0.54  % (24595)Refutation found. Thanks to Tanya!
% 1.39/0.54  % SZS status Theorem for theBenchmark
% 1.39/0.54  % SZS output start Proof for theBenchmark
% 1.39/0.54  fof(f472,plain,(
% 1.39/0.54    $false),
% 1.39/0.54    inference(avatar_sat_refutation,[],[f96,f98,f102,f116,f121,f123,f125,f152,f158,f263,f264,f324,f332,f349,f351,f361,f424,f437,f453,f471])).
% 1.39/0.54  fof(f471,plain,(
% 1.39/0.54    ~spl6_39),
% 1.39/0.54    inference(avatar_contradiction_clause,[],[f454])).
% 1.39/0.54  fof(f454,plain,(
% 1.39/0.54    $false | ~spl6_39),
% 1.39/0.54    inference(subsumption_resolution,[],[f24,f356])).
% 1.39/0.54  fof(f356,plain,(
% 1.39/0.54    sK1 = sK2 | ~spl6_39),
% 1.39/0.54    inference(avatar_component_clause,[],[f354])).
% 1.39/0.54  fof(f354,plain,(
% 1.39/0.54    spl6_39 <=> sK1 = sK2),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).
% 1.39/0.54  fof(f24,plain,(
% 1.39/0.54    sK1 != sK2),
% 1.39/0.54    inference(cnf_transformation,[],[f13])).
% 1.39/0.54  fof(f13,plain,(
% 1.39/0.54    ? [X0,X1] : (? [X2] : (X1 != X2 & k1_tarski(X0) = k2_relat_1(X2) & k1_tarski(X0) = k2_relat_1(X1) & k1_relat_1(X1) = k1_relat_1(X2) & v1_funct_1(X2) & v1_relat_1(X2)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.39/0.54    inference(flattening,[],[f12])).
% 1.39/0.54  fof(f12,plain,(
% 1.39/0.54    ? [X0,X1] : (? [X2] : ((X1 != X2 & (k1_tarski(X0) = k2_relat_1(X2) & k1_tarski(X0) = k2_relat_1(X1) & k1_relat_1(X1) = k1_relat_1(X2))) & (v1_funct_1(X2) & v1_relat_1(X2))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.39/0.54    inference(ennf_transformation,[],[f11])).
% 1.39/0.54  fof(f11,negated_conjecture,(
% 1.39/0.54    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_tarski(X0) = k2_relat_1(X2) & k1_tarski(X0) = k2_relat_1(X1) & k1_relat_1(X1) = k1_relat_1(X2)) => X1 = X2)))),
% 1.39/0.54    inference(negated_conjecture,[],[f10])).
% 1.39/0.54  fof(f10,conjecture,(
% 1.39/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_tarski(X0) = k2_relat_1(X2) & k1_tarski(X0) = k2_relat_1(X1) & k1_relat_1(X1) = k1_relat_1(X2)) => X1 = X2)))),
% 1.39/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_funct_1)).
% 1.39/0.54  fof(f453,plain,(
% 1.39/0.54    ~spl6_5 | spl6_40 | spl6_47),
% 1.39/0.54    inference(avatar_contradiction_clause,[],[f451])).
% 1.39/0.54  fof(f451,plain,(
% 1.39/0.54    $false | (~spl6_5 | spl6_40 | spl6_47)),
% 1.39/0.54    inference(unit_resulting_resolution,[],[f360,f436,f95])).
% 1.39/0.54  fof(f95,plain,(
% 1.39/0.54    ( ! [X0] : (r2_hidden(sK3(sK2,X0),k1_relat_1(sK1)) | r1_tarski(sK2,X0)) ) | ~spl6_5),
% 1.39/0.54    inference(avatar_component_clause,[],[f94])).
% 1.39/0.54  fof(f94,plain,(
% 1.39/0.54    spl6_5 <=> ! [X0] : (r2_hidden(sK3(sK2,X0),k1_relat_1(sK1)) | r1_tarski(sK2,X0))),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.39/0.54  fof(f436,plain,(
% 1.39/0.54    ~r2_hidden(sK3(sK2,sK1),k1_relat_1(sK1)) | spl6_47),
% 1.39/0.54    inference(avatar_component_clause,[],[f434])).
% 1.39/0.54  fof(f434,plain,(
% 1.39/0.54    spl6_47 <=> r2_hidden(sK3(sK2,sK1),k1_relat_1(sK1))),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).
% 1.39/0.54  fof(f360,plain,(
% 1.39/0.54    ~r1_tarski(sK2,sK1) | spl6_40),
% 1.39/0.54    inference(avatar_component_clause,[],[f358])).
% 1.39/0.54  fof(f358,plain,(
% 1.39/0.54    spl6_40 <=> r1_tarski(sK2,sK1)),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).
% 1.39/0.54  fof(f437,plain,(
% 1.39/0.54    ~spl6_47 | spl6_40 | ~spl6_10 | ~spl6_45),
% 1.39/0.54    inference(avatar_split_clause,[],[f431,f422,f150,f358,f434])).
% 1.39/0.54  fof(f150,plain,(
% 1.39/0.54    spl6_10 <=> ! [X0] : (r2_hidden(k4_tarski(X0,sK0),sK1) | ~r2_hidden(X0,k1_relat_1(sK1)))),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 1.39/0.54  fof(f422,plain,(
% 1.39/0.54    spl6_45 <=> ! [X2] : (~r2_hidden(k4_tarski(sK3(sK2,X2),sK0),X2) | r1_tarski(sK2,X2))),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).
% 1.39/0.54  fof(f431,plain,(
% 1.39/0.54    r1_tarski(sK2,sK1) | ~r2_hidden(sK3(sK2,sK1),k1_relat_1(sK1)) | (~spl6_10 | ~spl6_45)),
% 1.39/0.54    inference(resolution,[],[f423,f151])).
% 1.39/0.54  fof(f151,plain,(
% 1.39/0.54    ( ! [X0] : (r2_hidden(k4_tarski(X0,sK0),sK1) | ~r2_hidden(X0,k1_relat_1(sK1))) ) | ~spl6_10),
% 1.39/0.54    inference(avatar_component_clause,[],[f150])).
% 1.39/0.54  fof(f423,plain,(
% 1.39/0.54    ( ! [X2] : (~r2_hidden(k4_tarski(sK3(sK2,X2),sK0),X2) | r1_tarski(sK2,X2)) ) | ~spl6_45),
% 1.39/0.54    inference(avatar_component_clause,[],[f422])).
% 1.39/0.54  fof(f424,plain,(
% 1.39/0.54    ~spl6_3 | spl6_45 | ~spl6_5 | ~spl6_27),
% 1.39/0.54    inference(avatar_split_clause,[],[f415,f260,f94,f422,f86])).
% 1.39/0.54  fof(f86,plain,(
% 1.39/0.54    spl6_3 <=> v1_relat_1(sK2)),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.39/0.54  fof(f260,plain,(
% 1.39/0.54    spl6_27 <=> ! [X3] : (sK0 = sK4(sK2,X3) | ~r2_hidden(sK3(sK2,X3),k1_relat_1(sK1)) | r1_tarski(sK2,X3))),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 1.39/0.54  fof(f415,plain,(
% 1.39/0.54    ( ! [X2] : (~r2_hidden(k4_tarski(sK3(sK2,X2),sK0),X2) | ~v1_relat_1(sK2) | r1_tarski(sK2,X2)) ) | (~spl6_5 | ~spl6_27)),
% 1.39/0.54    inference(duplicate_literal_removal,[],[f412])).
% 1.39/0.54  fof(f412,plain,(
% 1.39/0.54    ( ! [X2] : (~r2_hidden(k4_tarski(sK3(sK2,X2),sK0),X2) | ~v1_relat_1(sK2) | r1_tarski(sK2,X2) | r1_tarski(sK2,X2)) ) | (~spl6_5 | ~spl6_27)),
% 1.39/0.54    inference(superposition,[],[f30,f410])).
% 1.39/0.54  fof(f410,plain,(
% 1.39/0.54    ( ! [X0] : (sK0 = sK4(sK2,X0) | r1_tarski(sK2,X0)) ) | (~spl6_5 | ~spl6_27)),
% 1.39/0.54    inference(duplicate_literal_removal,[],[f409])).
% 1.39/0.54  fof(f409,plain,(
% 1.39/0.54    ( ! [X0] : (sK0 = sK4(sK2,X0) | r1_tarski(sK2,X0) | r1_tarski(sK2,X0)) ) | (~spl6_5 | ~spl6_27)),
% 1.39/0.54    inference(resolution,[],[f261,f95])).
% 1.39/0.54  fof(f261,plain,(
% 1.39/0.54    ( ! [X3] : (~r2_hidden(sK3(sK2,X3),k1_relat_1(sK1)) | sK0 = sK4(sK2,X3) | r1_tarski(sK2,X3)) ) | ~spl6_27),
% 1.39/0.54    inference(avatar_component_clause,[],[f260])).
% 1.39/0.54  fof(f30,plain,(
% 1.39/0.54    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) | ~v1_relat_1(X0) | r1_tarski(X0,X1)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f14])).
% 1.39/0.54  fof(f14,plain,(
% 1.39/0.54    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | ~v1_relat_1(X0))),
% 1.39/0.54    inference(ennf_transformation,[],[f7])).
% 1.39/0.54  fof(f7,axiom,(
% 1.39/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) => r2_hidden(k4_tarski(X2,X3),X1))))),
% 1.39/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).
% 1.39/0.54  fof(f361,plain,(
% 1.39/0.54    spl6_39 | ~spl6_40 | ~spl6_38),
% 1.39/0.54    inference(avatar_split_clause,[],[f352,f346,f358,f354])).
% 1.39/0.54  fof(f346,plain,(
% 1.39/0.54    spl6_38 <=> r1_tarski(sK1,sK2)),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).
% 1.39/0.54  fof(f352,plain,(
% 1.39/0.54    ~r1_tarski(sK2,sK1) | sK1 = sK2 | ~spl6_38),
% 1.39/0.54    inference(resolution,[],[f348,f35])).
% 1.39/0.54  fof(f35,plain,(
% 1.39/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.39/0.54    inference(cnf_transformation,[],[f1])).
% 1.39/0.54  fof(f1,axiom,(
% 1.39/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.39/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.39/0.54  fof(f348,plain,(
% 1.39/0.54    r1_tarski(sK1,sK2) | ~spl6_38),
% 1.39/0.54    inference(avatar_component_clause,[],[f346])).
% 1.39/0.54  fof(f351,plain,(
% 1.39/0.54    ~spl6_6 | ~spl6_8 | spl6_38 | spl6_37),
% 1.39/0.54    inference(avatar_split_clause,[],[f350,f342,f346,f113,f106])).
% 1.39/0.54  fof(f106,plain,(
% 1.39/0.54    spl6_6 <=> v1_relat_1(sK1)),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.39/0.54  fof(f113,plain,(
% 1.39/0.54    spl6_8 <=> v1_funct_1(sK1)),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 1.39/0.54  fof(f342,plain,(
% 1.39/0.54    spl6_37 <=> r2_hidden(sK3(sK1,sK2),k1_relat_1(sK1))),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).
% 1.39/0.54  fof(f350,plain,(
% 1.39/0.54    r1_tarski(sK1,sK2) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl6_37),
% 1.39/0.54    inference(resolution,[],[f344,f75])).
% 1.39/0.54  fof(f75,plain,(
% 1.39/0.54    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),k1_relat_1(X0)) | r1_tarski(X0,X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.39/0.54    inference(duplicate_literal_removal,[],[f72])).
% 1.39/0.54  fof(f72,plain,(
% 1.39/0.54    ( ! [X0,X1] : (~v1_relat_1(X0) | r1_tarski(X0,X1) | ~v1_funct_1(X0) | r2_hidden(sK3(X0,X1),k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.39/0.54    inference(resolution,[],[f29,f41])).
% 1.39/0.54  fof(f41,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | r2_hidden(X0,k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f18])).
% 1.39/0.54  fof(f18,plain,(
% 1.39/0.54    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.39/0.54    inference(flattening,[],[f17])).
% 1.39/0.54  fof(f17,plain,(
% 1.39/0.54    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.39/0.54    inference(ennf_transformation,[],[f9])).
% 1.39/0.54  fof(f9,axiom,(
% 1.39/0.54    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.39/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 1.39/0.54  fof(f29,plain,(
% 1.39/0.54    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) | ~v1_relat_1(X0) | r1_tarski(X0,X1)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f14])).
% 1.39/0.54  fof(f344,plain,(
% 1.39/0.54    ~r2_hidden(sK3(sK1,sK2),k1_relat_1(sK1)) | spl6_37),
% 1.39/0.54    inference(avatar_component_clause,[],[f342])).
% 1.39/0.54  fof(f349,plain,(
% 1.39/0.54    ~spl6_37 | spl6_38 | ~spl6_11 | ~spl6_35),
% 1.39/0.54    inference(avatar_split_clause,[],[f340,f330,f156,f346,f342])).
% 1.39/0.54  fof(f156,plain,(
% 1.39/0.54    spl6_11 <=> ! [X1] : (~r2_hidden(X1,k1_relat_1(sK1)) | r2_hidden(k4_tarski(X1,sK0),sK2))),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 1.39/0.54  fof(f330,plain,(
% 1.39/0.54    spl6_35 <=> ! [X0] : (~r2_hidden(k4_tarski(sK3(sK1,X0),sK0),X0) | r1_tarski(sK1,X0))),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).
% 1.39/0.54  fof(f340,plain,(
% 1.39/0.54    r1_tarski(sK1,sK2) | ~r2_hidden(sK3(sK1,sK2),k1_relat_1(sK1)) | (~spl6_11 | ~spl6_35)),
% 1.39/0.54    inference(resolution,[],[f331,f157])).
% 1.39/0.54  fof(f157,plain,(
% 1.39/0.54    ( ! [X1] : (r2_hidden(k4_tarski(X1,sK0),sK2) | ~r2_hidden(X1,k1_relat_1(sK1))) ) | ~spl6_11),
% 1.39/0.54    inference(avatar_component_clause,[],[f156])).
% 1.39/0.54  fof(f331,plain,(
% 1.39/0.54    ( ! [X0] : (~r2_hidden(k4_tarski(sK3(sK1,X0),sK0),X0) | r1_tarski(sK1,X0)) ) | ~spl6_35),
% 1.39/0.54    inference(avatar_component_clause,[],[f330])).
% 1.39/0.54  fof(f332,plain,(
% 1.39/0.54    ~spl6_6 | spl6_35 | ~spl6_34),
% 1.39/0.54    inference(avatar_split_clause,[],[f328,f322,f330,f106])).
% 1.39/0.54  fof(f322,plain,(
% 1.39/0.54    spl6_34 <=> ! [X0] : (sK0 = sK4(sK1,X0) | r1_tarski(sK1,X0))),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 1.39/0.54  fof(f328,plain,(
% 1.39/0.54    ( ! [X0] : (~r2_hidden(k4_tarski(sK3(sK1,X0),sK0),X0) | ~v1_relat_1(sK1) | r1_tarski(sK1,X0)) ) | ~spl6_34),
% 1.39/0.54    inference(duplicate_literal_removal,[],[f325])).
% 1.39/0.54  fof(f325,plain,(
% 1.39/0.54    ( ! [X0] : (~r2_hidden(k4_tarski(sK3(sK1,X0),sK0),X0) | ~v1_relat_1(sK1) | r1_tarski(sK1,X0) | r1_tarski(sK1,X0)) ) | ~spl6_34),
% 1.39/0.54    inference(superposition,[],[f30,f323])).
% 1.39/0.54  fof(f323,plain,(
% 1.39/0.54    ( ! [X0] : (sK0 = sK4(sK1,X0) | r1_tarski(sK1,X0)) ) | ~spl6_34),
% 1.39/0.54    inference(avatar_component_clause,[],[f322])).
% 1.39/0.54  fof(f324,plain,(
% 1.39/0.54    ~spl6_6 | ~spl6_8 | spl6_34 | ~spl6_26),
% 1.39/0.54    inference(avatar_split_clause,[],[f320,f256,f322,f113,f106])).
% 1.39/0.54  fof(f256,plain,(
% 1.39/0.54    spl6_26 <=> ! [X2] : (sK0 = sK4(sK1,X2) | ~r2_hidden(sK3(sK1,X2),k1_relat_1(sK1)) | r1_tarski(sK1,X2))),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 1.39/0.54  fof(f320,plain,(
% 1.39/0.54    ( ! [X0] : (sK0 = sK4(sK1,X0) | r1_tarski(sK1,X0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) ) | ~spl6_26),
% 1.39/0.54    inference(duplicate_literal_removal,[],[f319])).
% 1.39/0.54  fof(f319,plain,(
% 1.39/0.54    ( ! [X0] : (sK0 = sK4(sK1,X0) | r1_tarski(sK1,X0) | r1_tarski(sK1,X0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) ) | ~spl6_26),
% 1.39/0.54    inference(resolution,[],[f257,f75])).
% 1.39/0.54  fof(f257,plain,(
% 1.39/0.54    ( ! [X2] : (~r2_hidden(sK3(sK1,X2),k1_relat_1(sK1)) | sK0 = sK4(sK1,X2) | r1_tarski(sK1,X2)) ) | ~spl6_26),
% 1.39/0.54    inference(avatar_component_clause,[],[f256])).
% 1.39/0.54  fof(f264,plain,(
% 1.39/0.54    ~spl6_3 | ~spl6_4 | spl6_27 | ~spl6_9),
% 1.39/0.54    inference(avatar_split_clause,[],[f251,f119,f260,f90,f86])).
% 1.39/0.54  fof(f90,plain,(
% 1.39/0.54    spl6_4 <=> v1_funct_1(sK2)),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.39/0.54  fof(f119,plain,(
% 1.39/0.54    spl6_9 <=> ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK1)))),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 1.39/0.54  fof(f251,plain,(
% 1.39/0.54    ( ! [X5] : (sK0 = sK4(sK2,X5) | ~r2_hidden(sK3(sK2,X5),k1_relat_1(sK1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | r1_tarski(sK2,X5)) ) | ~spl6_9),
% 1.39/0.54    inference(superposition,[],[f128,f134])).
% 1.39/0.54  fof(f134,plain,(
% 1.39/0.54    ( ! [X0,X1] : (sK4(X0,X1) = k1_funct_1(X0,sK3(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | r1_tarski(X0,X1)) )),
% 1.39/0.54    inference(duplicate_literal_removal,[],[f132])).
% 1.39/0.54  fof(f132,plain,(
% 1.39/0.54    ( ! [X0,X1] : (~v1_funct_1(X0) | sK4(X0,X1) = k1_funct_1(X0,sK3(X0,X1)) | ~v1_relat_1(X0) | ~v1_relat_1(X0) | r1_tarski(X0,X1)) )),
% 1.39/0.54    inference(resolution,[],[f42,f29])).
% 1.39/0.54  fof(f42,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | k1_funct_1(X2,X0) = X1 | ~v1_relat_1(X2)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f18])).
% 1.39/0.54  fof(f128,plain,(
% 1.39/0.54    ( ! [X0] : (sK0 = k1_funct_1(sK2,X0) | ~r2_hidden(X0,k1_relat_1(sK1))) ) | ~spl6_9),
% 1.39/0.54    inference(resolution,[],[f120,f67])).
% 1.39/0.54  fof(f67,plain,(
% 1.39/0.54    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | sK0 = X0) )),
% 1.39/0.54    inference(superposition,[],[f56,f49])).
% 1.39/0.54  fof(f49,plain,(
% 1.39/0.54    k2_relat_1(sK1) = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 1.39/0.54    inference(definition_unfolding,[],[f22,f47])).
% 1.39/0.54  fof(f47,plain,(
% 1.39/0.54    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.39/0.54    inference(definition_unfolding,[],[f27,f46])).
% 1.39/0.54  fof(f46,plain,(
% 1.39/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.39/0.54    inference(definition_unfolding,[],[f31,f45])).
% 1.39/0.54  fof(f45,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.39/0.54    inference(definition_unfolding,[],[f40,f44])).
% 1.39/0.54  fof(f44,plain,(
% 1.39/0.54    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f6])).
% 1.39/0.54  fof(f6,axiom,(
% 1.39/0.54    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.39/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.39/0.54  fof(f40,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f5])).
% 1.39/0.54  fof(f5,axiom,(
% 1.39/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.39/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.39/0.54  fof(f31,plain,(
% 1.39/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f4])).
% 1.39/0.54  fof(f4,axiom,(
% 1.39/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.39/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.39/0.54  fof(f27,plain,(
% 1.39/0.54    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f3])).
% 1.39/0.54  fof(f3,axiom,(
% 1.39/0.54    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.39/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.39/0.54  fof(f22,plain,(
% 1.39/0.54    k1_tarski(sK0) = k2_relat_1(sK1)),
% 1.39/0.54    inference(cnf_transformation,[],[f13])).
% 1.39/0.54  fof(f56,plain,(
% 1.39/0.54    ( ! [X2,X0] : (~r2_hidden(X2,k3_enumset1(X0,X0,X0,X0,X0)) | X0 = X2) )),
% 1.39/0.54    inference(equality_resolution,[],[f52])).
% 1.39/0.54  fof(f52,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 1.39/0.54    inference(definition_unfolding,[],[f37,f47])).
% 1.39/0.54  fof(f37,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.39/0.54    inference(cnf_transformation,[],[f2])).
% 1.39/0.54  fof(f2,axiom,(
% 1.39/0.54    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.39/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.39/0.54  fof(f120,plain,(
% 1.39/0.54    ( ! [X0] : (r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK1)) | ~r2_hidden(X0,k1_relat_1(sK1))) ) | ~spl6_9),
% 1.39/0.54    inference(avatar_component_clause,[],[f119])).
% 1.39/0.54  fof(f263,plain,(
% 1.39/0.54    ~spl6_6 | ~spl6_8 | spl6_26 | ~spl6_7),
% 1.39/0.54    inference(avatar_split_clause,[],[f250,f110,f256,f113,f106])).
% 1.39/0.54  fof(f110,plain,(
% 1.39/0.54    spl6_7 <=> ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | sK0 = k1_funct_1(sK1,X0))),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.39/0.54  fof(f250,plain,(
% 1.39/0.54    ( ! [X4] : (sK0 = sK4(sK1,X4) | ~r2_hidden(sK3(sK1,X4),k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | r1_tarski(sK1,X4)) ) | ~spl6_7),
% 1.39/0.54    inference(superposition,[],[f111,f134])).
% 1.39/0.54  fof(f111,plain,(
% 1.39/0.54    ( ! [X0] : (sK0 = k1_funct_1(sK1,X0) | ~r2_hidden(X0,k1_relat_1(sK1))) ) | ~spl6_7),
% 1.39/0.54    inference(avatar_component_clause,[],[f110])).
% 1.39/0.54  fof(f158,plain,(
% 1.39/0.54    ~spl6_3 | ~spl6_4 | spl6_11 | ~spl6_9),
% 1.39/0.54    inference(avatar_split_clause,[],[f154,f119,f156,f90,f86])).
% 1.39/0.54  fof(f154,plain,(
% 1.39/0.54    ( ! [X1] : (~r2_hidden(X1,k1_relat_1(sK1)) | r2_hidden(k4_tarski(X1,sK0),sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl6_9),
% 1.39/0.54    inference(duplicate_literal_removal,[],[f153])).
% 1.39/0.54  fof(f153,plain,(
% 1.39/0.54    ( ! [X1] : (~r2_hidden(X1,k1_relat_1(sK1)) | r2_hidden(k4_tarski(X1,sK0),sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~r2_hidden(X1,k1_relat_1(sK1))) ) | ~spl6_9),
% 1.39/0.54    inference(forward_demodulation,[],[f144,f21])).
% 1.39/0.54  fof(f21,plain,(
% 1.39/0.54    k1_relat_1(sK1) = k1_relat_1(sK2)),
% 1.39/0.54    inference(cnf_transformation,[],[f13])).
% 1.39/0.54  % (24591)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.39/0.54  fof(f144,plain,(
% 1.39/0.54    ( ! [X1] : (r2_hidden(k4_tarski(X1,sK0),sK2) | ~v1_funct_1(sK2) | ~r2_hidden(X1,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | ~r2_hidden(X1,k1_relat_1(sK1))) ) | ~spl6_9),
% 1.39/0.54    inference(superposition,[],[f59,f128])).
% 1.39/0.54  fof(f59,plain,(
% 1.39/0.54    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 1.39/0.54    inference(equality_resolution,[],[f43])).
% 1.39/0.54  fof(f43,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | k1_funct_1(X2,X0) != X1 | r2_hidden(k4_tarski(X0,X1),X2)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f18])).
% 1.39/0.54  fof(f152,plain,(
% 1.39/0.54    ~spl6_6 | ~spl6_8 | spl6_10 | ~spl6_7),
% 1.39/0.54    inference(avatar_split_clause,[],[f145,f110,f150,f113,f106])).
% 1.39/0.54  fof(f145,plain,(
% 1.39/0.54    ( ! [X0] : (r2_hidden(k4_tarski(X0,sK0),sK1) | ~v1_funct_1(sK1) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_relat_1(sK1)) ) | ~spl6_7),
% 1.39/0.54    inference(duplicate_literal_removal,[],[f143])).
% 1.39/0.54  fof(f143,plain,(
% 1.39/0.54    ( ! [X0] : (r2_hidden(k4_tarski(X0,sK0),sK1) | ~v1_funct_1(sK1) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_relat_1(sK1) | ~r2_hidden(X0,k1_relat_1(sK1))) ) | ~spl6_7),
% 1.39/0.54    inference(superposition,[],[f59,f111])).
% 1.39/0.54  fof(f125,plain,(
% 1.39/0.54    spl6_8),
% 1.39/0.54    inference(avatar_contradiction_clause,[],[f124])).
% 1.39/0.54  fof(f124,plain,(
% 1.39/0.54    $false | spl6_8),
% 1.39/0.54    inference(subsumption_resolution,[],[f26,f115])).
% 1.39/0.54  fof(f115,plain,(
% 1.39/0.54    ~v1_funct_1(sK1) | spl6_8),
% 1.39/0.54    inference(avatar_component_clause,[],[f113])).
% 1.39/0.54  fof(f26,plain,(
% 1.39/0.54    v1_funct_1(sK1)),
% 1.39/0.54    inference(cnf_transformation,[],[f13])).
% 1.39/0.54  fof(f123,plain,(
% 1.39/0.54    spl6_6),
% 1.39/0.54    inference(avatar_contradiction_clause,[],[f122])).
% 1.39/0.54  fof(f122,plain,(
% 1.39/0.54    $false | spl6_6),
% 1.39/0.54    inference(subsumption_resolution,[],[f25,f108])).
% 1.39/0.54  fof(f108,plain,(
% 1.39/0.54    ~v1_relat_1(sK1) | spl6_6),
% 1.39/0.54    inference(avatar_component_clause,[],[f106])).
% 1.39/0.54  fof(f25,plain,(
% 1.39/0.54    v1_relat_1(sK1)),
% 1.39/0.54    inference(cnf_transformation,[],[f13])).
% 1.39/0.54  fof(f121,plain,(
% 1.39/0.54    ~spl6_3 | ~spl6_4 | spl6_9),
% 1.39/0.54    inference(avatar_split_clause,[],[f117,f119,f90,f86])).
% 1.39/0.54  fof(f117,plain,(
% 1.39/0.54    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK1)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 1.39/0.54    inference(forward_demodulation,[],[f104,f21])).
% 1.39/0.54  fof(f104,plain,(
% 1.39/0.54    ( ! [X0] : (r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK1)) | ~v1_funct_1(sK2) | ~r2_hidden(X0,k1_relat_1(sK2)) | ~v1_relat_1(sK2)) )),
% 1.39/0.54    inference(superposition,[],[f32,f61])).
% 1.39/0.54  fof(f61,plain,(
% 1.39/0.54    k2_relat_1(sK1) = k2_relat_1(sK2)),
% 1.39/0.54    inference(superposition,[],[f49,f48])).
% 1.39/0.54  fof(f48,plain,(
% 1.39/0.54    k2_relat_1(sK2) = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 1.39/0.54    inference(definition_unfolding,[],[f23,f47])).
% 1.39/0.54  fof(f23,plain,(
% 1.39/0.54    k1_tarski(sK0) = k2_relat_1(sK2)),
% 1.39/0.54    inference(cnf_transformation,[],[f13])).
% 1.39/0.54  fof(f32,plain,(
% 1.39/0.54    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~v1_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f16])).
% 1.39/0.54  fof(f16,plain,(
% 1.39/0.54    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.39/0.54    inference(flattening,[],[f15])).
% 1.39/0.54  fof(f15,plain,(
% 1.39/0.54    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.39/0.54    inference(ennf_transformation,[],[f8])).
% 1.39/0.54  fof(f8,axiom,(
% 1.39/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 1.39/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).
% 1.39/0.54  fof(f116,plain,(
% 1.39/0.54    ~spl6_6 | spl6_7 | ~spl6_8),
% 1.39/0.54    inference(avatar_split_clause,[],[f103,f113,f110,f106])).
% 1.39/0.54  fof(f103,plain,(
% 1.39/0.54    ( ! [X0] : (~v1_funct_1(sK1) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_relat_1(sK1) | sK0 = k1_funct_1(sK1,X0)) )),
% 1.39/0.54    inference(resolution,[],[f32,f67])).
% 1.39/0.54  fof(f102,plain,(
% 1.39/0.54    spl6_4),
% 1.39/0.54    inference(avatar_contradiction_clause,[],[f101])).
% 1.39/0.54  fof(f101,plain,(
% 1.39/0.54    $false | spl6_4),
% 1.39/0.54    inference(subsumption_resolution,[],[f20,f92])).
% 1.39/0.54  fof(f92,plain,(
% 1.39/0.54    ~v1_funct_1(sK2) | spl6_4),
% 1.39/0.54    inference(avatar_component_clause,[],[f90])).
% 1.39/0.54  fof(f20,plain,(
% 1.39/0.54    v1_funct_1(sK2)),
% 1.39/0.54    inference(cnf_transformation,[],[f13])).
% 1.39/0.54  fof(f98,plain,(
% 1.39/0.54    spl6_3),
% 1.39/0.54    inference(avatar_contradiction_clause,[],[f97])).
% 1.39/0.54  fof(f97,plain,(
% 1.39/0.54    $false | spl6_3),
% 1.39/0.54    inference(subsumption_resolution,[],[f19,f88])).
% 1.39/0.54  fof(f88,plain,(
% 1.39/0.54    ~v1_relat_1(sK2) | spl6_3),
% 1.39/0.54    inference(avatar_component_clause,[],[f86])).
% 1.39/0.54  fof(f19,plain,(
% 1.39/0.54    v1_relat_1(sK2)),
% 1.39/0.54    inference(cnf_transformation,[],[f13])).
% 1.39/0.54  fof(f96,plain,(
% 1.39/0.54    ~spl6_3 | ~spl6_4 | spl6_5),
% 1.39/0.54    inference(avatar_split_clause,[],[f84,f94,f90,f86])).
% 1.39/0.54  fof(f84,plain,(
% 1.39/0.54    ( ! [X0] : (r2_hidden(sK3(sK2,X0),k1_relat_1(sK1)) | r1_tarski(sK2,X0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 1.39/0.54    inference(superposition,[],[f75,f21])).
% 1.39/0.54  % SZS output end Proof for theBenchmark
% 1.39/0.54  % (24595)------------------------------
% 1.39/0.54  % (24595)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.54  % (24598)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.39/0.54  % (24595)Termination reason: Refutation
% 1.39/0.54  
% 1.39/0.54  % (24595)Memory used [KB]: 6524
% 1.39/0.54  % (24595)Time elapsed: 0.141 s
% 1.39/0.54  % (24595)------------------------------
% 1.39/0.54  % (24595)------------------------------
% 1.39/0.54  % (24581)Success in time 0.181 s
%------------------------------------------------------------------------------
