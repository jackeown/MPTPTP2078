%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:58 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 232 expanded)
%              Number of leaves         :   35 (  95 expanded)
%              Depth                    :   11
%              Number of atoms          :  448 ( 866 expanded)
%              Number of equality atoms :   95 ( 187 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f762,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f92,f97,f102,f107,f118,f133,f149,f155,f165,f176,f191,f196,f431,f439,f512,f756])).

fof(f756,plain,
    ( ~ spl13_4
    | ~ spl13_5
    | spl13_10
    | ~ spl13_13
    | ~ spl13_14
    | ~ spl13_40 ),
    inference(avatar_contradiction_clause,[],[f755])).

fof(f755,plain,
    ( $false
    | ~ spl13_4
    | ~ spl13_5
    | spl13_10
    | ~ spl13_13
    | ~ spl13_14
    | ~ spl13_40 ),
    inference(subsumption_resolution,[],[f754,f190])).

fof(f190,plain,
    ( r2_hidden(sK10(sK11(sK9,sK8)),sK7)
    | ~ spl13_13 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl13_13
  <=> r2_hidden(sK10(sK11(sK9,sK8)),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_13])])).

fof(f754,plain,
    ( ~ r2_hidden(sK10(sK11(sK9,sK8)),sK7)
    | ~ spl13_4
    | ~ spl13_5
    | spl13_10
    | ~ spl13_14
    | ~ spl13_40 ),
    inference(forward_demodulation,[],[f753,f427])).

fof(f427,plain,
    ( sK7 = k1_relat_1(sK9)
    | ~ spl13_40 ),
    inference(avatar_component_clause,[],[f425])).

fof(f425,plain,
    ( spl13_40
  <=> sK7 = k1_relat_1(sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_40])])).

fof(f753,plain,
    ( ~ r2_hidden(sK10(sK11(sK9,sK8)),k1_relat_1(sK9))
    | ~ spl13_4
    | ~ spl13_5
    | spl13_10
    | ~ spl13_14 ),
    inference(subsumption_resolution,[],[f752,f119])).

fof(f119,plain,
    ( ! [X0,X1] : sP0(sK9,X0,X1)
    | ~ spl13_4
    | ~ spl13_5 ),
    inference(unit_resulting_resolution,[],[f115,f106,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X2,X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( sP1(X2,X1,X0)
          & sP0(X0,X2,X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f15,f22,f21])).

fof(f21,plain,(
    ! [X0,X2,X1] :
      ( ( k1_funct_1(X0,X1) = X2
      <=> r2_hidden(k4_tarski(X1,X2),X0) )
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ( k1_funct_1(X0,X1) = X2
      <=> k1_xboole_0 = X2 )
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ sP1(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

fof(f106,plain,
    ( v1_funct_1(sK9)
    | ~ spl13_4 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl13_4
  <=> v1_funct_1(sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).

fof(f115,plain,
    ( v1_relat_1(sK9)
    | ~ spl13_5 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl13_5
  <=> v1_relat_1(sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_5])])).

fof(f752,plain,
    ( ~ r2_hidden(sK10(sK11(sK9,sK8)),k1_relat_1(sK9))
    | ~ sP0(sK9,sK11(sK9,sK8),sK10(sK11(sK9,sK8)))
    | spl13_10
    | ~ spl13_14 ),
    inference(subsumption_resolution,[],[f736,f169])).

fof(f169,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK11(sK9,sK8)),sK9)
    | spl13_10 ),
    inference(unit_resulting_resolution,[],[f162,f79])).

fof(f79,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,sK11(X0,X1)),X0)
      | sP5(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( sP5(X0,X1)
        | ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK11(X0,X1)),X0)
          & r2_hidden(sK11(X0,X1),X1) ) )
      & ( ! [X4] :
            ( r2_hidden(k4_tarski(sK12(X0,X4),X4),X0)
            | ~ r2_hidden(X4,X1) )
        | ~ sP5(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12])],[f46,f48,f47])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
          & r2_hidden(X2,X1) )
     => ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK11(X0,X1)),X0)
        & r2_hidden(sK11(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X4,X0] :
      ( ? [X5] : r2_hidden(k4_tarski(X5,X4),X0)
     => r2_hidden(k4_tarski(sK12(X0,X4),X4),X0) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( sP5(X0,X1)
        | ? [X2] :
            ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            & r2_hidden(X2,X1) ) )
      & ( ! [X4] :
            ( ? [X5] : r2_hidden(k4_tarski(X5,X4),X0)
            | ~ r2_hidden(X4,X1) )
        | ~ sP5(X0,X1) ) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X2,X1] :
      ( ( sP5(X2,X1)
        | ? [X3] :
            ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
            & r2_hidden(X3,X1) ) )
      & ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
            | ~ r2_hidden(X3,X1) )
        | ~ sP5(X2,X1) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X2,X1] :
      ( sP5(X2,X1)
    <=> ! [X3] :
          ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
          | ~ r2_hidden(X3,X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f162,plain,
    ( ~ sP5(sK9,sK8)
    | spl13_10 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl13_10
  <=> sP5(sK9,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_10])])).

fof(f736,plain,
    ( r2_hidden(k4_tarski(sK10(sK11(sK9,sK8)),sK11(sK9,sK8)),sK9)
    | ~ r2_hidden(sK10(sK11(sK9,sK8)),k1_relat_1(sK9))
    | ~ sP0(sK9,sK11(sK9,sK8),sK10(sK11(sK9,sK8)))
    | ~ spl13_14 ),
    inference(superposition,[],[f83,f195])).

fof(f195,plain,
    ( sK11(sK9,sK8) = k1_funct_1(sK9,sK10(sK11(sK9,sK8)))
    | ~ spl13_14 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl13_14
  <=> sK11(sK9,sK8) = k1_funct_1(sK9,sK10(sK11(sK9,sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_14])])).

fof(f83,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,k1_funct_1(X0,X2)),X0)
      | ~ r2_hidden(X2,k1_relat_1(X0))
      | ~ sP0(X0,k1_funct_1(X0,X2),X2) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,X1),X0)
      | k1_funct_1(X0,X2) != X1
      | ~ r2_hidden(X2,k1_relat_1(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_funct_1(X0,X2) = X1
          | ~ r2_hidden(k4_tarski(X2,X1),X0) )
        & ( r2_hidden(k4_tarski(X2,X1),X0)
          | k1_funct_1(X0,X2) != X1 ) )
      | ~ r2_hidden(X2,k1_relat_1(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0,X2,X1] :
      ( ( ( k1_funct_1(X0,X1) = X2
          | ~ r2_hidden(k4_tarski(X1,X2),X0) )
        & ( r2_hidden(k4_tarski(X1,X2),X0)
          | k1_funct_1(X0,X1) != X2 ) )
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f512,plain,
    ( spl13_10
    | ~ spl13_41 ),
    inference(avatar_contradiction_clause,[],[f511])).

fof(f511,plain,
    ( $false
    | spl13_10
    | ~ spl13_41 ),
    inference(subsumption_resolution,[],[f453,f121])).

fof(f121,plain,(
    ! [X0] : sP5(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f108,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK11(X0,X1),X1)
      | sP5(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f108,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f56,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f56,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f453,plain,
    ( ~ sP5(sK9,k1_xboole_0)
    | spl13_10
    | ~ spl13_41 ),
    inference(backward_demodulation,[],[f162,f437])).

fof(f437,plain,
    ( k1_xboole_0 = sK8
    | ~ spl13_41 ),
    inference(avatar_component_clause,[],[f435])).

fof(f435,plain,
    ( spl13_41
  <=> k1_xboole_0 = sK8 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_41])])).

fof(f439,plain,
    ( spl13_41
    | ~ spl13_39 ),
    inference(avatar_split_clause,[],[f433,f421,f435])).

fof(f421,plain,
    ( spl13_39
  <=> sP2(sK7,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_39])])).

fof(f433,plain,
    ( k1_xboole_0 = sK8
    | ~ spl13_39 ),
    inference(resolution,[],[f423,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ sP2(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP2(X0,X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP2(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f423,plain,
    ( sP2(sK7,sK8)
    | ~ spl13_39 ),
    inference(avatar_component_clause,[],[f421])).

fof(f431,plain,
    ( spl13_39
    | spl13_40
    | ~ spl13_3
    | ~ spl13_6
    | ~ spl13_9 ),
    inference(avatar_split_clause,[],[f430,f152,f129,f99,f425,f421])).

fof(f99,plain,
    ( spl13_3
  <=> v1_funct_2(sK9,sK7,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).

fof(f129,plain,
    ( spl13_6
  <=> sP3(sK7,sK9,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_6])])).

fof(f152,plain,
    ( spl13_9
  <=> k1_relset_1(sK7,sK8,sK9) = k1_relat_1(sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_9])])).

fof(f430,plain,
    ( sK7 = k1_relat_1(sK9)
    | sP2(sK7,sK8)
    | ~ spl13_3
    | ~ spl13_6
    | ~ spl13_9 ),
    inference(subsumption_resolution,[],[f429,f131])).

fof(f131,plain,
    ( sP3(sK7,sK9,sK8)
    | ~ spl13_6 ),
    inference(avatar_component_clause,[],[f129])).

fof(f429,plain,
    ( sK7 = k1_relat_1(sK9)
    | sP2(sK7,sK8)
    | ~ sP3(sK7,sK9,sK8)
    | ~ spl13_3
    | ~ spl13_9 ),
    inference(subsumption_resolution,[],[f416,f101])).

fof(f101,plain,
    ( v1_funct_2(sK9,sK7,sK8)
    | ~ spl13_3 ),
    inference(avatar_component_clause,[],[f99])).

fof(f416,plain,
    ( sK7 = k1_relat_1(sK9)
    | ~ v1_funct_2(sK9,sK7,sK8)
    | sP2(sK7,sK8)
    | ~ sP3(sK7,sK9,sK8)
    | ~ spl13_9 ),
    inference(superposition,[],[f154,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | sP2(X0,X2)
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP2(X0,X2)
      | ~ sP3(X0,X1,X2) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP2(X0,X1)
      | ~ sP3(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP2(X0,X1)
      | ~ sP3(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f154,plain,
    ( k1_relset_1(sK7,sK8,sK9) = k1_relat_1(sK9)
    | ~ spl13_9 ),
    inference(avatar_component_clause,[],[f152])).

fof(f196,plain,
    ( spl13_14
    | ~ spl13_11 ),
    inference(avatar_split_clause,[],[f183,f173,f193])).

fof(f173,plain,
    ( spl13_11
  <=> r2_hidden(sK11(sK9,sK8),sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_11])])).

fof(f183,plain,
    ( sK11(sK9,sK8) = k1_funct_1(sK9,sK10(sK11(sK9,sK8)))
    | ~ spl13_11 ),
    inference(unit_resulting_resolution,[],[f175,f54])).

fof(f54,plain,(
    ! [X3] :
      ( k1_funct_1(sK9,sK10(X3)) = X3
      | ~ r2_hidden(X3,sK8) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( sK8 != k2_relset_1(sK7,sK8,sK9)
    & ! [X3] :
        ( ( k1_funct_1(sK9,sK10(X3)) = X3
          & r2_hidden(sK10(X3),sK7) )
        | ~ r2_hidden(X3,sK8) )
    & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    & v1_funct_2(sK9,sK7,sK8)
    & v1_funct_1(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10])],[f12,f32,f31])).

fof(f31,plain,
    ( ? [X0,X1,X2] :
        ( k2_relset_1(X0,X1,X2) != X1
        & ! [X3] :
            ( ? [X4] :
                ( k1_funct_1(X2,X4) = X3
                & r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X1) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( sK8 != k2_relset_1(sK7,sK8,sK9)
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(sK9,X4) = X3
              & r2_hidden(X4,sK7) )
          | ~ r2_hidden(X3,sK8) )
      & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
      & v1_funct_2(sK9,sK7,sK8)
      & v1_funct_1(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X3] :
      ( ? [X4] :
          ( k1_funct_1(sK9,X4) = X3
          & r2_hidden(X4,sK7) )
     => ( k1_funct_1(sK9,sK10(X3)) = X3
        & r2_hidden(sK10(X3),sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ! [X3] :
              ~ ( ! [X4] :
                    ~ ( k1_funct_1(X2,X4) = X3
                      & r2_hidden(X4,X0) )
                & r2_hidden(X3,X1) )
         => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ! [X3] :
            ~ ( ! [X4] :
                  ~ ( k1_funct_1(X2,X4) = X3
                    & r2_hidden(X4,X0) )
              & r2_hidden(X3,X1) )
       => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).

fof(f175,plain,
    ( r2_hidden(sK11(sK9,sK8),sK8)
    | ~ spl13_11 ),
    inference(avatar_component_clause,[],[f173])).

fof(f191,plain,
    ( spl13_13
    | ~ spl13_11 ),
    inference(avatar_split_clause,[],[f184,f173,f188])).

fof(f184,plain,
    ( r2_hidden(sK10(sK11(sK9,sK8)),sK7)
    | ~ spl13_11 ),
    inference(unit_resulting_resolution,[],[f175,f53])).

fof(f53,plain,(
    ! [X3] :
      ( r2_hidden(sK10(X3),sK7)
      | ~ r2_hidden(X3,sK8) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f176,plain,
    ( spl13_11
    | spl13_10 ),
    inference(avatar_split_clause,[],[f171,f160,f173])).

fof(f171,plain,
    ( r2_hidden(sK11(sK9,sK8),sK8)
    | spl13_10 ),
    inference(unit_resulting_resolution,[],[f162,f78])).

fof(f165,plain,
    ( ~ spl13_10
    | spl13_1
    | ~ spl13_8 ),
    inference(avatar_split_clause,[],[f164,f145,f89,f160])).

fof(f89,plain,
    ( spl13_1
  <=> sK8 = k2_relset_1(sK7,sK8,sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f145,plain,
    ( spl13_8
  <=> sP6(sK8,sK9,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_8])])).

fof(f164,plain,
    ( ~ sP5(sK9,sK8)
    | spl13_1
    | ~ spl13_8 ),
    inference(subsumption_resolution,[],[f158,f147])).

fof(f147,plain,
    ( sP6(sK8,sK9,sK7)
    | ~ spl13_8 ),
    inference(avatar_component_clause,[],[f145])).

fof(f158,plain,
    ( ~ sP5(sK9,sK8)
    | ~ sP6(sK8,sK9,sK7)
    | spl13_1 ),
    inference(trivial_inequality_removal,[],[f157])).

fof(f157,plain,
    ( sK8 != sK8
    | ~ sP5(sK9,sK8)
    | ~ sP6(sK8,sK9,sK7)
    | spl13_1 ),
    inference(superposition,[],[f91,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X2,X0,X1) = X0
      | ~ sP5(X1,X0)
      | ~ sP6(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( ( sP5(X1,X0)
          | k2_relset_1(X2,X0,X1) != X0 )
        & ( k2_relset_1(X2,X0,X1) = X0
          | ~ sP5(X1,X0) ) )
      | ~ sP6(X0,X1,X2) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X1,X2,X0] :
      ( ( ( sP5(X2,X1)
          | k2_relset_1(X0,X1,X2) != X1 )
        & ( k2_relset_1(X0,X1,X2) = X1
          | ~ sP5(X2,X1) ) )
      | ~ sP6(X1,X2,X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X1,X2,X0] :
      ( ( sP5(X2,X1)
      <=> k2_relset_1(X0,X1,X2) = X1 )
      | ~ sP6(X1,X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).

fof(f91,plain,
    ( sK8 != k2_relset_1(sK7,sK8,sK9)
    | spl13_1 ),
    inference(avatar_component_clause,[],[f89])).

fof(f155,plain,
    ( spl13_9
    | ~ spl13_2 ),
    inference(avatar_split_clause,[],[f150,f94,f152])).

fof(f94,plain,
    ( spl13_2
  <=> m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f150,plain,
    ( k1_relset_1(sK7,sK8,sK9) = k1_relat_1(sK9)
    | ~ spl13_2 ),
    inference(unit_resulting_resolution,[],[f96,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f96,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ spl13_2 ),
    inference(avatar_component_clause,[],[f94])).

fof(f149,plain,
    ( spl13_8
    | ~ spl13_2 ),
    inference(avatar_split_clause,[],[f143,f94,f145])).

fof(f143,plain,
    ( sP6(sK8,sK9,sK7)
    | ~ spl13_2 ),
    inference(resolution,[],[f80,f96])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP6(X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( sP6(X1,X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f20,f29,f28])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k2_relset_1(X0,X1,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
              & r2_hidden(X3,X1) )
      <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relset_1)).

fof(f133,plain,
    ( spl13_6
    | ~ spl13_2 ),
    inference(avatar_split_clause,[],[f127,f94,f129])).

fof(f127,plain,
    ( sP3(sK7,sK9,sK8)
    | ~ spl13_2 ),
    inference(resolution,[],[f73,f96])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP3(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X2,X1,X0)
        & sP3(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f19,f26,f25,f24])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP4(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f118,plain,
    ( spl13_5
    | ~ spl13_2 ),
    inference(avatar_split_clause,[],[f117,f94,f113])).

fof(f117,plain,
    ( v1_relat_1(sK9)
    | ~ spl13_2 ),
    inference(subsumption_resolution,[],[f111,f64])).

fof(f64,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f111,plain,
    ( v1_relat_1(sK9)
    | ~ v1_relat_1(k2_zfmisc_1(sK7,sK8))
    | ~ spl13_2 ),
    inference(resolution,[],[f57,f96])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f107,plain,(
    spl13_4 ),
    inference(avatar_split_clause,[],[f50,f104])).

fof(f50,plain,(
    v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f33])).

fof(f102,plain,(
    spl13_3 ),
    inference(avatar_split_clause,[],[f51,f99])).

fof(f51,plain,(
    v1_funct_2(sK9,sK7,sK8) ),
    inference(cnf_transformation,[],[f33])).

fof(f97,plain,(
    spl13_2 ),
    inference(avatar_split_clause,[],[f52,f94])).

fof(f52,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) ),
    inference(cnf_transformation,[],[f33])).

fof(f92,plain,(
    ~ spl13_1 ),
    inference(avatar_split_clause,[],[f55,f89])).

fof(f55,plain,(
    sK8 != k2_relset_1(sK7,sK8,sK9) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:06:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (5018)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.49  % (5026)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.49  % (5022)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (5023)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.50  % (5022)Refutation not found, incomplete strategy% (5022)------------------------------
% 0.21/0.50  % (5022)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (5022)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (5022)Memory used [KB]: 6140
% 0.21/0.50  % (5022)Time elapsed: 0.060 s
% 0.21/0.50  % (5022)------------------------------
% 0.21/0.50  % (5022)------------------------------
% 0.21/0.50  % (5015)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (5030)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (5030)Refutation not found, incomplete strategy% (5030)------------------------------
% 0.21/0.50  % (5030)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (5030)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (5030)Memory used [KB]: 10618
% 0.21/0.50  % (5030)Time elapsed: 0.060 s
% 0.21/0.50  % (5030)------------------------------
% 0.21/0.50  % (5030)------------------------------
% 0.21/0.51  % (5026)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f762,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f92,f97,f102,f107,f118,f133,f149,f155,f165,f176,f191,f196,f431,f439,f512,f756])).
% 0.21/0.53  fof(f756,plain,(
% 0.21/0.53    ~spl13_4 | ~spl13_5 | spl13_10 | ~spl13_13 | ~spl13_14 | ~spl13_40),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f755])).
% 0.21/0.53  fof(f755,plain,(
% 0.21/0.53    $false | (~spl13_4 | ~spl13_5 | spl13_10 | ~spl13_13 | ~spl13_14 | ~spl13_40)),
% 0.21/0.53    inference(subsumption_resolution,[],[f754,f190])).
% 0.21/0.53  fof(f190,plain,(
% 0.21/0.53    r2_hidden(sK10(sK11(sK9,sK8)),sK7) | ~spl13_13),
% 0.21/0.53    inference(avatar_component_clause,[],[f188])).
% 0.21/0.53  fof(f188,plain,(
% 0.21/0.53    spl13_13 <=> r2_hidden(sK10(sK11(sK9,sK8)),sK7)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl13_13])])).
% 0.21/0.53  fof(f754,plain,(
% 0.21/0.53    ~r2_hidden(sK10(sK11(sK9,sK8)),sK7) | (~spl13_4 | ~spl13_5 | spl13_10 | ~spl13_14 | ~spl13_40)),
% 0.21/0.53    inference(forward_demodulation,[],[f753,f427])).
% 0.21/0.53  fof(f427,plain,(
% 0.21/0.53    sK7 = k1_relat_1(sK9) | ~spl13_40),
% 0.21/0.53    inference(avatar_component_clause,[],[f425])).
% 0.21/0.53  fof(f425,plain,(
% 0.21/0.53    spl13_40 <=> sK7 = k1_relat_1(sK9)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl13_40])])).
% 0.21/0.53  fof(f753,plain,(
% 0.21/0.53    ~r2_hidden(sK10(sK11(sK9,sK8)),k1_relat_1(sK9)) | (~spl13_4 | ~spl13_5 | spl13_10 | ~spl13_14)),
% 0.21/0.53    inference(subsumption_resolution,[],[f752,f119])).
% 0.21/0.53  fof(f119,plain,(
% 0.21/0.53    ( ! [X0,X1] : (sP0(sK9,X0,X1)) ) | (~spl13_4 | ~spl13_5)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f115,f106,f62])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (sP0(X0,X2,X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0] : (! [X1,X2] : (sP1(X2,X1,X0) & sP0(X0,X2,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(definition_folding,[],[f15,f22,f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0,X2,X1] : ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)) | ~sP0(X0,X2,X1))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X2,X1,X0] : ((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0)) | ~sP1(X2,X1,X0))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(flattening,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).
% 0.21/0.53  fof(f106,plain,(
% 0.21/0.53    v1_funct_1(sK9) | ~spl13_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f104])).
% 0.21/0.53  fof(f104,plain,(
% 0.21/0.53    spl13_4 <=> v1_funct_1(sK9)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).
% 0.21/0.53  fof(f115,plain,(
% 0.21/0.53    v1_relat_1(sK9) | ~spl13_5),
% 0.21/0.53    inference(avatar_component_clause,[],[f113])).
% 0.21/0.53  fof(f113,plain,(
% 0.21/0.53    spl13_5 <=> v1_relat_1(sK9)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl13_5])])).
% 0.21/0.53  fof(f752,plain,(
% 0.21/0.53    ~r2_hidden(sK10(sK11(sK9,sK8)),k1_relat_1(sK9)) | ~sP0(sK9,sK11(sK9,sK8),sK10(sK11(sK9,sK8))) | (spl13_10 | ~spl13_14)),
% 0.21/0.53    inference(subsumption_resolution,[],[f736,f169])).
% 0.21/0.53  fof(f169,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK11(sK9,sK8)),sK9)) ) | spl13_10),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f162,f79])).
% 0.21/0.53  fof(f79,plain,(
% 0.21/0.53    ( ! [X0,X3,X1] : (~r2_hidden(k4_tarski(X3,sK11(X0,X1)),X0) | sP5(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f49])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ! [X0,X1] : ((sP5(X0,X1) | (! [X3] : ~r2_hidden(k4_tarski(X3,sK11(X0,X1)),X0) & r2_hidden(sK11(X0,X1),X1))) & (! [X4] : (r2_hidden(k4_tarski(sK12(X0,X4),X4),X0) | ~r2_hidden(X4,X1)) | ~sP5(X0,X1)))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12])],[f46,f48,f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ! [X1,X0] : (? [X2] : (! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) & r2_hidden(X2,X1)) => (! [X3] : ~r2_hidden(k4_tarski(X3,sK11(X0,X1)),X0) & r2_hidden(sK11(X0,X1),X1)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ! [X4,X0] : (? [X5] : r2_hidden(k4_tarski(X5,X4),X0) => r2_hidden(k4_tarski(sK12(X0,X4),X4),X0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ! [X0,X1] : ((sP5(X0,X1) | ? [X2] : (! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) & r2_hidden(X2,X1))) & (! [X4] : (? [X5] : r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(X4,X1)) | ~sP5(X0,X1)))),
% 0.21/0.53    inference(rectify,[],[f45])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ! [X2,X1] : ((sP5(X2,X1) | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1))) & (! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1)) | ~sP5(X2,X1)))),
% 0.21/0.53    inference(nnf_transformation,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X2,X1] : (sP5(X2,X1) <=> ! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1)))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 0.21/0.53  fof(f162,plain,(
% 0.21/0.53    ~sP5(sK9,sK8) | spl13_10),
% 0.21/0.53    inference(avatar_component_clause,[],[f160])).
% 0.21/0.53  fof(f160,plain,(
% 0.21/0.53    spl13_10 <=> sP5(sK9,sK8)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl13_10])])).
% 0.21/0.53  fof(f736,plain,(
% 0.21/0.53    r2_hidden(k4_tarski(sK10(sK11(sK9,sK8)),sK11(sK9,sK8)),sK9) | ~r2_hidden(sK10(sK11(sK9,sK8)),k1_relat_1(sK9)) | ~sP0(sK9,sK11(sK9,sK8),sK10(sK11(sK9,sK8))) | ~spl13_14),
% 0.21/0.53    inference(superposition,[],[f83,f195])).
% 0.21/0.53  fof(f195,plain,(
% 0.21/0.53    sK11(sK9,sK8) = k1_funct_1(sK9,sK10(sK11(sK9,sK8))) | ~spl13_14),
% 0.21/0.53    inference(avatar_component_clause,[],[f193])).
% 0.21/0.53  fof(f193,plain,(
% 0.21/0.53    spl13_14 <=> sK11(sK9,sK8) = k1_funct_1(sK9,sK10(sK11(sK9,sK8)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl13_14])])).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    ( ! [X2,X0] : (r2_hidden(k4_tarski(X2,k1_funct_1(X0,X2)),X0) | ~r2_hidden(X2,k1_relat_1(X0)) | ~sP0(X0,k1_funct_1(X0,X2),X2)) )),
% 0.21/0.53    inference(equality_resolution,[],[f60])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X2,X1),X0) | k1_funct_1(X0,X2) != X1 | ~r2_hidden(X2,k1_relat_1(X0)) | ~sP0(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (((k1_funct_1(X0,X2) = X1 | ~r2_hidden(k4_tarski(X2,X1),X0)) & (r2_hidden(k4_tarski(X2,X1),X0) | k1_funct_1(X0,X2) != X1)) | ~r2_hidden(X2,k1_relat_1(X0)) | ~sP0(X0,X1,X2))),
% 0.21/0.53    inference(rectify,[],[f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ! [X0,X2,X1] : (((k1_funct_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(X1,X2),X0)) & (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2)) | ~r2_hidden(X1,k1_relat_1(X0)) | ~sP0(X0,X2,X1))),
% 0.21/0.53    inference(nnf_transformation,[],[f21])).
% 0.21/0.53  fof(f512,plain,(
% 0.21/0.53    spl13_10 | ~spl13_41),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f511])).
% 0.21/0.53  fof(f511,plain,(
% 0.21/0.53    $false | (spl13_10 | ~spl13_41)),
% 0.21/0.53    inference(subsumption_resolution,[],[f453,f121])).
% 0.21/0.53  fof(f121,plain,(
% 0.21/0.53    ( ! [X0] : (sP5(X0,k1_xboole_0)) )),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f108,f78])).
% 0.21/0.53  fof(f78,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(sK11(X0,X1),X1) | sP5(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f49])).
% 0.21/0.53  fof(f108,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f56,f65])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.53  fof(f453,plain,(
% 0.21/0.53    ~sP5(sK9,k1_xboole_0) | (spl13_10 | ~spl13_41)),
% 0.21/0.53    inference(backward_demodulation,[],[f162,f437])).
% 0.21/0.53  fof(f437,plain,(
% 0.21/0.53    k1_xboole_0 = sK8 | ~spl13_41),
% 0.21/0.53    inference(avatar_component_clause,[],[f435])).
% 0.21/0.53  fof(f435,plain,(
% 0.21/0.53    spl13_41 <=> k1_xboole_0 = sK8),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl13_41])])).
% 0.21/0.53  fof(f439,plain,(
% 0.21/0.53    spl13_41 | ~spl13_39),
% 0.21/0.53    inference(avatar_split_clause,[],[f433,f421,f435])).
% 0.21/0.53  fof(f421,plain,(
% 0.21/0.53    spl13_39 <=> sP2(sK7,sK8)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl13_39])])).
% 0.21/0.53  fof(f433,plain,(
% 0.21/0.53    k1_xboole_0 = sK8 | ~spl13_39),
% 0.21/0.53    inference(resolution,[],[f423,f71])).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~sP2(X0,X1) | k1_xboole_0 = X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP2(X0,X1))),
% 0.21/0.53    inference(nnf_transformation,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP2(X0,X1))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.53  fof(f423,plain,(
% 0.21/0.53    sP2(sK7,sK8) | ~spl13_39),
% 0.21/0.53    inference(avatar_component_clause,[],[f421])).
% 0.21/0.53  fof(f431,plain,(
% 0.21/0.53    spl13_39 | spl13_40 | ~spl13_3 | ~spl13_6 | ~spl13_9),
% 0.21/0.53    inference(avatar_split_clause,[],[f430,f152,f129,f99,f425,f421])).
% 0.21/0.53  fof(f99,plain,(
% 0.21/0.53    spl13_3 <=> v1_funct_2(sK9,sK7,sK8)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).
% 0.21/0.53  fof(f129,plain,(
% 0.21/0.53    spl13_6 <=> sP3(sK7,sK9,sK8)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl13_6])])).
% 0.21/0.53  fof(f152,plain,(
% 0.21/0.53    spl13_9 <=> k1_relset_1(sK7,sK8,sK9) = k1_relat_1(sK9)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl13_9])])).
% 0.21/0.53  fof(f430,plain,(
% 0.21/0.53    sK7 = k1_relat_1(sK9) | sP2(sK7,sK8) | (~spl13_3 | ~spl13_6 | ~spl13_9)),
% 0.21/0.53    inference(subsumption_resolution,[],[f429,f131])).
% 0.21/0.53  fof(f131,plain,(
% 0.21/0.53    sP3(sK7,sK9,sK8) | ~spl13_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f129])).
% 0.21/0.53  fof(f429,plain,(
% 0.21/0.53    sK7 = k1_relat_1(sK9) | sP2(sK7,sK8) | ~sP3(sK7,sK9,sK8) | (~spl13_3 | ~spl13_9)),
% 0.21/0.53    inference(subsumption_resolution,[],[f416,f101])).
% 0.21/0.53  fof(f101,plain,(
% 0.21/0.53    v1_funct_2(sK9,sK7,sK8) | ~spl13_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f99])).
% 0.21/0.53  fof(f416,plain,(
% 0.21/0.53    sK7 = k1_relat_1(sK9) | ~v1_funct_2(sK9,sK7,sK8) | sP2(sK7,sK8) | ~sP3(sK7,sK9,sK8) | ~spl13_9),
% 0.21/0.53    inference(superposition,[],[f154,f69])).
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | sP2(X0,X2) | ~sP3(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP2(X0,X2) | ~sP3(X0,X1,X2))),
% 0.21/0.53    inference(rectify,[],[f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP2(X0,X1) | ~sP3(X0,X2,X1))),
% 0.21/0.53    inference(nnf_transformation,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP2(X0,X1) | ~sP3(X0,X2,X1))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.21/0.53  fof(f154,plain,(
% 0.21/0.53    k1_relset_1(sK7,sK8,sK9) = k1_relat_1(sK9) | ~spl13_9),
% 0.21/0.53    inference(avatar_component_clause,[],[f152])).
% 0.21/0.53  fof(f196,plain,(
% 0.21/0.53    spl13_14 | ~spl13_11),
% 0.21/0.53    inference(avatar_split_clause,[],[f183,f173,f193])).
% 0.21/0.53  fof(f173,plain,(
% 0.21/0.53    spl13_11 <=> r2_hidden(sK11(sK9,sK8),sK8)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl13_11])])).
% 0.21/0.53  fof(f183,plain,(
% 0.21/0.53    sK11(sK9,sK8) = k1_funct_1(sK9,sK10(sK11(sK9,sK8))) | ~spl13_11),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f175,f54])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ( ! [X3] : (k1_funct_1(sK9,sK10(X3)) = X3 | ~r2_hidden(X3,sK8)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    sK8 != k2_relset_1(sK7,sK8,sK9) & ! [X3] : ((k1_funct_1(sK9,sK10(X3)) = X3 & r2_hidden(sK10(X3),sK7)) | ~r2_hidden(X3,sK8)) & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) & v1_funct_2(sK9,sK7,sK8) & v1_funct_1(sK9)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10])],[f12,f32,f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (sK8 != k2_relset_1(sK7,sK8,sK9) & ! [X3] : (? [X4] : (k1_funct_1(sK9,X4) = X3 & r2_hidden(X4,sK7)) | ~r2_hidden(X3,sK8)) & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) & v1_funct_2(sK9,sK7,sK8) & v1_funct_1(sK9))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ! [X3] : (? [X4] : (k1_funct_1(sK9,X4) = X3 & r2_hidden(X4,sK7)) => (k1_funct_1(sK9,sK10(X3)) = X3 & r2_hidden(sK10(X3),sK7)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.53    inference(flattening,[],[f11])).
% 0.21/0.53  fof(f11,plain,(
% 0.21/0.53    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 0.21/0.53    inference(negated_conjecture,[],[f9])).
% 0.21/0.53  fof(f9,conjecture,(
% 0.21/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).
% 0.21/0.53  fof(f175,plain,(
% 0.21/0.53    r2_hidden(sK11(sK9,sK8),sK8) | ~spl13_11),
% 0.21/0.53    inference(avatar_component_clause,[],[f173])).
% 0.21/0.53  fof(f191,plain,(
% 0.21/0.53    spl13_13 | ~spl13_11),
% 0.21/0.53    inference(avatar_split_clause,[],[f184,f173,f188])).
% 0.21/0.53  fof(f184,plain,(
% 0.21/0.53    r2_hidden(sK10(sK11(sK9,sK8)),sK7) | ~spl13_11),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f175,f53])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ( ! [X3] : (r2_hidden(sK10(X3),sK7) | ~r2_hidden(X3,sK8)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f33])).
% 0.21/0.53  fof(f176,plain,(
% 0.21/0.53    spl13_11 | spl13_10),
% 0.21/0.53    inference(avatar_split_clause,[],[f171,f160,f173])).
% 0.21/0.53  fof(f171,plain,(
% 0.21/0.53    r2_hidden(sK11(sK9,sK8),sK8) | spl13_10),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f162,f78])).
% 0.21/0.53  fof(f165,plain,(
% 0.21/0.53    ~spl13_10 | spl13_1 | ~spl13_8),
% 0.21/0.53    inference(avatar_split_clause,[],[f164,f145,f89,f160])).
% 0.21/0.53  fof(f89,plain,(
% 0.21/0.53    spl13_1 <=> sK8 = k2_relset_1(sK7,sK8,sK9)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).
% 0.21/0.53  fof(f145,plain,(
% 0.21/0.53    spl13_8 <=> sP6(sK8,sK9,sK7)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl13_8])])).
% 0.21/0.53  fof(f164,plain,(
% 0.21/0.53    ~sP5(sK9,sK8) | (spl13_1 | ~spl13_8)),
% 0.21/0.53    inference(subsumption_resolution,[],[f158,f147])).
% 0.21/0.53  fof(f147,plain,(
% 0.21/0.53    sP6(sK8,sK9,sK7) | ~spl13_8),
% 0.21/0.53    inference(avatar_component_clause,[],[f145])).
% 0.21/0.53  fof(f158,plain,(
% 0.21/0.53    ~sP5(sK9,sK8) | ~sP6(sK8,sK9,sK7) | spl13_1),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f157])).
% 0.21/0.53  fof(f157,plain,(
% 0.21/0.53    sK8 != sK8 | ~sP5(sK9,sK8) | ~sP6(sK8,sK9,sK7) | spl13_1),
% 0.21/0.53    inference(superposition,[],[f91,f75])).
% 0.21/0.53  fof(f75,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k2_relset_1(X2,X0,X1) = X0 | ~sP5(X1,X0) | ~sP6(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f44])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (((sP5(X1,X0) | k2_relset_1(X2,X0,X1) != X0) & (k2_relset_1(X2,X0,X1) = X0 | ~sP5(X1,X0))) | ~sP6(X0,X1,X2))),
% 0.21/0.53    inference(rectify,[],[f43])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ! [X1,X2,X0] : (((sP5(X2,X1) | k2_relset_1(X0,X1,X2) != X1) & (k2_relset_1(X0,X1,X2) = X1 | ~sP5(X2,X1))) | ~sP6(X1,X2,X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X1,X2,X0] : ((sP5(X2,X1) <=> k2_relset_1(X0,X1,X2) = X1) | ~sP6(X1,X2,X0))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).
% 0.21/0.53  fof(f91,plain,(
% 0.21/0.53    sK8 != k2_relset_1(sK7,sK8,sK9) | spl13_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f89])).
% 0.21/0.53  fof(f155,plain,(
% 0.21/0.53    spl13_9 | ~spl13_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f150,f94,f152])).
% 0.21/0.53  fof(f94,plain,(
% 0.21/0.53    spl13_2 <=> m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).
% 0.21/0.53  fof(f150,plain,(
% 0.21/0.53    k1_relset_1(sK7,sK8,sK9) = k1_relat_1(sK9) | ~spl13_2),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f96,f66])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.53  fof(f96,plain,(
% 0.21/0.53    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) | ~spl13_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f94])).
% 0.21/0.53  fof(f149,plain,(
% 0.21/0.53    spl13_8 | ~spl13_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f143,f94,f145])).
% 0.21/0.53  fof(f143,plain,(
% 0.21/0.53    sP6(sK8,sK9,sK7) | ~spl13_2),
% 0.21/0.53    inference(resolution,[],[f80,f96])).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP6(X1,X2,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (sP6(X1,X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(definition_folding,[],[f20,f29,f28])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relset_1)).
% 0.21/0.53  fof(f133,plain,(
% 0.21/0.53    spl13_6 | ~spl13_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f127,f94,f129])).
% 0.21/0.53  fof(f127,plain,(
% 0.21/0.53    sP3(sK7,sK9,sK8) | ~spl13_2),
% 0.21/0.53    inference(resolution,[],[f73,f96])).
% 0.21/0.53  fof(f73,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP3(X0,X2,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((sP4(X2,X1,X0) & sP3(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(definition_folding,[],[f19,f26,f25,f24])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP4(X2,X1,X0))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(flattening,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.53  fof(f118,plain,(
% 0.21/0.53    spl13_5 | ~spl13_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f117,f94,f113])).
% 0.21/0.53  fof(f117,plain,(
% 0.21/0.53    v1_relat_1(sK9) | ~spl13_2),
% 0.21/0.53    inference(subsumption_resolution,[],[f111,f64])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.53  fof(f111,plain,(
% 0.21/0.53    v1_relat_1(sK9) | ~v1_relat_1(k2_zfmisc_1(sK7,sK8)) | ~spl13_2),
% 0.21/0.53    inference(resolution,[],[f57,f96])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.53  fof(f107,plain,(
% 0.21/0.53    spl13_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f50,f104])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    v1_funct_1(sK9)),
% 0.21/0.53    inference(cnf_transformation,[],[f33])).
% 0.21/0.53  fof(f102,plain,(
% 0.21/0.53    spl13_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f51,f99])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    v1_funct_2(sK9,sK7,sK8)),
% 0.21/0.53    inference(cnf_transformation,[],[f33])).
% 0.21/0.53  fof(f97,plain,(
% 0.21/0.53    spl13_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f52,f94])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))),
% 0.21/0.53    inference(cnf_transformation,[],[f33])).
% 0.21/0.53  fof(f92,plain,(
% 0.21/0.53    ~spl13_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f55,f89])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    sK8 != k2_relset_1(sK7,sK8,sK9)),
% 0.21/0.53    inference(cnf_transformation,[],[f33])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (5026)------------------------------
% 0.21/0.53  % (5026)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (5026)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (5026)Memory used [KB]: 11001
% 0.21/0.53  % (5026)Time elapsed: 0.088 s
% 0.21/0.53  % (5026)------------------------------
% 0.21/0.53  % (5026)------------------------------
% 0.21/0.53  % (5009)Success in time 0.163 s
%------------------------------------------------------------------------------
