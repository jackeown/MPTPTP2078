%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  159 ( 291 expanded)
%              Number of leaves         :   35 (  98 expanded)
%              Depth                    :   13
%              Number of atoms          :  591 (1382 expanded)
%              Number of equality atoms :  106 ( 325 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f528,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f194,f329,f373,f433,f504,f513,f527])).

fof(f527,plain,
    ( spl19_1
    | ~ spl19_2 ),
    inference(avatar_contradiction_clause,[],[f526])).

fof(f526,plain,
    ( $false
    | spl19_1
    | ~ spl19_2 ),
    inference(subsumption_resolution,[],[f519,f189])).

fof(f189,plain,
    ( ~ v5_relat_1(sK12,k1_xboole_0)
    | spl19_1 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl19_1
  <=> v5_relat_1(sK12,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_1])])).

fof(f519,plain,
    ( v5_relat_1(sK12,k1_xboole_0)
    | ~ spl19_2 ),
    inference(backward_demodulation,[],[f142,f192])).

fof(f192,plain,
    ( k1_xboole_0 = sK11
    | ~ spl19_2 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl19_2
  <=> k1_xboole_0 = sK11 ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_2])])).

fof(f142,plain,(
    v5_relat_1(sK12,sK11) ),
    inference(resolution,[],[f108,f76])).

fof(f76,plain,(
    m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( sK11 != k2_relset_1(sK10,sK11,sK12)
    & ! [X3] :
        ( ( k1_funct_1(sK12,sK13(X3)) = X3
          & r2_hidden(sK13(X3),sK10) )
        | ~ r2_hidden(X3,sK11) )
    & m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)))
    & v1_funct_2(sK12,sK10,sK11)
    & v1_funct_1(sK12) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11,sK12,sK13])],[f15,f42,f41])).

fof(f41,plain,
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
   => ( sK11 != k2_relset_1(sK10,sK11,sK12)
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(sK12,X4) = X3
              & r2_hidden(X4,sK10) )
          | ~ r2_hidden(X3,sK11) )
      & m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)))
      & v1_funct_2(sK12,sK10,sK11)
      & v1_funct_1(sK12) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X3] :
      ( ? [X4] :
          ( k1_funct_1(sK12,X4) = X3
          & r2_hidden(X4,sK10) )
     => ( k1_funct_1(sK12,sK13(X3)) = X3
        & r2_hidden(sK13(X3),sK10) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f513,plain,
    ( spl19_2
    | ~ spl19_4 ),
    inference(avatar_split_clause,[],[f512,f326,f191])).

fof(f326,plain,
    ( spl19_4
  <=> sP5(sK10,sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_4])])).

fof(f512,plain,
    ( k1_xboole_0 = sK11
    | ~ spl19_4 ),
    inference(resolution,[],[f328,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ sP5(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP5(X0,X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP5(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f328,plain,
    ( sP5(sK10,sK11)
    | ~ spl19_4 ),
    inference(avatar_component_clause,[],[f326])).

fof(f504,plain,(
    ~ spl19_9 ),
    inference(avatar_contradiction_clause,[],[f503])).

fof(f503,plain,
    ( $false
    | ~ spl19_9 ),
    inference(subsumption_resolution,[],[f502,f201])).

fof(f201,plain,(
    ~ sP8(sK12,sK11) ),
    inference(subsumption_resolution,[],[f199,f152])).

fof(f152,plain,(
    sP9(sK11,sK12,sK10) ),
    inference(resolution,[],[f122,f76])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP9(X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( sP9(X1,X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f26,f39,f38])).

fof(f38,plain,(
    ! [X2,X1] :
      ( sP8(X2,X1)
    <=> ! [X3] :
          ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
          | ~ r2_hidden(X3,X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP8])])).

fof(f39,plain,(
    ! [X1,X2,X0] :
      ( ( sP8(X2,X1)
      <=> k2_relset_1(X0,X1,X2) = X1 )
      | ~ sP9(X1,X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP9])])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k2_relset_1(X0,X1,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
              & r2_hidden(X3,X1) )
      <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relset_1)).

fof(f199,plain,
    ( ~ sP8(sK12,sK11)
    | ~ sP9(sK11,sK12,sK10) ),
    inference(trivial_inequality_removal,[],[f197])).

fof(f197,plain,
    ( sK11 != sK11
    | ~ sP8(sK12,sK11)
    | ~ sP9(sK11,sK12,sK10) ),
    inference(superposition,[],[f79,f117])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X2,X0,X1) = X0
      | ~ sP8(X1,X0)
      | ~ sP9(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( ( ( sP8(X1,X0)
          | k2_relset_1(X2,X0,X1) != X0 )
        & ( k2_relset_1(X2,X0,X1) = X0
          | ~ sP8(X1,X0) ) )
      | ~ sP9(X0,X1,X2) ) ),
    inference(rectify,[],[f67])).

fof(f67,plain,(
    ! [X1,X2,X0] :
      ( ( ( sP8(X2,X1)
          | k2_relset_1(X0,X1,X2) != X1 )
        & ( k2_relset_1(X0,X1,X2) = X1
          | ~ sP8(X2,X1) ) )
      | ~ sP9(X1,X2,X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f79,plain,(
    sK11 != k2_relset_1(sK10,sK11,sK12) ),
    inference(cnf_transformation,[],[f43])).

fof(f502,plain,
    ( sP8(sK12,sK11)
    | ~ spl19_9 ),
    inference(duplicate_literal_removal,[],[f501])).

fof(f501,plain,
    ( sP8(sK12,sK11)
    | sP8(sK12,sK11)
    | ~ spl19_9 ),
    inference(resolution,[],[f500,f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK17(X0,X1),X1)
      | sP8(X0,X1) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ( sP8(X0,X1)
        | ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK17(X0,X1)),X0)
          & r2_hidden(sK17(X0,X1),X1) ) )
      & ( ! [X4] :
            ( r2_hidden(k4_tarski(sK18(X0,X4),X4),X0)
            | ~ r2_hidden(X4,X1) )
        | ~ sP8(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK17,sK18])],[f70,f72,f71])).

fof(f71,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
          & r2_hidden(X2,X1) )
     => ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK17(X0,X1)),X0)
        & r2_hidden(sK17(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,(
    ! [X4,X0] :
      ( ? [X5] : r2_hidden(k4_tarski(X5,X4),X0)
     => r2_hidden(k4_tarski(sK18(X0,X4),X4),X0) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ( sP8(X0,X1)
        | ? [X2] :
            ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            & r2_hidden(X2,X1) ) )
      & ( ! [X4] :
            ( ? [X5] : r2_hidden(k4_tarski(X5,X4),X0)
            | ~ r2_hidden(X4,X1) )
        | ~ sP8(X0,X1) ) ) ),
    inference(rectify,[],[f69])).

fof(f69,plain,(
    ! [X2,X1] :
      ( ( sP8(X2,X1)
        | ? [X3] :
            ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
            & r2_hidden(X3,X1) ) )
      & ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
            | ~ r2_hidden(X3,X1) )
        | ~ sP8(X2,X1) ) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f500,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK17(sK12,X0),sK11)
        | sP8(sK12,X0) )
    | ~ spl19_9 ),
    inference(duplicate_literal_removal,[],[f494])).

fof(f494,plain,
    ( ! [X0] :
        ( sP8(sK12,X0)
        | ~ r2_hidden(sK17(sK12,X0),sK11)
        | ~ r2_hidden(sK17(sK12,X0),sK11) )
    | ~ spl19_9 ),
    inference(resolution,[],[f364,f77])).

fof(f77,plain,(
    ! [X3] :
      ( r2_hidden(sK13(X3),sK10)
      | ~ r2_hidden(X3,sK11) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f364,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK13(sK17(sK12,X0)),X1)
        | sP8(sK12,X0)
        | ~ r2_hidden(sK17(sK12,X0),sK11) )
    | ~ spl19_9 ),
    inference(avatar_component_clause,[],[f363])).

fof(f363,plain,
    ( spl19_9
  <=> ! [X1,X0] :
        ( ~ r2_hidden(sK13(sK17(sK12,X0)),X1)
        | sP8(sK12,X0)
        | ~ r2_hidden(sK17(sK12,X0),sK11) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_9])])).

fof(f433,plain,
    ( spl19_9
    | ~ spl19_3
    | ~ spl19_5 ),
    inference(avatar_split_clause,[],[f432,f341,f322,f363])).

fof(f322,plain,
    ( spl19_3
  <=> sK10 = k1_relat_1(sK12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_3])])).

fof(f341,plain,
    ( spl19_5
  <=> sP2(sK12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_5])])).

fof(f432,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK13(sK17(sK12,X0)),X1)
        | ~ r2_hidden(sK17(sK12,X0),sK11)
        | sP8(sK12,X0) )
    | ~ spl19_3
    | ~ spl19_5 ),
    inference(subsumption_resolution,[],[f431,f131])).

fof(f131,plain,(
    v1_relat_1(sK12) ),
    inference(resolution,[],[f104,f76])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f431,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK13(sK17(sK12,X0)),X1)
        | ~ r2_hidden(sK17(sK12,X0),sK11)
        | ~ v1_relat_1(sK12)
        | sP8(sK12,X0) )
    | ~ spl19_3
    | ~ spl19_5 ),
    inference(subsumption_resolution,[],[f428,f342])).

fof(f342,plain,
    ( sP2(sK12)
    | ~ spl19_5 ),
    inference(avatar_component_clause,[],[f341])).

fof(f428,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK13(sK17(sK12,X0)),X1)
        | ~ r2_hidden(sK17(sK12,X0),sK11)
        | ~ sP2(sK12)
        | ~ v1_relat_1(sK12)
        | sP8(sK12,X0) )
    | ~ spl19_3 ),
    inference(resolution,[],[f397,f233])).

fof(f233,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(sK17(X0,X1),X0,X2)
      | ~ sP2(X0)
      | ~ v1_relat_1(X0)
      | sP8(X0,X1) ) ),
    inference(resolution,[],[f232,f169])).

fof(f169,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(X0,X1,sK17(X1,X2))
      | sP8(X1,X2) ) ),
    inference(resolution,[],[f100,f121])).

fof(f121,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,sK17(X0,X1)),X0)
      | sP8(X0,X1) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK16(X0,X1,X2),X2),X1)
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ! [X3] :
            ( ~ r2_hidden(X3,X0)
            | ~ r2_hidden(k4_tarski(X3,X2),X1)
            | ~ r2_hidden(X3,k1_relat_1(X1)) ) )
      & ( ( r2_hidden(sK16(X0,X1,X2),X0)
          & r2_hidden(k4_tarski(sK16(X0,X1,X2),X2),X1)
          & r2_hidden(sK16(X0,X1,X2),k1_relat_1(X1)) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16])],[f59,f60])).

fof(f60,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(k4_tarski(X4,X2),X1)
          & r2_hidden(X4,k1_relat_1(X1)) )
     => ( r2_hidden(sK16(X0,X1,X2),X0)
        & r2_hidden(k4_tarski(sK16(X0,X1,X2),X2),X1)
        & r2_hidden(sK16(X0,X1,X2),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ! [X3] :
            ( ~ r2_hidden(X3,X0)
            | ~ r2_hidden(k4_tarski(X3,X2),X1)
            | ~ r2_hidden(X3,k1_relat_1(X1)) ) )
      & ( ? [X4] :
            ( r2_hidden(X4,X0)
            & r2_hidden(k4_tarski(X4,X2),X1)
            & r2_hidden(X4,k1_relat_1(X1)) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(rectify,[],[f58])).

fof(f58,plain,(
    ! [X1,X2,X0] :
      ( ( sP3(X1,X2,X0)
        | ! [X3] :
            ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X0),X2)
            | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) )
        | ~ sP3(X1,X2,X0) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X1,X2,X0] :
      ( sP3(X1,X2,X0)
    <=> ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(k4_tarski(X3,X0),X2)
          & r2_hidden(X3,k1_relat_1(X2)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f232,plain,(
    ! [X2,X0,X1] :
      ( sP3(X0,X1,X2)
      | ~ sP0(X2,X1,X0)
      | ~ sP2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f171,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( sP4(X0,X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( sP4(X0,X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_folding,[],[f19,f32,f31])).

fof(f32,plain,(
    ! [X0,X2,X1] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> sP3(X1,X2,X0) )
      | ~ sP4(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(f171,plain,(
    ! [X2,X0,X1] :
      ( ~ sP4(X2,X1,X0)
      | sP3(X0,X1,X2)
      | ~ sP0(X2,X1,X0)
      | ~ sP2(X1) ) ),
    inference(resolution,[],[f97,f158])).

fof(f158,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k9_relat_1(X1,X2))
      | ~ sP0(X0,X1,X2)
      | ~ sP2(X1) ) ),
    inference(resolution,[],[f84,f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( sP1(X1,X0,k9_relat_1(X0,X1))
      | ~ sP2(X0) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X0,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ sP2(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ~ sP1(X1,X0,X2) )
          & ( sP1(X1,X0,X2)
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ sP2(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> sP1(X1,X0,X2) )
      | ~ sP2(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f84,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X4,X1,X0)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ~ sP0(sK14(X0,X1,X2),X1,X0)
            | ~ r2_hidden(sK14(X0,X1,X2),X2) )
          & ( sP0(sK14(X0,X1,X2),X1,X0)
            | r2_hidden(sK14(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X4,X1,X0) )
            & ( sP0(X4,X1,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f46,f47])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP0(X3,X1,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP0(X3,X1,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP0(sK14(X0,X1,X2),X1,X0)
          | ~ r2_hidden(sK14(X0,X1,X2),X2) )
        & ( sP0(sK14(X0,X1,X2),X1,X0)
          | r2_hidden(sK14(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X3,X1,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X3,X1,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X4,X1,X0) )
            & ( sP0(X4,X1,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X1,X0,X2] :
      ( ( sP1(X1,X0,X2)
        | ? [X3] :
            ( ( ~ sP0(X3,X0,X1)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X3,X0,X1)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP0(X3,X0,X1) )
            & ( sP0(X3,X0,X1)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X1,X0,X2] :
      ( sP1(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP0(X3,X0,X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
      | sP3(X2,X1,X0)
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X1,X2))
          | ~ sP3(X2,X1,X0) )
        & ( sP3(X2,X1,X0)
          | ~ r2_hidden(X0,k9_relat_1(X1,X2)) ) )
      | ~ sP4(X0,X1,X2) ) ),
    inference(rectify,[],[f56])).

fof(f56,plain,(
    ! [X0,X2,X1] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ~ sP3(X1,X2,X0) )
        & ( sP3(X1,X2,X0)
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ sP4(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f397,plain,
    ( ! [X0,X1] :
        ( sP0(X0,sK12,X1)
        | ~ r2_hidden(sK13(X0),X1)
        | ~ r2_hidden(X0,sK11) )
    | ~ spl19_3 ),
    inference(subsumption_resolution,[],[f396,f77])).

fof(f396,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK13(X0),sK10)
        | ~ r2_hidden(sK13(X0),X1)
        | sP0(X0,sK12,X1)
        | ~ r2_hidden(X0,sK11) )
    | ~ spl19_3 ),
    inference(forward_demodulation,[],[f214,f324])).

fof(f324,plain,
    ( sK10 = k1_relat_1(sK12)
    | ~ spl19_3 ),
    inference(avatar_component_clause,[],[f322])).

fof(f214,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK13(X0),k1_relat_1(sK12))
      | ~ r2_hidden(sK13(X0),X1)
      | sP0(X0,sK12,X1)
      | ~ r2_hidden(X0,sK11) ) ),
    inference(superposition,[],[f124,f78])).

fof(f78,plain,(
    ! [X3] :
      ( k1_funct_1(sK12,sK13(X3)) = X3
      | ~ r2_hidden(X3,sK11) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f124,plain,(
    ! [X2,X3,X1] :
      ( sP0(k1_funct_1(X1,X3),X1,X2)
      | ~ r2_hidden(X3,X2)
      | ~ r2_hidden(X3,k1_relat_1(X1)) ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2)
      | k1_funct_1(X1,X3) != X0
      | ~ r2_hidden(X3,X2)
      | ~ r2_hidden(X3,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( k1_funct_1(X1,X3) != X0
            | ~ r2_hidden(X3,X2)
            | ~ r2_hidden(X3,k1_relat_1(X1)) ) )
      & ( ( k1_funct_1(X1,sK15(X0,X1,X2)) = X0
          & r2_hidden(sK15(X0,X1,X2),X2)
          & r2_hidden(sK15(X0,X1,X2),k1_relat_1(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f50,f51])).

fof(f51,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X1,X4) = X0
          & r2_hidden(X4,X2)
          & r2_hidden(X4,k1_relat_1(X1)) )
     => ( k1_funct_1(X1,sK15(X0,X1,X2)) = X0
        & r2_hidden(sK15(X0,X1,X2),X2)
        & r2_hidden(sK15(X0,X1,X2),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( k1_funct_1(X1,X3) != X0
            | ~ r2_hidden(X3,X2)
            | ~ r2_hidden(X3,k1_relat_1(X1)) ) )
      & ( ? [X4] :
            ( k1_funct_1(X1,X4) = X0
            & r2_hidden(X4,X2)
            & r2_hidden(X4,k1_relat_1(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X3,X0,X1] :
      ( ( sP0(X3,X0,X1)
        | ! [X4] :
            ( k1_funct_1(X0,X4) != X3
            | ~ r2_hidden(X4,X1)
            | ~ r2_hidden(X4,k1_relat_1(X0)) ) )
      & ( ? [X4] :
            ( k1_funct_1(X0,X4) = X3
            & r2_hidden(X4,X1)
            & r2_hidden(X4,k1_relat_1(X0)) )
        | ~ sP0(X3,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X3,X0,X1] :
      ( sP0(X3,X0,X1)
    <=> ? [X4] :
          ( k1_funct_1(X0,X4) = X3
          & r2_hidden(X4,X1)
          & r2_hidden(X4,k1_relat_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f373,plain,(
    spl19_5 ),
    inference(avatar_contradiction_clause,[],[f372])).

fof(f372,plain,
    ( $false
    | spl19_5 ),
    inference(subsumption_resolution,[],[f371,f131])).

fof(f371,plain,
    ( ~ v1_relat_1(sK12)
    | spl19_5 ),
    inference(subsumption_resolution,[],[f370,f74])).

fof(f74,plain,(
    v1_funct_1(sK12) ),
    inference(cnf_transformation,[],[f43])).

fof(f370,plain,
    ( ~ v1_funct_1(sK12)
    | ~ v1_relat_1(sK12)
    | spl19_5 ),
    inference(resolution,[],[f343,f91])).

fof(f91,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f17,f29,f28,f27])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f343,plain,
    ( ~ sP2(sK12)
    | spl19_5 ),
    inference(avatar_component_clause,[],[f341])).

fof(f329,plain,
    ( spl19_3
    | spl19_4 ),
    inference(avatar_split_clause,[],[f320,f326,f322])).

fof(f320,plain,
    ( sP5(sK10,sK11)
    | sK10 = k1_relat_1(sK12) ),
    inference(subsumption_resolution,[],[f319,f75])).

fof(f75,plain,(
    v1_funct_2(sK12,sK10,sK11) ),
    inference(cnf_transformation,[],[f43])).

fof(f319,plain,
    ( ~ v1_funct_2(sK12,sK10,sK11)
    | sP5(sK10,sK11)
    | sK10 = k1_relat_1(sK12) ),
    inference(resolution,[],[f286,f76])).

fof(f286,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(X5,X3,X4)
      | sP5(X3,X4)
      | k1_relat_1(X5) = X3 ) ),
    inference(subsumption_resolution,[],[f284,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP6(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( sP7(X2,X1,X0)
        & sP6(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f25,f36,f35,f34])).

fof(f35,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP5(X0,X1)
      | ~ sP6(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP7(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP7])])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f284,plain,(
    ! [X4,X5,X3] :
      ( k1_relat_1(X5) = X3
      | ~ v1_funct_2(X5,X3,X4)
      | sP5(X3,X4)
      | ~ sP6(X3,X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(superposition,[],[f111,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | sP5(X0,X2)
      | ~ sP6(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP5(X0,X2)
      | ~ sP6(X0,X1,X2) ) ),
    inference(rectify,[],[f64])).

fof(f64,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP5(X0,X1)
      | ~ sP6(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f194,plain,
    ( ~ spl19_1
    | ~ spl19_2 ),
    inference(avatar_split_clause,[],[f185,f191,f187])).

fof(f185,plain,
    ( k1_xboole_0 != sK11
    | ~ v5_relat_1(sK12,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f184,f131])).

fof(f184,plain,
    ( k1_xboole_0 != sK11
    | ~ v5_relat_1(sK12,k1_xboole_0)
    | ~ v1_relat_1(sK12) ),
    inference(superposition,[],[f183,f140])).

fof(f140,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | ~ v5_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f135,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f135,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f96,f80])).

fof(f80,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
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

fof(f183,plain,(
    sK11 != k2_relat_1(sK12) ),
    inference(subsumption_resolution,[],[f182,f76])).

fof(f182,plain,
    ( sK11 != k2_relat_1(sK12)
    | ~ m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))) ),
    inference(superposition,[],[f79,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:57:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (25536)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.48  % (25544)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.49  % (25533)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.49  % (25534)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.49  % (25546)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (25535)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (25539)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.50  % (25541)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.50  % (25553)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.50  % (25538)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.50  % (25543)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.50  % (25536)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % (25550)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.50  % (25555)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.50  % (25540)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.50  % (25548)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.51  % (25549)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.51  % (25556)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.51  % (25547)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.51  % (25554)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  % (25537)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (25542)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.51  % (25539)Refutation not found, incomplete strategy% (25539)------------------------------
% 0.21/0.51  % (25539)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (25539)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (25539)Memory used [KB]: 1663
% 0.21/0.51  % (25539)Time elapsed: 0.104 s
% 0.21/0.51  % (25539)------------------------------
% 0.21/0.51  % (25539)------------------------------
% 0.21/0.51  % (25557)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f528,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f194,f329,f373,f433,f504,f513,f527])).
% 0.21/0.52  fof(f527,plain,(
% 0.21/0.52    spl19_1 | ~spl19_2),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f526])).
% 0.21/0.52  fof(f526,plain,(
% 0.21/0.52    $false | (spl19_1 | ~spl19_2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f519,f189])).
% 0.21/0.52  fof(f189,plain,(
% 0.21/0.52    ~v5_relat_1(sK12,k1_xboole_0) | spl19_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f187])).
% 0.21/0.52  fof(f187,plain,(
% 0.21/0.52    spl19_1 <=> v5_relat_1(sK12,k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl19_1])])).
% 0.21/0.52  fof(f519,plain,(
% 0.21/0.52    v5_relat_1(sK12,k1_xboole_0) | ~spl19_2),
% 0.21/0.52    inference(backward_demodulation,[],[f142,f192])).
% 0.21/0.52  fof(f192,plain,(
% 0.21/0.52    k1_xboole_0 = sK11 | ~spl19_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f191])).
% 0.21/0.52  fof(f191,plain,(
% 0.21/0.52    spl19_2 <=> k1_xboole_0 = sK11),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl19_2])])).
% 0.21/0.52  fof(f142,plain,(
% 0.21/0.52    v5_relat_1(sK12,sK11)),
% 0.21/0.52    inference(resolution,[],[f108,f76])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)))),
% 0.21/0.52    inference(cnf_transformation,[],[f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    sK11 != k2_relset_1(sK10,sK11,sK12) & ! [X3] : ((k1_funct_1(sK12,sK13(X3)) = X3 & r2_hidden(sK13(X3),sK10)) | ~r2_hidden(X3,sK11)) & m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))) & v1_funct_2(sK12,sK10,sK11) & v1_funct_1(sK12)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11,sK12,sK13])],[f15,f42,f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (sK11 != k2_relset_1(sK10,sK11,sK12) & ! [X3] : (? [X4] : (k1_funct_1(sK12,X4) = X3 & r2_hidden(X4,sK10)) | ~r2_hidden(X3,sK11)) & m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11))) & v1_funct_2(sK12,sK10,sK11) & v1_funct_1(sK12))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ! [X3] : (? [X4] : (k1_funct_1(sK12,X4) = X3 & r2_hidden(X4,sK10)) => (k1_funct_1(sK12,sK13(X3)) = X3 & r2_hidden(sK13(X3),sK10)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.52    inference(flattening,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.52    inference(ennf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 0.21/0.52    inference(negated_conjecture,[],[f12])).
% 0.21/0.52  fof(f12,conjecture,(
% 0.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).
% 0.21/0.52  fof(f108,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.52  fof(f513,plain,(
% 0.21/0.52    spl19_2 | ~spl19_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f512,f326,f191])).
% 0.21/0.52  fof(f326,plain,(
% 0.21/0.52    spl19_4 <=> sP5(sK10,sK11)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl19_4])])).
% 0.21/0.52  fof(f512,plain,(
% 0.21/0.52    k1_xboole_0 = sK11 | ~spl19_4),
% 0.21/0.52    inference(resolution,[],[f328,f113])).
% 0.21/0.52  fof(f113,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~sP5(X0,X1) | k1_xboole_0 = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f66])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP5(X0,X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP5(X0,X1))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 0.21/0.52  fof(f328,plain,(
% 0.21/0.52    sP5(sK10,sK11) | ~spl19_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f326])).
% 0.21/0.52  fof(f504,plain,(
% 0.21/0.52    ~spl19_9),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f503])).
% 0.21/0.52  fof(f503,plain,(
% 0.21/0.52    $false | ~spl19_9),
% 0.21/0.52    inference(subsumption_resolution,[],[f502,f201])).
% 0.21/0.52  fof(f201,plain,(
% 0.21/0.52    ~sP8(sK12,sK11)),
% 0.21/0.52    inference(subsumption_resolution,[],[f199,f152])).
% 0.21/0.52  fof(f152,plain,(
% 0.21/0.52    sP9(sK11,sK12,sK10)),
% 0.21/0.52    inference(resolution,[],[f122,f76])).
% 0.21/0.52  fof(f122,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP9(X1,X2,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (sP9(X1,X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(definition_folding,[],[f26,f39,f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ! [X2,X1] : (sP8(X2,X1) <=> ! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1)))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP8])])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ! [X1,X2,X0] : ((sP8(X2,X1) <=> k2_relset_1(X0,X1,X2) = X1) | ~sP9(X1,X2,X0))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP9])])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relset_1)).
% 0.21/0.52  fof(f199,plain,(
% 0.21/0.52    ~sP8(sK12,sK11) | ~sP9(sK11,sK12,sK10)),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f197])).
% 0.21/0.52  fof(f197,plain,(
% 0.21/0.52    sK11 != sK11 | ~sP8(sK12,sK11) | ~sP9(sK11,sK12,sK10)),
% 0.21/0.52    inference(superposition,[],[f79,f117])).
% 0.21/0.52  fof(f117,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k2_relset_1(X2,X0,X1) = X0 | ~sP8(X1,X0) | ~sP9(X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f68])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((sP8(X1,X0) | k2_relset_1(X2,X0,X1) != X0) & (k2_relset_1(X2,X0,X1) = X0 | ~sP8(X1,X0))) | ~sP9(X0,X1,X2))),
% 0.21/0.52    inference(rectify,[],[f67])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    ! [X1,X2,X0] : (((sP8(X2,X1) | k2_relset_1(X0,X1,X2) != X1) & (k2_relset_1(X0,X1,X2) = X1 | ~sP8(X2,X1))) | ~sP9(X1,X2,X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f39])).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    sK11 != k2_relset_1(sK10,sK11,sK12)),
% 0.21/0.52    inference(cnf_transformation,[],[f43])).
% 0.21/0.52  fof(f502,plain,(
% 0.21/0.52    sP8(sK12,sK11) | ~spl19_9),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f501])).
% 0.21/0.52  fof(f501,plain,(
% 0.21/0.52    sP8(sK12,sK11) | sP8(sK12,sK11) | ~spl19_9),
% 0.21/0.52    inference(resolution,[],[f500,f120])).
% 0.21/0.52  fof(f120,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(sK17(X0,X1),X1) | sP8(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f73])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    ! [X0,X1] : ((sP8(X0,X1) | (! [X3] : ~r2_hidden(k4_tarski(X3,sK17(X0,X1)),X0) & r2_hidden(sK17(X0,X1),X1))) & (! [X4] : (r2_hidden(k4_tarski(sK18(X0,X4),X4),X0) | ~r2_hidden(X4,X1)) | ~sP8(X0,X1)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK17,sK18])],[f70,f72,f71])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X2] : (! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) & r2_hidden(X2,X1)) => (! [X3] : ~r2_hidden(k4_tarski(X3,sK17(X0,X1)),X0) & r2_hidden(sK17(X0,X1),X1)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    ! [X4,X0] : (? [X5] : r2_hidden(k4_tarski(X5,X4),X0) => r2_hidden(k4_tarski(sK18(X0,X4),X4),X0))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    ! [X0,X1] : ((sP8(X0,X1) | ? [X2] : (! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) & r2_hidden(X2,X1))) & (! [X4] : (? [X5] : r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(X4,X1)) | ~sP8(X0,X1)))),
% 0.21/0.52    inference(rectify,[],[f69])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    ! [X2,X1] : ((sP8(X2,X1) | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1))) & (! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1)) | ~sP8(X2,X1)))),
% 0.21/0.52    inference(nnf_transformation,[],[f38])).
% 0.21/0.52  fof(f500,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(sK17(sK12,X0),sK11) | sP8(sK12,X0)) ) | ~spl19_9),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f494])).
% 0.21/0.52  fof(f494,plain,(
% 0.21/0.52    ( ! [X0] : (sP8(sK12,X0) | ~r2_hidden(sK17(sK12,X0),sK11) | ~r2_hidden(sK17(sK12,X0),sK11)) ) | ~spl19_9),
% 0.21/0.52    inference(resolution,[],[f364,f77])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    ( ! [X3] : (r2_hidden(sK13(X3),sK10) | ~r2_hidden(X3,sK11)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f43])).
% 0.21/0.52  fof(f364,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(sK13(sK17(sK12,X0)),X1) | sP8(sK12,X0) | ~r2_hidden(sK17(sK12,X0),sK11)) ) | ~spl19_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f363])).
% 0.21/0.52  fof(f363,plain,(
% 0.21/0.52    spl19_9 <=> ! [X1,X0] : (~r2_hidden(sK13(sK17(sK12,X0)),X1) | sP8(sK12,X0) | ~r2_hidden(sK17(sK12,X0),sK11))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl19_9])])).
% 0.21/0.52  fof(f433,plain,(
% 0.21/0.52    spl19_9 | ~spl19_3 | ~spl19_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f432,f341,f322,f363])).
% 0.21/0.52  fof(f322,plain,(
% 0.21/0.52    spl19_3 <=> sK10 = k1_relat_1(sK12)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl19_3])])).
% 0.21/0.52  fof(f341,plain,(
% 0.21/0.52    spl19_5 <=> sP2(sK12)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl19_5])])).
% 0.21/0.52  fof(f432,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(sK13(sK17(sK12,X0)),X1) | ~r2_hidden(sK17(sK12,X0),sK11) | sP8(sK12,X0)) ) | (~spl19_3 | ~spl19_5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f431,f131])).
% 0.21/0.52  fof(f131,plain,(
% 0.21/0.52    v1_relat_1(sK12)),
% 0.21/0.52    inference(resolution,[],[f104,f76])).
% 0.21/0.52  fof(f104,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.52  fof(f431,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(sK13(sK17(sK12,X0)),X1) | ~r2_hidden(sK17(sK12,X0),sK11) | ~v1_relat_1(sK12) | sP8(sK12,X0)) ) | (~spl19_3 | ~spl19_5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f428,f342])).
% 0.21/0.52  fof(f342,plain,(
% 0.21/0.52    sP2(sK12) | ~spl19_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f341])).
% 0.21/0.52  fof(f428,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(sK13(sK17(sK12,X0)),X1) | ~r2_hidden(sK17(sK12,X0),sK11) | ~sP2(sK12) | ~v1_relat_1(sK12) | sP8(sK12,X0)) ) | ~spl19_3),
% 0.21/0.52    inference(resolution,[],[f397,f233])).
% 0.21/0.52  fof(f233,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~sP0(sK17(X0,X1),X0,X2) | ~sP2(X0) | ~v1_relat_1(X0) | sP8(X0,X1)) )),
% 0.21/0.52    inference(resolution,[],[f232,f169])).
% 0.21/0.52  fof(f169,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~sP3(X0,X1,sK17(X1,X2)) | sP8(X1,X2)) )),
% 0.21/0.52    inference(resolution,[],[f100,f121])).
% 0.21/0.52  fof(f121,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (~r2_hidden(k4_tarski(X3,sK17(X0,X1)),X0) | sP8(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f73])).
% 0.21/0.52  fof(f100,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK16(X0,X1,X2),X2),X1) | ~sP3(X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f61])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(k4_tarski(X3,X2),X1) | ~r2_hidden(X3,k1_relat_1(X1)))) & ((r2_hidden(sK16(X0,X1,X2),X0) & r2_hidden(k4_tarski(sK16(X0,X1,X2),X2),X1) & r2_hidden(sK16(X0,X1,X2),k1_relat_1(X1))) | ~sP3(X0,X1,X2)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16])],[f59,f60])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(k4_tarski(X4,X2),X1) & r2_hidden(X4,k1_relat_1(X1))) => (r2_hidden(sK16(X0,X1,X2),X0) & r2_hidden(k4_tarski(sK16(X0,X1,X2),X2),X1) & r2_hidden(sK16(X0,X1,X2),k1_relat_1(X1))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(k4_tarski(X3,X2),X1) | ~r2_hidden(X3,k1_relat_1(X1)))) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(k4_tarski(X4,X2),X1) & r2_hidden(X4,k1_relat_1(X1))) | ~sP3(X0,X1,X2)))),
% 0.21/0.52    inference(rectify,[],[f58])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ! [X1,X2,X0] : ((sP3(X1,X2,X0) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~sP3(X1,X2,X0)))),
% 0.21/0.52    inference(nnf_transformation,[],[f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ! [X1,X2,X0] : (sP3(X1,X2,X0) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.21/0.52  fof(f232,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (sP3(X0,X1,X2) | ~sP0(X2,X1,X0) | ~sP2(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(resolution,[],[f171,f103])).
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (sP4(X0,X2,X1) | ~v1_relat_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (sP4(X0,X2,X1) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(definition_folding,[],[f19,f32,f31])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ! [X0,X2,X1] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> sP3(X1,X2,X0)) | ~sP4(X0,X2,X1))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 0.21/0.52  fof(f171,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~sP4(X2,X1,X0) | sP3(X0,X1,X2) | ~sP0(X2,X1,X0) | ~sP2(X1)) )),
% 0.21/0.52    inference(resolution,[],[f97,f158])).
% 0.21/0.52  fof(f158,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r2_hidden(X0,k9_relat_1(X1,X2)) | ~sP0(X0,X1,X2) | ~sP2(X1)) )),
% 0.21/0.52    inference(resolution,[],[f84,f123])).
% 0.21/0.52  fof(f123,plain,(
% 0.21/0.52    ( ! [X0,X1] : (sP1(X1,X0,k9_relat_1(X0,X1)) | ~sP2(X0)) )),
% 0.21/0.52    inference(equality_resolution,[],[f81])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (sP1(X1,X0,X2) | k9_relat_1(X0,X1) != X2 | ~sP2(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ~sP1(X1,X0,X2)) & (sP1(X1,X0,X2) | k9_relat_1(X0,X1) != X2)) | ~sP2(X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> sP1(X1,X0,X2)) | ~sP2(X0))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~sP0(X4,X1,X0) | r2_hidden(X4,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ((~sP0(sK14(X0,X1,X2),X1,X0) | ~r2_hidden(sK14(X0,X1,X2),X2)) & (sP0(sK14(X0,X1,X2),X1,X0) | r2_hidden(sK14(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X4,X1,X0)) & (sP0(X4,X1,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f46,f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ! [X2,X1,X0] : (? [X3] : ((~sP0(X3,X1,X0) | ~r2_hidden(X3,X2)) & (sP0(X3,X1,X0) | r2_hidden(X3,X2))) => ((~sP0(sK14(X0,X1,X2),X1,X0) | ~r2_hidden(sK14(X0,X1,X2),X2)) & (sP0(sK14(X0,X1,X2),X1,X0) | r2_hidden(sK14(X0,X1,X2),X2))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X3,X1,X0) | ~r2_hidden(X3,X2)) & (sP0(X3,X1,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X4,X1,X0)) & (sP0(X4,X1,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 0.21/0.52    inference(rectify,[],[f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ! [X1,X0,X2] : ((sP1(X1,X0,X2) | ? [X3] : ((~sP0(X3,X0,X1) | ~r2_hidden(X3,X2)) & (sP0(X3,X0,X1) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP0(X3,X0,X1)) & (sP0(X3,X0,X1) | ~r2_hidden(X3,X2))) | ~sP1(X1,X0,X2)))),
% 0.21/0.52    inference(nnf_transformation,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X1,X0,X2] : (sP1(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP0(X3,X0,X1)))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.52  fof(f97,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X1,X2)) | sP3(X2,X1,X0) | ~sP4(X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f57])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X1,X2)) | ~sP3(X2,X1,X0)) & (sP3(X2,X1,X0) | ~r2_hidden(X0,k9_relat_1(X1,X2)))) | ~sP4(X0,X1,X2))),
% 0.21/0.52    inference(rectify,[],[f56])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ! [X0,X2,X1] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ~sP3(X1,X2,X0)) & (sP3(X1,X2,X0) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~sP4(X0,X2,X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f32])).
% 0.21/0.52  fof(f397,plain,(
% 0.21/0.52    ( ! [X0,X1] : (sP0(X0,sK12,X1) | ~r2_hidden(sK13(X0),X1) | ~r2_hidden(X0,sK11)) ) | ~spl19_3),
% 0.21/0.52    inference(subsumption_resolution,[],[f396,f77])).
% 0.21/0.52  fof(f396,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(sK13(X0),sK10) | ~r2_hidden(sK13(X0),X1) | sP0(X0,sK12,X1) | ~r2_hidden(X0,sK11)) ) | ~spl19_3),
% 0.21/0.52    inference(forward_demodulation,[],[f214,f324])).
% 0.21/0.52  fof(f324,plain,(
% 0.21/0.52    sK10 = k1_relat_1(sK12) | ~spl19_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f322])).
% 0.21/0.52  fof(f214,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(sK13(X0),k1_relat_1(sK12)) | ~r2_hidden(sK13(X0),X1) | sP0(X0,sK12,X1) | ~r2_hidden(X0,sK11)) )),
% 0.21/0.52    inference(superposition,[],[f124,f78])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    ( ! [X3] : (k1_funct_1(sK12,sK13(X3)) = X3 | ~r2_hidden(X3,sK11)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f43])).
% 0.21/0.52  fof(f124,plain,(
% 0.21/0.52    ( ! [X2,X3,X1] : (sP0(k1_funct_1(X1,X3),X1,X2) | ~r2_hidden(X3,X2) | ~r2_hidden(X3,k1_relat_1(X1))) )),
% 0.21/0.52    inference(equality_resolution,[],[f90])).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2) | k1_funct_1(X1,X3) != X0 | ~r2_hidden(X3,X2) | ~r2_hidden(X3,k1_relat_1(X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f52])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (k1_funct_1(X1,X3) != X0 | ~r2_hidden(X3,X2) | ~r2_hidden(X3,k1_relat_1(X1)))) & ((k1_funct_1(X1,sK15(X0,X1,X2)) = X0 & r2_hidden(sK15(X0,X1,X2),X2) & r2_hidden(sK15(X0,X1,X2),k1_relat_1(X1))) | ~sP0(X0,X1,X2)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f50,f51])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ! [X2,X1,X0] : (? [X4] : (k1_funct_1(X1,X4) = X0 & r2_hidden(X4,X2) & r2_hidden(X4,k1_relat_1(X1))) => (k1_funct_1(X1,sK15(X0,X1,X2)) = X0 & r2_hidden(sK15(X0,X1,X2),X2) & r2_hidden(sK15(X0,X1,X2),k1_relat_1(X1))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (k1_funct_1(X1,X3) != X0 | ~r2_hidden(X3,X2) | ~r2_hidden(X3,k1_relat_1(X1)))) & (? [X4] : (k1_funct_1(X1,X4) = X0 & r2_hidden(X4,X2) & r2_hidden(X4,k1_relat_1(X1))) | ~sP0(X0,X1,X2)))),
% 0.21/0.52    inference(rectify,[],[f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ! [X3,X0,X1] : ((sP0(X3,X0,X1) | ! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0)))) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | ~sP0(X3,X0,X1)))),
% 0.21/0.52    inference(nnf_transformation,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X3,X0,X1] : (sP0(X3,X0,X1) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.52  fof(f373,plain,(
% 0.21/0.52    spl19_5),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f372])).
% 0.21/0.52  fof(f372,plain,(
% 0.21/0.52    $false | spl19_5),
% 0.21/0.52    inference(subsumption_resolution,[],[f371,f131])).
% 0.21/0.52  fof(f371,plain,(
% 0.21/0.52    ~v1_relat_1(sK12) | spl19_5),
% 0.21/0.52    inference(subsumption_resolution,[],[f370,f74])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    v1_funct_1(sK12)),
% 0.21/0.52    inference(cnf_transformation,[],[f43])).
% 0.21/0.52  fof(f370,plain,(
% 0.21/0.52    ~v1_funct_1(sK12) | ~v1_relat_1(sK12) | spl19_5),
% 0.21/0.52    inference(resolution,[],[f343,f91])).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    ( ! [X0] : (sP2(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ! [X0] : (sP2(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(definition_folding,[],[f17,f29,f28,f27])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(flattening,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).
% 0.21/0.52  fof(f343,plain,(
% 0.21/0.52    ~sP2(sK12) | spl19_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f341])).
% 0.21/0.52  fof(f329,plain,(
% 0.21/0.52    spl19_3 | spl19_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f320,f326,f322])).
% 0.21/0.52  fof(f320,plain,(
% 0.21/0.52    sP5(sK10,sK11) | sK10 = k1_relat_1(sK12)),
% 0.21/0.52    inference(subsumption_resolution,[],[f319,f75])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    v1_funct_2(sK12,sK10,sK11)),
% 0.21/0.52    inference(cnf_transformation,[],[f43])).
% 0.21/0.52  fof(f319,plain,(
% 0.21/0.52    ~v1_funct_2(sK12,sK10,sK11) | sP5(sK10,sK11) | sK10 = k1_relat_1(sK12)),
% 0.21/0.52    inference(resolution,[],[f286,f76])).
% 0.21/0.52  fof(f286,plain,(
% 0.21/0.52    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(X5,X3,X4) | sP5(X3,X4) | k1_relat_1(X5) = X3) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f284,f115])).
% 0.21/0.52  fof(f115,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP6(X0,X2,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((sP7(X2,X1,X0) & sP6(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(definition_folding,[],[f25,f36,f35,f34])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP5(X0,X1) | ~sP6(X0,X2,X1))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP7(X2,X1,X0))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP7])])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(flattening,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.52  fof(f284,plain,(
% 0.21/0.52    ( ! [X4,X5,X3] : (k1_relat_1(X5) = X3 | ~v1_funct_2(X5,X3,X4) | sP5(X3,X4) | ~sP6(X3,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 0.21/0.52    inference(superposition,[],[f111,f105])).
% 0.21/0.52  fof(f105,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.52  fof(f111,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | sP5(X0,X2) | ~sP6(X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f65])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP5(X0,X2) | ~sP6(X0,X1,X2))),
% 0.21/0.52    inference(rectify,[],[f64])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP5(X0,X1) | ~sP6(X0,X2,X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f35])).
% 0.21/0.52  fof(f194,plain,(
% 0.21/0.52    ~spl19_1 | ~spl19_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f185,f191,f187])).
% 0.21/0.52  fof(f185,plain,(
% 0.21/0.52    k1_xboole_0 != sK11 | ~v5_relat_1(sK12,k1_xboole_0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f184,f131])).
% 0.21/0.52  fof(f184,plain,(
% 0.21/0.52    k1_xboole_0 != sK11 | ~v5_relat_1(sK12,k1_xboole_0) | ~v1_relat_1(sK12)),
% 0.21/0.52    inference(superposition,[],[f183,f140])).
% 0.21/0.52  fof(f140,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | ~v5_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(resolution,[],[f135,f92])).
% 0.21/0.52  fof(f92,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f53])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.52  fof(f135,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(resolution,[],[f96,f80])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f55])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(flattening,[],[f54])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.52  fof(f183,plain,(
% 0.21/0.52    sK11 != k2_relat_1(sK12)),
% 0.21/0.52    inference(subsumption_resolution,[],[f182,f76])).
% 0.21/0.52  fof(f182,plain,(
% 0.21/0.52    sK11 != k2_relat_1(sK12) | ~m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK10,sK11)))),
% 0.21/0.52    inference(superposition,[],[f79,f106])).
% 0.21/0.52  fof(f106,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (25536)------------------------------
% 0.21/0.52  % (25536)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (25536)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (25536)Memory used [KB]: 6396
% 0.21/0.52  % (25536)Time elapsed: 0.097 s
% 0.21/0.52  % (25536)------------------------------
% 0.21/0.52  % (25536)------------------------------
% 0.21/0.52  % (25531)Success in time 0.164 s
%------------------------------------------------------------------------------
