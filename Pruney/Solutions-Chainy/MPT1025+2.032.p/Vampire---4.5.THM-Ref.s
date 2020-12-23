%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:26 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  210 ( 366 expanded)
%              Number of leaves         :   51 ( 154 expanded)
%              Depth                    :   12
%              Number of atoms          :  648 (1257 expanded)
%              Number of equality atoms :  100 ( 183 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2513,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f116,f121,f126,f131,f200,f201,f234,f246,f266,f351,f853,f901,f917,f928,f939,f1104,f1278,f1299,f1319,f1352,f1399,f1517,f1535,f1539,f2434,f2511])).

fof(f2511,plain,
    ( ~ spl17_59
    | ~ spl17_82
    | ~ spl17_184 ),
    inference(avatar_contradiction_clause,[],[f2510])).

fof(f2510,plain,
    ( $false
    | ~ spl17_59
    | ~ spl17_82
    | ~ spl17_184 ),
    inference(subsumption_resolution,[],[f2509,f1103])).

fof(f1103,plain,
    ( m1_subset_1(sK14(sK11,sK12,sK13),sK9)
    | ~ spl17_82 ),
    inference(avatar_component_clause,[],[f1101])).

fof(f1101,plain,
    ( spl17_82
  <=> m1_subset_1(sK14(sK11,sK12,sK13),sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_82])])).

fof(f2509,plain,
    ( ~ m1_subset_1(sK14(sK11,sK12,sK13),sK9)
    | ~ spl17_59
    | ~ spl17_184 ),
    inference(subsumption_resolution,[],[f2503,f916])).

fof(f916,plain,
    ( r2_hidden(sK14(sK11,sK12,sK13),sK11)
    | ~ spl17_59 ),
    inference(avatar_component_clause,[],[f914])).

fof(f914,plain,
    ( spl17_59
  <=> r2_hidden(sK14(sK11,sK12,sK13),sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_59])])).

fof(f2503,plain,
    ( ~ r2_hidden(sK14(sK11,sK12,sK13),sK11)
    | ~ m1_subset_1(sK14(sK11,sK12,sK13),sK9)
    | ~ spl17_184 ),
    inference(trivial_inequality_removal,[],[f2500])).

fof(f2500,plain,
    ( ~ r2_hidden(sK14(sK11,sK12,sK13),sK11)
    | ~ m1_subset_1(sK14(sK11,sK12,sK13),sK9)
    | sK13 != sK13
    | ~ spl17_184 ),
    inference(resolution,[],[f2429,f214])).

fof(f214,plain,(
    ! [X0,X1] :
      ( ~ sP7(X1,X0,sK12)
      | ~ r2_hidden(X0,sK11)
      | ~ m1_subset_1(X0,sK9)
      | sK13 != X1 ) ),
    inference(superposition,[],[f71,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X1) = X0
      | ~ sP7(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( ( sP7(X0,X1,X2)
        | k1_funct_1(X2,X1) != X0
        | ~ r2_hidden(X1,k1_relat_1(X2)) )
      & ( ( k1_funct_1(X2,X1) = X0
          & r2_hidden(X1,k1_relat_1(X2)) )
        | ~ sP7(X0,X1,X2) ) ) ),
    inference(rectify,[],[f65])).

fof(f65,plain,(
    ! [X1,X0,X2] :
      ( ( sP7(X1,X0,X2)
        | k1_funct_1(X2,X0) != X1
        | ~ r2_hidden(X0,k1_relat_1(X2)) )
      & ( ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) )
        | ~ sP7(X1,X0,X2) ) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X1,X0,X2] :
      ( ( sP7(X1,X0,X2)
        | k1_funct_1(X2,X0) != X1
        | ~ r2_hidden(X0,k1_relat_1(X2)) )
      & ( ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) )
        | ~ sP7(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X1,X0,X2] :
      ( sP7(X1,X0,X2)
    <=> ( k1_funct_1(X2,X0) = X1
        & r2_hidden(X0,k1_relat_1(X2)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP7])])).

fof(f71,plain,(
    ! [X5] :
      ( k1_funct_1(sK12,X5) != sK13
      | ~ r2_hidden(X5,sK11)
      | ~ m1_subset_1(X5,sK9) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ! [X5] :
        ( k1_funct_1(sK12,X5) != sK13
        | ~ r2_hidden(X5,sK11)
        | ~ m1_subset_1(X5,sK9) )
    & r2_hidden(sK13,k7_relset_1(sK9,sK10,sK12,sK11))
    & m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10)))
    & v1_funct_2(sK12,sK9,sK10)
    & v1_funct_1(sK12) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11,sK12,sK13])],[f15,f41,f40])).

fof(f40,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ! [X5] :
                ( k1_funct_1(X3,X5) != X4
                | ~ r2_hidden(X5,X2)
                | ~ m1_subset_1(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(sK12,X5) != X4
              | ~ r2_hidden(X5,sK11)
              | ~ m1_subset_1(X5,sK9) )
          & r2_hidden(X4,k7_relset_1(sK9,sK10,sK12,sK11)) )
      & m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10)))
      & v1_funct_2(sK12,sK9,sK10)
      & v1_funct_1(sK12) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X4] :
        ( ! [X5] :
            ( k1_funct_1(sK12,X5) != X4
            | ~ r2_hidden(X5,sK11)
            | ~ m1_subset_1(X5,sK9) )
        & r2_hidden(X4,k7_relset_1(sK9,sK10,sK12,sK11)) )
   => ( ! [X5] :
          ( k1_funct_1(sK12,X5) != sK13
          | ~ r2_hidden(X5,sK11)
          | ~ m1_subset_1(X5,sK9) )
      & r2_hidden(sK13,k7_relset_1(sK9,sK10,sK12,sK11)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ( m1_subset_1(X5,X0)
                 => ~ ( k1_funct_1(X3,X5) = X4
                      & r2_hidden(X5,X2) ) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ( m1_subset_1(X5,X0)
               => ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2) ) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).

fof(f2429,plain,
    ( sP7(sK13,sK14(sK11,sK12,sK13),sK12)
    | ~ spl17_184 ),
    inference(avatar_component_clause,[],[f2427])).

fof(f2427,plain,
    ( spl17_184
  <=> sP7(sK13,sK14(sK11,sK12,sK13),sK12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_184])])).

fof(f2434,plain,
    ( spl17_184
    | ~ spl17_4
    | ~ spl17_12
    | ~ spl17_63 ),
    inference(avatar_split_clause,[],[f2433,f936,f196,f128,f2427])).

fof(f128,plain,
    ( spl17_4
  <=> v1_funct_1(sK12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_4])])).

fof(f196,plain,
    ( spl17_12
  <=> v1_relat_1(sK12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_12])])).

fof(f936,plain,
    ( spl17_63
  <=> r2_hidden(k4_tarski(sK14(sK11,sK12,sK13),sK13),sK12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_63])])).

fof(f2433,plain,
    ( sP7(sK13,sK14(sK11,sK12,sK13),sK12)
    | ~ spl17_4
    | ~ spl17_12
    | ~ spl17_63 ),
    inference(subsumption_resolution,[],[f2413,f212])).

fof(f212,plain,
    ( ! [X0,X1] : sP8(sK12,X0,X1)
    | ~ spl17_4
    | ~ spl17_12 ),
    inference(unit_resulting_resolution,[],[f198,f130,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( sP8(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( sP8(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_folding,[],[f25,f38,f37])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> sP7(X1,X0,X2) )
      | ~ sP8(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP8])])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f130,plain,
    ( v1_funct_1(sK12)
    | ~ spl17_4 ),
    inference(avatar_component_clause,[],[f128])).

fof(f198,plain,
    ( v1_relat_1(sK12)
    | ~ spl17_12 ),
    inference(avatar_component_clause,[],[f196])).

fof(f2413,plain,
    ( sP7(sK13,sK14(sK11,sK12,sK13),sK12)
    | ~ sP8(sK12,sK14(sK11,sK12,sK13),sK13)
    | ~ spl17_63 ),
    inference(resolution,[],[f938,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),X0)
      | sP7(X2,X1,X0)
      | ~ sP8(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X1,X2),X0)
          | ~ sP7(X2,X1,X0) )
        & ( sP7(X2,X1,X0)
          | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ sP8(X0,X1,X2) ) ),
    inference(rectify,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ sP7(X1,X0,X2) )
        & ( sP7(X1,X0,X2)
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ sP8(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f938,plain,
    ( r2_hidden(k4_tarski(sK14(sK11,sK12,sK13),sK13),sK12)
    | ~ spl17_63 ),
    inference(avatar_component_clause,[],[f936])).

fof(f1539,plain,
    ( ~ spl17_13
    | spl17_88
    | ~ spl17_3
    | spl17_23
    | ~ spl17_16 ),
    inference(avatar_split_clause,[],[f1265,f348,f411,f123,f1155,f230])).

fof(f230,plain,
    ( spl17_13
  <=> sP3(sK9,sK12,sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_13])])).

fof(f1155,plain,
    ( spl17_88
  <=> sP2(sK9,sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_88])])).

fof(f123,plain,
    ( spl17_3
  <=> v1_funct_2(sK12,sK9,sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_3])])).

fof(f411,plain,
    ( spl17_23
  <=> sK9 = k1_relat_1(sK12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_23])])).

fof(f348,plain,
    ( spl17_16
  <=> k1_relat_1(sK12) = k1_relset_1(sK9,sK10,sK12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_16])])).

fof(f1265,plain,
    ( sK9 = k1_relat_1(sK12)
    | ~ v1_funct_2(sK12,sK9,sK10)
    | sP2(sK9,sK10)
    | ~ sP3(sK9,sK12,sK10)
    | ~ spl17_16 ),
    inference(superposition,[],[f350,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | sP2(X0,X2)
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP2(X0,X2)
      | ~ sP3(X0,X1,X2) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP2(X0,X1)
      | ~ sP3(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP2(X0,X1)
      | ~ sP3(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f350,plain,
    ( k1_relat_1(sK12) = k1_relset_1(sK9,sK10,sK12)
    | ~ spl17_16 ),
    inference(avatar_component_clause,[],[f348])).

fof(f1535,plain,
    ( ~ spl17_15
    | ~ spl17_22
    | spl17_23
    | ~ spl17_16 ),
    inference(avatar_split_clause,[],[f1266,f348,f411,f407,f262])).

fof(f262,plain,
    ( spl17_15
  <=> sP6(sK9,sK12,sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_15])])).

fof(f407,plain,
    ( spl17_22
  <=> sP5(sK12,sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_22])])).

fof(f1266,plain,
    ( sK9 = k1_relat_1(sK12)
    | ~ sP5(sK12,sK9)
    | ~ sP6(sK9,sK12,sK10)
    | ~ spl17_16 ),
    inference(superposition,[],[f350,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ sP5(X1,X0)
      | ~ sP6(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( ( sP5(X1,X0)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ sP5(X1,X0) ) )
      | ~ sP6(X0,X1,X2) ) ),
    inference(rectify,[],[f55])).

fof(f55,plain,(
    ! [X1,X2,X0] :
      ( ( ( sP5(X2,X1)
          | k1_relset_1(X1,X0,X2) != X1 )
        & ( k1_relset_1(X1,X0,X2) = X1
          | ~ sP5(X2,X1) ) )
      | ~ sP6(X1,X2,X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X1,X2,X0] :
      ( ( sP5(X2,X1)
      <=> k1_relset_1(X1,X0,X2) = X1 )
      | ~ sP6(X1,X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).

fof(f1517,plain,
    ( ~ spl17_11
    | ~ spl17_50
    | ~ spl17_106 ),
    inference(avatar_contradiction_clause,[],[f1516])).

fof(f1516,plain,
    ( $false
    | ~ spl17_11
    | ~ spl17_50
    | ~ spl17_106 ),
    inference(subsumption_resolution,[],[f1447,f299])).

fof(f299,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k9_relat_1(k1_xboole_0,X1))
    | ~ spl17_11 ),
    inference(unit_resulting_resolution,[],[f207,f289,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
      | sP0(X2,X1,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X1,X2))
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ r2_hidden(X0,k9_relat_1(X1,X2)) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X0,X2,X1] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ~ sP0(X1,X2,X0) )
        & ( sP0(X1,X2,X0)
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X2,X1] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> sP0(X1,X2,X0) )
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f289,plain,(
    ! [X0,X1] : ~ sP0(X0,k1_xboole_0,X1) ),
    inference(unit_resulting_resolution,[],[f138,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK14(X0,X1,X2),X2),X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ~ r2_hidden(X3,X0)
            | ~ r2_hidden(k4_tarski(X3,X2),X1)
            | ~ r2_hidden(X3,k1_relat_1(X1)) ) )
      & ( ( r2_hidden(sK14(X0,X1,X2),X0)
          & r2_hidden(k4_tarski(sK14(X0,X1,X2),X2),X1)
          & r2_hidden(sK14(X0,X1,X2),k1_relat_1(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f47,f48])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(k4_tarski(X4,X2),X1)
          & r2_hidden(X4,k1_relat_1(X1)) )
     => ( r2_hidden(sK14(X0,X1,X2),X0)
        & r2_hidden(k4_tarski(sK14(X0,X1,X2),X2),X1)
        & r2_hidden(sK14(X0,X1,X2),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ~ r2_hidden(X3,X0)
            | ~ r2_hidden(k4_tarski(X3,X2),X1)
            | ~ r2_hidden(X3,k1_relat_1(X1)) ) )
      & ( ? [X4] :
            ( r2_hidden(X4,X0)
            & r2_hidden(k4_tarski(X4,X2),X1)
            & r2_hidden(X4,k1_relat_1(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X1,X2,X0] :
      ( ( sP0(X1,X2,X0)
        | ! [X3] :
            ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X0),X2)
            | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) )
        | ~ sP0(X1,X2,X0) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X1,X2,X0] :
      ( sP0(X1,X2,X0)
    <=> ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(k4_tarski(X3,X0),X2)
          & r2_hidden(X3,k1_relat_1(X2)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f138,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f72,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f72,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f207,plain,
    ( ! [X0,X1] : sP1(X0,k1_xboole_0,X1)
    | ~ spl17_11 ),
    inference(unit_resulting_resolution,[],[f193,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_folding,[],[f18,f28,f27])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(f193,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl17_11 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl17_11
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_11])])).

fof(f1447,plain,
    ( r2_hidden(sK13,k9_relat_1(k1_xboole_0,sK11))
    | ~ spl17_50
    | ~ spl17_106 ),
    inference(backward_demodulation,[],[f807,f1347])).

fof(f1347,plain,
    ( k1_xboole_0 = sK12
    | ~ spl17_106 ),
    inference(avatar_component_clause,[],[f1345])).

fof(f1345,plain,
    ( spl17_106
  <=> k1_xboole_0 = sK12 ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_106])])).

fof(f807,plain,
    ( r2_hidden(sK13,k9_relat_1(sK12,sK11))
    | ~ spl17_50 ),
    inference(avatar_component_clause,[],[f805])).

fof(f805,plain,
    ( spl17_50
  <=> r2_hidden(sK13,k9_relat_1(sK12,sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_50])])).

fof(f1399,plain,
    ( spl17_22
    | ~ spl17_107 ),
    inference(avatar_contradiction_clause,[],[f1398])).

fof(f1398,plain,
    ( $false
    | spl17_22
    | ~ spl17_107 ),
    inference(subsumption_resolution,[],[f1355,f203])).

fof(f203,plain,(
    ! [X0] : sP5(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f138,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK15(X0,X1),X1)
      | sP5(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( sP5(X0,X1)
        | ( ! [X3] : ~ r2_hidden(k4_tarski(sK15(X0,X1),X3),X0)
          & r2_hidden(sK15(X0,X1),X1) ) )
      & ( ! [X4] :
            ( r2_hidden(k4_tarski(X4,sK16(X0,X4)),X0)
            | ~ r2_hidden(X4,X1) )
        | ~ sP5(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15,sK16])],[f58,f60,f59])).

fof(f59,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
          & r2_hidden(X2,X1) )
     => ( ! [X3] : ~ r2_hidden(k4_tarski(sK15(X0,X1),X3),X0)
        & r2_hidden(sK15(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X4,X0] :
      ( ? [X5] : r2_hidden(k4_tarski(X4,X5),X0)
     => r2_hidden(k4_tarski(X4,sK16(X0,X4)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( sP5(X0,X1)
        | ? [X2] :
            ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            & r2_hidden(X2,X1) ) )
      & ( ! [X4] :
            ( ? [X5] : r2_hidden(k4_tarski(X4,X5),X0)
            | ~ r2_hidden(X4,X1) )
        | ~ sP5(X0,X1) ) ) ),
    inference(rectify,[],[f57])).

fof(f57,plain,(
    ! [X2,X1] :
      ( ( sP5(X2,X1)
        | ? [X3] :
            ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
            & r2_hidden(X3,X1) ) )
      & ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) )
        | ~ sP5(X2,X1) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X2,X1] :
      ( sP5(X2,X1)
    <=> ! [X3] :
          ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
          | ~ r2_hidden(X3,X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f1355,plain,
    ( ~ sP5(sK12,k1_xboole_0)
    | spl17_22
    | ~ spl17_107 ),
    inference(backward_demodulation,[],[f409,f1351])).

fof(f1351,plain,
    ( k1_xboole_0 = sK9
    | ~ spl17_107 ),
    inference(avatar_component_clause,[],[f1349])).

fof(f1349,plain,
    ( spl17_107
  <=> k1_xboole_0 = sK9 ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_107])])).

fof(f409,plain,
    ( ~ sP5(sK12,sK9)
    | spl17_22 ),
    inference(avatar_component_clause,[],[f407])).

fof(f1352,plain,
    ( spl17_106
    | spl17_107
    | ~ spl17_97
    | ~ spl17_101 ),
    inference(avatar_split_clause,[],[f1343,f1316,f1296,f1349,f1345])).

fof(f1296,plain,
    ( spl17_97
  <=> v1_funct_2(sK12,sK9,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_97])])).

fof(f1316,plain,
    ( spl17_101
  <=> sP4(sK12,k1_xboole_0,sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_101])])).

fof(f1343,plain,
    ( k1_xboole_0 = sK9
    | k1_xboole_0 = sK12
    | ~ spl17_97
    | ~ spl17_101 ),
    inference(subsumption_resolution,[],[f1342,f1298])).

fof(f1298,plain,
    ( v1_funct_2(sK12,sK9,k1_xboole_0)
    | ~ spl17_97 ),
    inference(avatar_component_clause,[],[f1296])).

fof(f1342,plain,
    ( ~ v1_funct_2(sK12,sK9,k1_xboole_0)
    | k1_xboole_0 = sK9
    | k1_xboole_0 = sK12
    | ~ spl17_101 ),
    inference(resolution,[],[f1318,f109])).

fof(f109,plain,(
    ! [X2,X0] :
      ( ~ sP4(X0,k1_xboole_0,X2)
      | ~ v1_funct_2(X0,X2,k1_xboole_0)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ v1_funct_2(X0,X2,X1)
      | k1_xboole_0 = X2
      | k1_xboole_0 != X1
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X0,X2,X1)
          | k1_xboole_0 != X0 )
        & ( k1_xboole_0 = X0
          | ~ v1_funct_2(X0,X2,X1) ) )
      | k1_xboole_0 = X2
      | k1_xboole_0 != X1
      | ~ sP4(X0,X1,X2) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X2,X1,X0] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_xboole_0 != X2 )
        & ( k1_xboole_0 = X2
          | ~ v1_funct_2(X2,X0,X1) ) )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP4(X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP4(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f1318,plain,
    ( sP4(sK12,k1_xboole_0,sK9)
    | ~ spl17_101 ),
    inference(avatar_component_clause,[],[f1316])).

fof(f1319,plain,
    ( spl17_101
    | ~ spl17_14
    | ~ spl17_95 ),
    inference(avatar_split_clause,[],[f1284,f1274,f242,f1316])).

fof(f242,plain,
    ( spl17_14
  <=> sP4(sK12,sK10,sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_14])])).

fof(f1274,plain,
    ( spl17_95
  <=> k1_xboole_0 = sK10 ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_95])])).

fof(f1284,plain,
    ( sP4(sK12,k1_xboole_0,sK9)
    | ~ spl17_14
    | ~ spl17_95 ),
    inference(backward_demodulation,[],[f244,f1276])).

fof(f1276,plain,
    ( k1_xboole_0 = sK10
    | ~ spl17_95 ),
    inference(avatar_component_clause,[],[f1274])).

fof(f244,plain,
    ( sP4(sK12,sK10,sK9)
    | ~ spl17_14 ),
    inference(avatar_component_clause,[],[f242])).

fof(f1299,plain,
    ( spl17_97
    | ~ spl17_3
    | ~ spl17_95 ),
    inference(avatar_split_clause,[],[f1280,f1274,f123,f1296])).

fof(f1280,plain,
    ( v1_funct_2(sK12,sK9,k1_xboole_0)
    | ~ spl17_3
    | ~ spl17_95 ),
    inference(backward_demodulation,[],[f125,f1276])).

fof(f125,plain,
    ( v1_funct_2(sK12,sK9,sK10)
    | ~ spl17_3 ),
    inference(avatar_component_clause,[],[f123])).

fof(f1278,plain,
    ( spl17_95
    | ~ spl17_88 ),
    inference(avatar_split_clause,[],[f1272,f1155,f1274])).

fof(f1272,plain,
    ( k1_xboole_0 = sK10
    | ~ spl17_88 ),
    inference(resolution,[],[f1157,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ sP2(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP2(X0,X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP2(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f1157,plain,
    ( sP2(sK9,sK10)
    | ~ spl17_88 ),
    inference(avatar_component_clause,[],[f1155])).

fof(f1104,plain,
    ( spl17_82
    | ~ spl17_61 ),
    inference(avatar_split_clause,[],[f1098,f925,f1101])).

fof(f925,plain,
    ( spl17_61
  <=> r2_hidden(sK14(sK11,sK12,sK13),sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_61])])).

fof(f1098,plain,
    ( m1_subset_1(sK14(sK11,sK12,sK13),sK9)
    | ~ spl17_61 ),
    inference(unit_resulting_resolution,[],[f927,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f927,plain,
    ( r2_hidden(sK14(sK11,sK12,sK13),sK9)
    | ~ spl17_61 ),
    inference(avatar_component_clause,[],[f925])).

fof(f939,plain,
    ( spl17_63
    | ~ spl17_58 ),
    inference(avatar_split_clause,[],[f908,f897,f936])).

fof(f897,plain,
    ( spl17_58
  <=> sP0(sK11,sK12,sK13) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_58])])).

fof(f908,plain,
    ( r2_hidden(k4_tarski(sK14(sK11,sK12,sK13),sK13),sK12)
    | ~ spl17_58 ),
    inference(unit_resulting_resolution,[],[f899,f80])).

fof(f899,plain,
    ( sP0(sK11,sK12,sK13)
    | ~ spl17_58 ),
    inference(avatar_component_clause,[],[f897])).

fof(f928,plain,
    ( spl17_61
    | ~ spl17_23
    | ~ spl17_58 ),
    inference(avatar_split_clause,[],[f923,f897,f411,f925])).

fof(f923,plain,
    ( r2_hidden(sK14(sK11,sK12,sK13),sK9)
    | ~ spl17_23
    | ~ spl17_58 ),
    inference(forward_demodulation,[],[f910,f413])).

fof(f413,plain,
    ( sK9 = k1_relat_1(sK12)
    | ~ spl17_23 ),
    inference(avatar_component_clause,[],[f411])).

fof(f910,plain,
    ( r2_hidden(sK14(sK11,sK12,sK13),k1_relat_1(sK12))
    | ~ spl17_58 ),
    inference(unit_resulting_resolution,[],[f899,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK14(X0,X1,X2),k1_relat_1(X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f917,plain,
    ( spl17_59
    | ~ spl17_58 ),
    inference(avatar_split_clause,[],[f912,f897,f914])).

fof(f912,plain,
    ( r2_hidden(sK14(sK11,sK12,sK13),sK11)
    | ~ spl17_58 ),
    inference(unit_resulting_resolution,[],[f899,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK14(X0,X1,X2),X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f901,plain,
    ( spl17_58
    | ~ spl17_12
    | ~ spl17_50 ),
    inference(avatar_split_clause,[],[f877,f805,f196,f897])).

fof(f877,plain,
    ( sP0(sK11,sK12,sK13)
    | ~ spl17_12
    | ~ spl17_50 ),
    inference(unit_resulting_resolution,[],[f202,f807,f77])).

fof(f202,plain,
    ( ! [X0,X1] : sP1(X0,sK12,X1)
    | ~ spl17_12 ),
    inference(unit_resulting_resolution,[],[f198,f83])).

fof(f853,plain,
    ( spl17_50
    | ~ spl17_1
    | ~ spl17_2 ),
    inference(avatar_split_clause,[],[f852,f118,f113,f805])).

fof(f113,plain,
    ( spl17_1
  <=> r2_hidden(sK13,k7_relset_1(sK9,sK10,sK12,sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_1])])).

fof(f118,plain,
    ( spl17_2
  <=> m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_2])])).

fof(f852,plain,
    ( r2_hidden(sK13,k9_relat_1(sK12,sK11))
    | ~ spl17_1
    | ~ spl17_2 ),
    inference(subsumption_resolution,[],[f795,f120])).

fof(f120,plain,
    ( m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10)))
    | ~ spl17_2 ),
    inference(avatar_component_clause,[],[f118])).

fof(f795,plain,
    ( r2_hidden(sK13,k9_relat_1(sK12,sK11))
    | ~ m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10)))
    | ~ spl17_1 ),
    inference(superposition,[],[f115,f106])).

fof(f106,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f115,plain,
    ( r2_hidden(sK13,k7_relset_1(sK9,sK10,sK12,sK11))
    | ~ spl17_1 ),
    inference(avatar_component_clause,[],[f113])).

fof(f351,plain,
    ( spl17_16
    | ~ spl17_2 ),
    inference(avatar_split_clause,[],[f345,f118,f348])).

fof(f345,plain,
    ( k1_relat_1(sK12) = k1_relset_1(sK9,sK10,sK12)
    | ~ spl17_2 ),
    inference(unit_resulting_resolution,[],[f120,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f266,plain,
    ( spl17_15
    | ~ spl17_2 ),
    inference(avatar_split_clause,[],[f260,f118,f262])).

fof(f260,plain,
    ( sP6(sK9,sK12,sK10)
    | ~ spl17_2 ),
    inference(resolution,[],[f99,f120])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | sP6(X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( sP6(X1,X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(definition_folding,[],[f23,f35,f34])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).

fof(f246,plain,
    ( spl17_14
    | ~ spl17_2 ),
    inference(avatar_split_clause,[],[f240,f118,f242])).

fof(f240,plain,
    ( sP4(sK12,sK10,sK9)
    | ~ spl17_2 ),
    inference(resolution,[],[f93,f120])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP4(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X2,X1,X0)
        & sP3(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f22,f32,f31,f30])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f234,plain,
    ( spl17_13
    | ~ spl17_2 ),
    inference(avatar_split_clause,[],[f228,f118,f230])).

fof(f228,plain,
    ( sP3(sK9,sK12,sK10)
    | ~ spl17_2 ),
    inference(resolution,[],[f92,f120])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP3(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f201,plain,
    ( spl17_12
    | ~ spl17_2 ),
    inference(avatar_split_clause,[],[f189,f118,f196])).

fof(f189,plain,
    ( v1_relat_1(sK12)
    | ~ spl17_2 ),
    inference(resolution,[],[f84,f120])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f200,plain,(
    spl17_11 ),
    inference(avatar_split_clause,[],[f188,f191])).

fof(f188,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f84,f168])).

fof(f168,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f72,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f131,plain,(
    spl17_4 ),
    inference(avatar_split_clause,[],[f67,f128])).

fof(f67,plain,(
    v1_funct_1(sK12) ),
    inference(cnf_transformation,[],[f42])).

fof(f126,plain,(
    spl17_3 ),
    inference(avatar_split_clause,[],[f68,f123])).

fof(f68,plain,(
    v1_funct_2(sK12,sK9,sK10) ),
    inference(cnf_transformation,[],[f42])).

fof(f121,plain,(
    spl17_2 ),
    inference(avatar_split_clause,[],[f69,f118])).

fof(f69,plain,(
    m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))) ),
    inference(cnf_transformation,[],[f42])).

fof(f116,plain,(
    spl17_1 ),
    inference(avatar_split_clause,[],[f70,f113])).

fof(f70,plain,(
    r2_hidden(sK13,k7_relset_1(sK9,sK10,sK12,sK11)) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:27:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.43  % (27462)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.47  % (27451)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.47  % (27462)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f2513,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f116,f121,f126,f131,f200,f201,f234,f246,f266,f351,f853,f901,f917,f928,f939,f1104,f1278,f1299,f1319,f1352,f1399,f1517,f1535,f1539,f2434,f2511])).
% 0.20/0.48  fof(f2511,plain,(
% 0.20/0.48    ~spl17_59 | ~spl17_82 | ~spl17_184),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f2510])).
% 0.20/0.48  fof(f2510,plain,(
% 0.20/0.48    $false | (~spl17_59 | ~spl17_82 | ~spl17_184)),
% 0.20/0.48    inference(subsumption_resolution,[],[f2509,f1103])).
% 0.20/0.48  fof(f1103,plain,(
% 0.20/0.48    m1_subset_1(sK14(sK11,sK12,sK13),sK9) | ~spl17_82),
% 0.20/0.48    inference(avatar_component_clause,[],[f1101])).
% 0.20/0.48  fof(f1101,plain,(
% 0.20/0.48    spl17_82 <=> m1_subset_1(sK14(sK11,sK12,sK13),sK9)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl17_82])])).
% 0.20/0.48  fof(f2509,plain,(
% 0.20/0.48    ~m1_subset_1(sK14(sK11,sK12,sK13),sK9) | (~spl17_59 | ~spl17_184)),
% 0.20/0.48    inference(subsumption_resolution,[],[f2503,f916])).
% 0.20/0.48  fof(f916,plain,(
% 0.20/0.48    r2_hidden(sK14(sK11,sK12,sK13),sK11) | ~spl17_59),
% 0.20/0.48    inference(avatar_component_clause,[],[f914])).
% 0.20/0.48  fof(f914,plain,(
% 0.20/0.48    spl17_59 <=> r2_hidden(sK14(sK11,sK12,sK13),sK11)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl17_59])])).
% 0.20/0.48  fof(f2503,plain,(
% 0.20/0.48    ~r2_hidden(sK14(sK11,sK12,sK13),sK11) | ~m1_subset_1(sK14(sK11,sK12,sK13),sK9) | ~spl17_184),
% 0.20/0.48    inference(trivial_inequality_removal,[],[f2500])).
% 0.20/0.48  fof(f2500,plain,(
% 0.20/0.48    ~r2_hidden(sK14(sK11,sK12,sK13),sK11) | ~m1_subset_1(sK14(sK11,sK12,sK13),sK9) | sK13 != sK13 | ~spl17_184),
% 0.20/0.48    inference(resolution,[],[f2429,f214])).
% 0.20/0.48  fof(f214,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~sP7(X1,X0,sK12) | ~r2_hidden(X0,sK11) | ~m1_subset_1(X0,sK9) | sK13 != X1) )),
% 0.20/0.48    inference(superposition,[],[f71,f103])).
% 0.20/0.48  fof(f103,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k1_funct_1(X2,X1) = X0 | ~sP7(X0,X1,X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f66])).
% 0.20/0.48  fof(f66,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((sP7(X0,X1,X2) | k1_funct_1(X2,X1) != X0 | ~r2_hidden(X1,k1_relat_1(X2))) & ((k1_funct_1(X2,X1) = X0 & r2_hidden(X1,k1_relat_1(X2))) | ~sP7(X0,X1,X2)))),
% 0.20/0.48    inference(rectify,[],[f65])).
% 0.20/0.48  fof(f65,plain,(
% 0.20/0.48    ! [X1,X0,X2] : ((sP7(X1,X0,X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~sP7(X1,X0,X2)))),
% 0.20/0.48    inference(flattening,[],[f64])).
% 0.20/0.48  fof(f64,plain,(
% 0.20/0.48    ! [X1,X0,X2] : ((sP7(X1,X0,X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~sP7(X1,X0,X2)))),
% 0.20/0.48    inference(nnf_transformation,[],[f37])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ! [X1,X0,X2] : (sP7(X1,X0,X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))))),
% 0.20/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP7])])).
% 0.20/0.48  fof(f71,plain,(
% 0.20/0.48    ( ! [X5] : (k1_funct_1(sK12,X5) != sK13 | ~r2_hidden(X5,sK11) | ~m1_subset_1(X5,sK9)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f42])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    (! [X5] : (k1_funct_1(sK12,X5) != sK13 | ~r2_hidden(X5,sK11) | ~m1_subset_1(X5,sK9)) & r2_hidden(sK13,k7_relset_1(sK9,sK10,sK12,sK11))) & m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))) & v1_funct_2(sK12,sK9,sK10) & v1_funct_1(sK12)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11,sK12,sK13])],[f15,f41,f40])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK12,X5) != X4 | ~r2_hidden(X5,sK11) | ~m1_subset_1(X5,sK9)) & r2_hidden(X4,k7_relset_1(sK9,sK10,sK12,sK11))) & m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))) & v1_funct_2(sK12,sK9,sK10) & v1_funct_1(sK12))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    ? [X4] : (! [X5] : (k1_funct_1(sK12,X5) != X4 | ~r2_hidden(X5,sK11) | ~m1_subset_1(X5,sK9)) & r2_hidden(X4,k7_relset_1(sK9,sK10,sK12,sK11))) => (! [X5] : (k1_funct_1(sK12,X5) != sK13 | ~r2_hidden(X5,sK11) | ~m1_subset_1(X5,sK9)) & r2_hidden(sK13,k7_relset_1(sK9,sK10,sK12,sK11)))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.20/0.48    inference(flattening,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.20/0.48    inference(ennf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.20/0.48    inference(negated_conjecture,[],[f12])).
% 0.20/0.48  fof(f12,conjecture,(
% 0.20/0.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).
% 0.20/0.48  fof(f2429,plain,(
% 0.20/0.48    sP7(sK13,sK14(sK11,sK12,sK13),sK12) | ~spl17_184),
% 0.20/0.48    inference(avatar_component_clause,[],[f2427])).
% 0.20/0.48  fof(f2427,plain,(
% 0.20/0.48    spl17_184 <=> sP7(sK13,sK14(sK11,sK12,sK13),sK12)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl17_184])])).
% 0.20/0.48  fof(f2434,plain,(
% 0.20/0.48    spl17_184 | ~spl17_4 | ~spl17_12 | ~spl17_63),
% 0.20/0.48    inference(avatar_split_clause,[],[f2433,f936,f196,f128,f2427])).
% 0.20/0.48  fof(f128,plain,(
% 0.20/0.48    spl17_4 <=> v1_funct_1(sK12)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl17_4])])).
% 0.20/0.48  fof(f196,plain,(
% 0.20/0.48    spl17_12 <=> v1_relat_1(sK12)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl17_12])])).
% 0.20/0.48  fof(f936,plain,(
% 0.20/0.48    spl17_63 <=> r2_hidden(k4_tarski(sK14(sK11,sK12,sK13),sK13),sK12)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl17_63])])).
% 0.20/0.48  fof(f2433,plain,(
% 0.20/0.48    sP7(sK13,sK14(sK11,sK12,sK13),sK12) | (~spl17_4 | ~spl17_12 | ~spl17_63)),
% 0.20/0.48    inference(subsumption_resolution,[],[f2413,f212])).
% 0.20/0.48  fof(f212,plain,(
% 0.20/0.48    ( ! [X0,X1] : (sP8(sK12,X0,X1)) ) | (~spl17_4 | ~spl17_12)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f198,f130,f105])).
% 0.20/0.48  fof(f105,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (sP8(X2,X0,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f39])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (sP8(X2,X0,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.48    inference(definition_folding,[],[f25,f38,f37])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ! [X2,X0,X1] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> sP7(X1,X0,X2)) | ~sP8(X2,X0,X1))),
% 0.20/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP8])])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.48    inference(flattening,[],[f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 0.20/0.48  fof(f130,plain,(
% 0.20/0.48    v1_funct_1(sK12) | ~spl17_4),
% 0.20/0.48    inference(avatar_component_clause,[],[f128])).
% 0.20/0.48  fof(f198,plain,(
% 0.20/0.48    v1_relat_1(sK12) | ~spl17_12),
% 0.20/0.48    inference(avatar_component_clause,[],[f196])).
% 0.20/0.48  fof(f2413,plain,(
% 0.20/0.48    sP7(sK13,sK14(sK11,sK12,sK13),sK12) | ~sP8(sK12,sK14(sK11,sK12,sK13),sK13) | ~spl17_63),
% 0.20/0.48    inference(resolution,[],[f938,f100])).
% 0.20/0.48  fof(f100,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X1,X2),X0) | sP7(X2,X1,X0) | ~sP8(X0,X1,X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f63])).
% 0.20/0.48  fof(f63,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X1,X2),X0) | ~sP7(X2,X1,X0)) & (sP7(X2,X1,X0) | ~r2_hidden(k4_tarski(X1,X2),X0))) | ~sP8(X0,X1,X2))),
% 0.20/0.48    inference(rectify,[],[f62])).
% 0.20/0.48  fof(f62,plain,(
% 0.20/0.48    ! [X2,X0,X1] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~sP7(X1,X0,X2)) & (sP7(X1,X0,X2) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~sP8(X2,X0,X1))),
% 0.20/0.48    inference(nnf_transformation,[],[f38])).
% 0.20/0.48  fof(f938,plain,(
% 0.20/0.48    r2_hidden(k4_tarski(sK14(sK11,sK12,sK13),sK13),sK12) | ~spl17_63),
% 0.20/0.48    inference(avatar_component_clause,[],[f936])).
% 0.20/0.48  fof(f1539,plain,(
% 0.20/0.48    ~spl17_13 | spl17_88 | ~spl17_3 | spl17_23 | ~spl17_16),
% 0.20/0.48    inference(avatar_split_clause,[],[f1265,f348,f411,f123,f1155,f230])).
% 0.20/0.48  fof(f230,plain,(
% 0.20/0.48    spl17_13 <=> sP3(sK9,sK12,sK10)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl17_13])])).
% 0.20/0.48  fof(f1155,plain,(
% 0.20/0.48    spl17_88 <=> sP2(sK9,sK10)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl17_88])])).
% 0.20/0.48  fof(f123,plain,(
% 0.20/0.48    spl17_3 <=> v1_funct_2(sK12,sK9,sK10)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl17_3])])).
% 0.20/0.48  fof(f411,plain,(
% 0.20/0.48    spl17_23 <=> sK9 = k1_relat_1(sK12)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl17_23])])).
% 0.20/0.48  fof(f348,plain,(
% 0.20/0.48    spl17_16 <=> k1_relat_1(sK12) = k1_relset_1(sK9,sK10,sK12)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl17_16])])).
% 0.20/0.48  fof(f1265,plain,(
% 0.20/0.48    sK9 = k1_relat_1(sK12) | ~v1_funct_2(sK12,sK9,sK10) | sP2(sK9,sK10) | ~sP3(sK9,sK12,sK10) | ~spl17_16),
% 0.20/0.48    inference(superposition,[],[f350,f88])).
% 0.20/0.48  fof(f88,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | sP2(X0,X2) | ~sP3(X0,X1,X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f53])).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP2(X0,X2) | ~sP3(X0,X1,X2))),
% 0.20/0.48    inference(rectify,[],[f52])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP2(X0,X1) | ~sP3(X0,X2,X1))),
% 0.20/0.48    inference(nnf_transformation,[],[f31])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP2(X0,X1) | ~sP3(X0,X2,X1))),
% 0.20/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.20/0.48  fof(f350,plain,(
% 0.20/0.48    k1_relat_1(sK12) = k1_relset_1(sK9,sK10,sK12) | ~spl17_16),
% 0.20/0.48    inference(avatar_component_clause,[],[f348])).
% 0.20/0.48  fof(f1535,plain,(
% 0.20/0.48    ~spl17_15 | ~spl17_22 | spl17_23 | ~spl17_16),
% 0.20/0.48    inference(avatar_split_clause,[],[f1266,f348,f411,f407,f262])).
% 0.20/0.48  fof(f262,plain,(
% 0.20/0.48    spl17_15 <=> sP6(sK9,sK12,sK10)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl17_15])])).
% 0.20/0.48  fof(f407,plain,(
% 0.20/0.48    spl17_22 <=> sP5(sK12,sK9)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl17_22])])).
% 0.20/0.48  fof(f1266,plain,(
% 0.20/0.48    sK9 = k1_relat_1(sK12) | ~sP5(sK12,sK9) | ~sP6(sK9,sK12,sK10) | ~spl17_16),
% 0.20/0.48    inference(superposition,[],[f350,f94])).
% 0.20/0.48  fof(f94,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~sP5(X1,X0) | ~sP6(X0,X1,X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f56])).
% 0.20/0.48  fof(f56,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (((sP5(X1,X0) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~sP5(X1,X0))) | ~sP6(X0,X1,X2))),
% 0.20/0.48    inference(rectify,[],[f55])).
% 0.20/0.48  fof(f55,plain,(
% 0.20/0.48    ! [X1,X2,X0] : (((sP5(X2,X1) | k1_relset_1(X1,X0,X2) != X1) & (k1_relset_1(X1,X0,X2) = X1 | ~sP5(X2,X1))) | ~sP6(X1,X2,X0))),
% 0.20/0.48    inference(nnf_transformation,[],[f35])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ! [X1,X2,X0] : ((sP5(X2,X1) <=> k1_relset_1(X1,X0,X2) = X1) | ~sP6(X1,X2,X0))),
% 0.20/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).
% 0.20/0.48  fof(f1517,plain,(
% 0.20/0.48    ~spl17_11 | ~spl17_50 | ~spl17_106),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f1516])).
% 0.20/0.48  fof(f1516,plain,(
% 0.20/0.48    $false | (~spl17_11 | ~spl17_50 | ~spl17_106)),
% 0.20/0.48    inference(subsumption_resolution,[],[f1447,f299])).
% 0.20/0.48  fof(f299,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(k1_xboole_0,X1))) ) | ~spl17_11),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f207,f289,f77])).
% 0.20/0.48  fof(f77,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X1,X2)) | sP0(X2,X1,X0) | ~sP1(X0,X1,X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f45])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X1,X2)) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~r2_hidden(X0,k9_relat_1(X1,X2)))) | ~sP1(X0,X1,X2))),
% 0.20/0.48    inference(rectify,[],[f44])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    ! [X0,X2,X1] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ~sP0(X1,X2,X0)) & (sP0(X1,X2,X0) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~sP1(X0,X2,X1))),
% 0.20/0.48    inference(nnf_transformation,[],[f28])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ! [X0,X2,X1] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> sP0(X1,X2,X0)) | ~sP1(X0,X2,X1))),
% 0.20/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.48  fof(f289,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~sP0(X0,k1_xboole_0,X1)) )),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f138,f80])).
% 0.20/0.48  fof(f80,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK14(X0,X1,X2),X2),X1) | ~sP0(X0,X1,X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f49])).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(k4_tarski(X3,X2),X1) | ~r2_hidden(X3,k1_relat_1(X1)))) & ((r2_hidden(sK14(X0,X1,X2),X0) & r2_hidden(k4_tarski(sK14(X0,X1,X2),X2),X1) & r2_hidden(sK14(X0,X1,X2),k1_relat_1(X1))) | ~sP0(X0,X1,X2)))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f47,f48])).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(k4_tarski(X4,X2),X1) & r2_hidden(X4,k1_relat_1(X1))) => (r2_hidden(sK14(X0,X1,X2),X0) & r2_hidden(k4_tarski(sK14(X0,X1,X2),X2),X1) & r2_hidden(sK14(X0,X1,X2),k1_relat_1(X1))))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(k4_tarski(X3,X2),X1) | ~r2_hidden(X3,k1_relat_1(X1)))) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(k4_tarski(X4,X2),X1) & r2_hidden(X4,k1_relat_1(X1))) | ~sP0(X0,X1,X2)))),
% 0.20/0.48    inference(rectify,[],[f46])).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    ! [X1,X2,X0] : ((sP0(X1,X2,X0) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~sP0(X1,X2,X0)))),
% 0.20/0.48    inference(nnf_transformation,[],[f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ! [X1,X2,X0] : (sP0(X1,X2,X0) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))))),
% 0.20/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.48  fof(f138,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f72,f76])).
% 0.20/0.48  fof(f76,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.20/0.48  fof(f72,plain,(
% 0.20/0.48    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.48  fof(f207,plain,(
% 0.20/0.48    ( ! [X0,X1] : (sP1(X0,k1_xboole_0,X1)) ) | ~spl17_11),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f193,f83])).
% 0.20/0.48  fof(f83,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (sP1(X0,X2,X1) | ~v1_relat_1(X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f29])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (sP1(X0,X2,X1) | ~v1_relat_1(X2))),
% 0.20/0.48    inference(definition_folding,[],[f18,f28,f27])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).
% 0.20/0.48  fof(f193,plain,(
% 0.20/0.48    v1_relat_1(k1_xboole_0) | ~spl17_11),
% 0.20/0.48    inference(avatar_component_clause,[],[f191])).
% 0.20/0.48  fof(f191,plain,(
% 0.20/0.48    spl17_11 <=> v1_relat_1(k1_xboole_0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl17_11])])).
% 0.20/0.48  fof(f1447,plain,(
% 0.20/0.48    r2_hidden(sK13,k9_relat_1(k1_xboole_0,sK11)) | (~spl17_50 | ~spl17_106)),
% 0.20/0.48    inference(backward_demodulation,[],[f807,f1347])).
% 0.20/0.48  fof(f1347,plain,(
% 0.20/0.48    k1_xboole_0 = sK12 | ~spl17_106),
% 0.20/0.48    inference(avatar_component_clause,[],[f1345])).
% 0.20/0.48  fof(f1345,plain,(
% 0.20/0.48    spl17_106 <=> k1_xboole_0 = sK12),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl17_106])])).
% 0.20/0.48  fof(f807,plain,(
% 0.20/0.48    r2_hidden(sK13,k9_relat_1(sK12,sK11)) | ~spl17_50),
% 0.20/0.48    inference(avatar_component_clause,[],[f805])).
% 0.20/0.48  fof(f805,plain,(
% 0.20/0.48    spl17_50 <=> r2_hidden(sK13,k9_relat_1(sK12,sK11))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl17_50])])).
% 0.20/0.48  fof(f1399,plain,(
% 0.20/0.48    spl17_22 | ~spl17_107),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f1398])).
% 0.20/0.48  fof(f1398,plain,(
% 0.20/0.48    $false | (spl17_22 | ~spl17_107)),
% 0.20/0.48    inference(subsumption_resolution,[],[f1355,f203])).
% 0.20/0.48  fof(f203,plain,(
% 0.20/0.48    ( ! [X0] : (sP5(X0,k1_xboole_0)) )),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f138,f97])).
% 0.20/0.48  fof(f97,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r2_hidden(sK15(X0,X1),X1) | sP5(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f61])).
% 0.20/0.48  fof(f61,plain,(
% 0.20/0.48    ! [X0,X1] : ((sP5(X0,X1) | (! [X3] : ~r2_hidden(k4_tarski(sK15(X0,X1),X3),X0) & r2_hidden(sK15(X0,X1),X1))) & (! [X4] : (r2_hidden(k4_tarski(X4,sK16(X0,X4)),X0) | ~r2_hidden(X4,X1)) | ~sP5(X0,X1)))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15,sK16])],[f58,f60,f59])).
% 0.20/0.48  fof(f59,plain,(
% 0.20/0.48    ! [X1,X0] : (? [X2] : (! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X2,X1)) => (! [X3] : ~r2_hidden(k4_tarski(sK15(X0,X1),X3),X0) & r2_hidden(sK15(X0,X1),X1)))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f60,plain,(
% 0.20/0.48    ! [X4,X0] : (? [X5] : r2_hidden(k4_tarski(X4,X5),X0) => r2_hidden(k4_tarski(X4,sK16(X0,X4)),X0))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f58,plain,(
% 0.20/0.48    ! [X0,X1] : ((sP5(X0,X1) | ? [X2] : (! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X2,X1))) & (! [X4] : (? [X5] : r2_hidden(k4_tarski(X4,X5),X0) | ~r2_hidden(X4,X1)) | ~sP5(X0,X1)))),
% 0.20/0.48    inference(rectify,[],[f57])).
% 0.20/0.48  fof(f57,plain,(
% 0.20/0.48    ! [X2,X1] : ((sP5(X2,X1) | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1))) & (! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) | ~sP5(X2,X1)))),
% 0.20/0.48    inference(nnf_transformation,[],[f34])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ! [X2,X1] : (sP5(X2,X1) <=> ! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)))),
% 0.20/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 0.20/0.48  fof(f1355,plain,(
% 0.20/0.48    ~sP5(sK12,k1_xboole_0) | (spl17_22 | ~spl17_107)),
% 0.20/0.48    inference(backward_demodulation,[],[f409,f1351])).
% 0.20/0.48  fof(f1351,plain,(
% 0.20/0.48    k1_xboole_0 = sK9 | ~spl17_107),
% 0.20/0.48    inference(avatar_component_clause,[],[f1349])).
% 0.20/0.48  fof(f1349,plain,(
% 0.20/0.48    spl17_107 <=> k1_xboole_0 = sK9),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl17_107])])).
% 0.20/0.48  fof(f409,plain,(
% 0.20/0.48    ~sP5(sK12,sK9) | spl17_22),
% 0.20/0.48    inference(avatar_component_clause,[],[f407])).
% 0.20/0.48  fof(f1352,plain,(
% 0.20/0.48    spl17_106 | spl17_107 | ~spl17_97 | ~spl17_101),
% 0.20/0.48    inference(avatar_split_clause,[],[f1343,f1316,f1296,f1349,f1345])).
% 0.20/0.48  fof(f1296,plain,(
% 0.20/0.48    spl17_97 <=> v1_funct_2(sK12,sK9,k1_xboole_0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl17_97])])).
% 0.20/0.48  fof(f1316,plain,(
% 0.20/0.48    spl17_101 <=> sP4(sK12,k1_xboole_0,sK9)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl17_101])])).
% 0.20/0.48  fof(f1343,plain,(
% 0.20/0.48    k1_xboole_0 = sK9 | k1_xboole_0 = sK12 | (~spl17_97 | ~spl17_101)),
% 0.20/0.48    inference(subsumption_resolution,[],[f1342,f1298])).
% 0.20/0.48  fof(f1298,plain,(
% 0.20/0.48    v1_funct_2(sK12,sK9,k1_xboole_0) | ~spl17_97),
% 0.20/0.48    inference(avatar_component_clause,[],[f1296])).
% 0.20/0.48  fof(f1342,plain,(
% 0.20/0.48    ~v1_funct_2(sK12,sK9,k1_xboole_0) | k1_xboole_0 = sK9 | k1_xboole_0 = sK12 | ~spl17_101),
% 0.20/0.48    inference(resolution,[],[f1318,f109])).
% 0.20/0.48  fof(f109,plain,(
% 0.20/0.48    ( ! [X2,X0] : (~sP4(X0,k1_xboole_0,X2) | ~v1_funct_2(X0,X2,k1_xboole_0) | k1_xboole_0 = X2 | k1_xboole_0 = X0) )),
% 0.20/0.48    inference(equality_resolution,[],[f86])).
% 0.20/0.48  fof(f86,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~v1_funct_2(X0,X2,X1) | k1_xboole_0 = X2 | k1_xboole_0 != X1 | ~sP4(X0,X1,X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f51])).
% 0.20/0.48  fof(f51,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (((v1_funct_2(X0,X2,X1) | k1_xboole_0 != X0) & (k1_xboole_0 = X0 | ~v1_funct_2(X0,X2,X1))) | k1_xboole_0 = X2 | k1_xboole_0 != X1 | ~sP4(X0,X1,X2))),
% 0.20/0.48    inference(rectify,[],[f50])).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    ! [X2,X1,X0] : (((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP4(X2,X1,X0))),
% 0.20/0.48    inference(nnf_transformation,[],[f32])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP4(X2,X1,X0))),
% 0.20/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 0.20/0.48  fof(f1318,plain,(
% 0.20/0.48    sP4(sK12,k1_xboole_0,sK9) | ~spl17_101),
% 0.20/0.48    inference(avatar_component_clause,[],[f1316])).
% 0.20/0.48  fof(f1319,plain,(
% 0.20/0.48    spl17_101 | ~spl17_14 | ~spl17_95),
% 0.20/0.48    inference(avatar_split_clause,[],[f1284,f1274,f242,f1316])).
% 0.20/0.48  fof(f242,plain,(
% 0.20/0.48    spl17_14 <=> sP4(sK12,sK10,sK9)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl17_14])])).
% 0.20/0.48  fof(f1274,plain,(
% 0.20/0.48    spl17_95 <=> k1_xboole_0 = sK10),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl17_95])])).
% 0.20/0.48  fof(f1284,plain,(
% 0.20/0.48    sP4(sK12,k1_xboole_0,sK9) | (~spl17_14 | ~spl17_95)),
% 0.20/0.48    inference(backward_demodulation,[],[f244,f1276])).
% 0.20/0.48  fof(f1276,plain,(
% 0.20/0.48    k1_xboole_0 = sK10 | ~spl17_95),
% 0.20/0.48    inference(avatar_component_clause,[],[f1274])).
% 0.20/0.48  fof(f244,plain,(
% 0.20/0.48    sP4(sK12,sK10,sK9) | ~spl17_14),
% 0.20/0.48    inference(avatar_component_clause,[],[f242])).
% 0.20/0.48  fof(f1299,plain,(
% 0.20/0.48    spl17_97 | ~spl17_3 | ~spl17_95),
% 0.20/0.48    inference(avatar_split_clause,[],[f1280,f1274,f123,f1296])).
% 0.20/0.48  fof(f1280,plain,(
% 0.20/0.48    v1_funct_2(sK12,sK9,k1_xboole_0) | (~spl17_3 | ~spl17_95)),
% 0.20/0.48    inference(backward_demodulation,[],[f125,f1276])).
% 0.20/0.48  fof(f125,plain,(
% 0.20/0.48    v1_funct_2(sK12,sK9,sK10) | ~spl17_3),
% 0.20/0.48    inference(avatar_component_clause,[],[f123])).
% 0.20/0.48  fof(f1278,plain,(
% 0.20/0.48    spl17_95 | ~spl17_88),
% 0.20/0.48    inference(avatar_split_clause,[],[f1272,f1155,f1274])).
% 0.20/0.48  fof(f1272,plain,(
% 0.20/0.48    k1_xboole_0 = sK10 | ~spl17_88),
% 0.20/0.48    inference(resolution,[],[f1157,f90])).
% 0.20/0.48  fof(f90,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~sP2(X0,X1) | k1_xboole_0 = X1) )),
% 0.20/0.48    inference(cnf_transformation,[],[f54])).
% 0.20/0.48  fof(f54,plain,(
% 0.20/0.48    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP2(X0,X1))),
% 0.20/0.48    inference(nnf_transformation,[],[f30])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP2(X0,X1))),
% 0.20/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.20/0.48  fof(f1157,plain,(
% 0.20/0.48    sP2(sK9,sK10) | ~spl17_88),
% 0.20/0.48    inference(avatar_component_clause,[],[f1155])).
% 0.20/0.48  fof(f1104,plain,(
% 0.20/0.48    spl17_82 | ~spl17_61),
% 0.20/0.48    inference(avatar_split_clause,[],[f1098,f925,f1101])).
% 0.20/0.48  fof(f925,plain,(
% 0.20/0.48    spl17_61 <=> r2_hidden(sK14(sK11,sK12,sK13),sK9)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl17_61])])).
% 0.20/0.48  fof(f1098,plain,(
% 0.20/0.48    m1_subset_1(sK14(sK11,sK12,sK13),sK9) | ~spl17_61),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f927,f73])).
% 0.20/0.48  fof(f73,plain,(
% 0.20/0.48    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.20/0.48  fof(f927,plain,(
% 0.20/0.48    r2_hidden(sK14(sK11,sK12,sK13),sK9) | ~spl17_61),
% 0.20/0.48    inference(avatar_component_clause,[],[f925])).
% 0.20/0.48  fof(f939,plain,(
% 0.20/0.48    spl17_63 | ~spl17_58),
% 0.20/0.48    inference(avatar_split_clause,[],[f908,f897,f936])).
% 0.20/0.48  fof(f897,plain,(
% 0.20/0.48    spl17_58 <=> sP0(sK11,sK12,sK13)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl17_58])])).
% 0.20/0.48  fof(f908,plain,(
% 0.20/0.48    r2_hidden(k4_tarski(sK14(sK11,sK12,sK13),sK13),sK12) | ~spl17_58),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f899,f80])).
% 0.20/0.48  fof(f899,plain,(
% 0.20/0.48    sP0(sK11,sK12,sK13) | ~spl17_58),
% 0.20/0.48    inference(avatar_component_clause,[],[f897])).
% 0.20/0.48  fof(f928,plain,(
% 0.20/0.48    spl17_61 | ~spl17_23 | ~spl17_58),
% 0.20/0.48    inference(avatar_split_clause,[],[f923,f897,f411,f925])).
% 0.20/0.48  fof(f923,plain,(
% 0.20/0.48    r2_hidden(sK14(sK11,sK12,sK13),sK9) | (~spl17_23 | ~spl17_58)),
% 0.20/0.48    inference(forward_demodulation,[],[f910,f413])).
% 0.20/0.48  fof(f413,plain,(
% 0.20/0.48    sK9 = k1_relat_1(sK12) | ~spl17_23),
% 0.20/0.48    inference(avatar_component_clause,[],[f411])).
% 0.20/0.48  fof(f910,plain,(
% 0.20/0.48    r2_hidden(sK14(sK11,sK12,sK13),k1_relat_1(sK12)) | ~spl17_58),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f899,f79])).
% 0.20/0.48  fof(f79,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (r2_hidden(sK14(X0,X1,X2),k1_relat_1(X1)) | ~sP0(X0,X1,X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f49])).
% 0.20/0.48  fof(f917,plain,(
% 0.20/0.48    spl17_59 | ~spl17_58),
% 0.20/0.48    inference(avatar_split_clause,[],[f912,f897,f914])).
% 0.20/0.48  fof(f912,plain,(
% 0.20/0.48    r2_hidden(sK14(sK11,sK12,sK13),sK11) | ~spl17_58),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f899,f81])).
% 0.20/0.48  fof(f81,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (r2_hidden(sK14(X0,X1,X2),X0) | ~sP0(X0,X1,X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f49])).
% 0.20/0.48  fof(f901,plain,(
% 0.20/0.48    spl17_58 | ~spl17_12 | ~spl17_50),
% 0.20/0.48    inference(avatar_split_clause,[],[f877,f805,f196,f897])).
% 0.20/0.48  fof(f877,plain,(
% 0.20/0.48    sP0(sK11,sK12,sK13) | (~spl17_12 | ~spl17_50)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f202,f807,f77])).
% 0.20/0.48  fof(f202,plain,(
% 0.20/0.48    ( ! [X0,X1] : (sP1(X0,sK12,X1)) ) | ~spl17_12),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f198,f83])).
% 0.20/0.48  fof(f853,plain,(
% 0.20/0.48    spl17_50 | ~spl17_1 | ~spl17_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f852,f118,f113,f805])).
% 0.20/0.48  fof(f113,plain,(
% 0.20/0.48    spl17_1 <=> r2_hidden(sK13,k7_relset_1(sK9,sK10,sK12,sK11))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl17_1])])).
% 0.20/0.48  fof(f118,plain,(
% 0.20/0.48    spl17_2 <=> m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl17_2])])).
% 0.20/0.48  fof(f852,plain,(
% 0.20/0.48    r2_hidden(sK13,k9_relat_1(sK12,sK11)) | (~spl17_1 | ~spl17_2)),
% 0.20/0.48    inference(subsumption_resolution,[],[f795,f120])).
% 0.20/0.48  fof(f120,plain,(
% 0.20/0.48    m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))) | ~spl17_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f118])).
% 0.20/0.48  fof(f795,plain,(
% 0.20/0.48    r2_hidden(sK13,k9_relat_1(sK12,sK11)) | ~m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10))) | ~spl17_1),
% 0.20/0.48    inference(superposition,[],[f115,f106])).
% 0.20/0.48  fof(f106,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,axiom,(
% 0.20/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.20/0.48  fof(f115,plain,(
% 0.20/0.48    r2_hidden(sK13,k7_relset_1(sK9,sK10,sK12,sK11)) | ~spl17_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f113])).
% 0.20/0.48  fof(f351,plain,(
% 0.20/0.48    spl17_16 | ~spl17_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f345,f118,f348])).
% 0.20/0.48  fof(f345,plain,(
% 0.20/0.48    k1_relat_1(sK12) = k1_relset_1(sK9,sK10,sK12) | ~spl17_2),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f120,f85])).
% 0.20/0.48  fof(f85,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.48  fof(f266,plain,(
% 0.20/0.48    spl17_15 | ~spl17_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f260,f118,f262])).
% 0.20/0.48  fof(f260,plain,(
% 0.20/0.48    sP6(sK9,sK12,sK10) | ~spl17_2),
% 0.20/0.48    inference(resolution,[],[f99,f120])).
% 0.20/0.48  fof(f99,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | sP6(X1,X2,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f36])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (sP6(X1,X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.20/0.48    inference(definition_folding,[],[f23,f35,f34])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.20/0.48    inference(ennf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).
% 0.20/0.48  fof(f246,plain,(
% 0.20/0.48    spl17_14 | ~spl17_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f240,f118,f242])).
% 0.20/0.48  fof(f240,plain,(
% 0.20/0.48    sP4(sK12,sK10,sK9) | ~spl17_2),
% 0.20/0.48    inference(resolution,[],[f93,f120])).
% 0.20/0.48  fof(f93,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP4(X2,X1,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f33])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((sP4(X2,X1,X0) & sP3(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(definition_folding,[],[f22,f32,f31,f30])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(flattening,[],[f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.48  fof(f234,plain,(
% 0.20/0.48    spl17_13 | ~spl17_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f228,f118,f230])).
% 0.20/0.48  fof(f228,plain,(
% 0.20/0.48    sP3(sK9,sK12,sK10) | ~spl17_2),
% 0.20/0.48    inference(resolution,[],[f92,f120])).
% 0.20/0.48  fof(f92,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP3(X0,X2,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f33])).
% 0.20/0.48  fof(f201,plain,(
% 0.20/0.48    spl17_12 | ~spl17_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f189,f118,f196])).
% 0.20/0.48  fof(f189,plain,(
% 0.20/0.48    v1_relat_1(sK12) | ~spl17_2),
% 0.20/0.48    inference(resolution,[],[f84,f120])).
% 0.20/0.48  fof(f84,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.48  fof(f200,plain,(
% 0.20/0.48    spl17_11),
% 0.20/0.48    inference(avatar_split_clause,[],[f188,f191])).
% 0.20/0.48  fof(f188,plain,(
% 0.20/0.48    v1_relat_1(k1_xboole_0)),
% 0.20/0.48    inference(resolution,[],[f84,f168])).
% 0.20/0.48  fof(f168,plain,(
% 0.20/0.48    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f72,f75])).
% 0.20/0.48  fof(f75,plain,(
% 0.20/0.48    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f43])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.48    inference(nnf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.48  fof(f131,plain,(
% 0.20/0.48    spl17_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f67,f128])).
% 0.20/0.48  fof(f67,plain,(
% 0.20/0.48    v1_funct_1(sK12)),
% 0.20/0.48    inference(cnf_transformation,[],[f42])).
% 0.20/0.48  fof(f126,plain,(
% 0.20/0.48    spl17_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f68,f123])).
% 0.20/0.48  fof(f68,plain,(
% 0.20/0.48    v1_funct_2(sK12,sK9,sK10)),
% 0.20/0.48    inference(cnf_transformation,[],[f42])).
% 0.20/0.48  fof(f121,plain,(
% 0.20/0.48    spl17_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f69,f118])).
% 0.20/0.48  fof(f69,plain,(
% 0.20/0.48    m1_subset_1(sK12,k1_zfmisc_1(k2_zfmisc_1(sK9,sK10)))),
% 0.20/0.48    inference(cnf_transformation,[],[f42])).
% 0.20/0.48  fof(f116,plain,(
% 0.20/0.48    spl17_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f70,f113])).
% 0.20/0.48  fof(f70,plain,(
% 0.20/0.48    r2_hidden(sK13,k7_relset_1(sK9,sK10,sK12,sK11))),
% 0.20/0.48    inference(cnf_transformation,[],[f42])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (27462)------------------------------
% 0.20/0.48  % (27462)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (27462)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (27462)Memory used [KB]: 12281
% 0.20/0.48  % (27462)Time elapsed: 0.084 s
% 0.20/0.48  % (27462)------------------------------
% 0.20/0.48  % (27462)------------------------------
% 0.20/0.48  % (27445)Success in time 0.131 s
%------------------------------------------------------------------------------
