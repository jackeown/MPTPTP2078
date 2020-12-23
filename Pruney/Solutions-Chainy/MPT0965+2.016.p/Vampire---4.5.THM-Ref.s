%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 193 expanded)
%              Number of leaves         :   34 (  81 expanded)
%              Depth                    :    9
%              Number of atoms          :  386 ( 684 expanded)
%              Number of equality atoms :   77 ( 121 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f279,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f84,f89,f94,f99,f104,f109,f118,f124,f161,f181,f187,f201,f209,f226,f238,f264,f278])).

fof(f278,plain,
    ( sK6 != k1_relset_1(sK6,sK7,sK9)
    | k1_relset_1(sK6,sK7,sK9) != k1_relat_1(sK9)
    | r2_hidden(sK8,k1_relat_1(sK9))
    | ~ r2_hidden(sK8,sK6) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f264,plain,
    ( spl12_19
    | spl12_2
    | ~ spl12_5
    | ~ spl12_10 ),
    inference(avatar_split_clause,[],[f255,f157,f101,f86,f261])).

fof(f261,plain,
    ( spl12_19
  <=> sK6 = k1_relset_1(sK6,sK7,sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_19])])).

fof(f86,plain,
    ( spl12_2
  <=> k1_xboole_0 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f101,plain,
    ( spl12_5
  <=> v1_funct_2(sK9,sK6,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_5])])).

fof(f157,plain,
    ( spl12_10
  <=> sP4(sK6,sK9,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).

fof(f255,plain,
    ( sK6 = k1_relset_1(sK6,sK7,sK9)
    | spl12_2
    | ~ spl12_5
    | ~ spl12_10 ),
    inference(unit_resulting_resolution,[],[f110,f159,f103,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | sP3(X0,X2)
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP3(X0,X2)
      | ~ sP4(X0,X1,X2) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP3(X0,X1)
      | ~ sP4(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP3(X0,X1)
      | ~ sP4(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f103,plain,
    ( v1_funct_2(sK9,sK6,sK7)
    | ~ spl12_5 ),
    inference(avatar_component_clause,[],[f101])).

fof(f159,plain,
    ( sP4(sK6,sK9,sK7)
    | ~ spl12_10 ),
    inference(avatar_component_clause,[],[f157])).

fof(f110,plain,
    ( ! [X0] : ~ sP3(X0,sK7)
    | spl12_2 ),
    inference(unit_resulting_resolution,[],[f88,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ sP3(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP3(X0,X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP3(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f88,plain,
    ( k1_xboole_0 != sK7
    | spl12_2 ),
    inference(avatar_component_clause,[],[f86])).

fof(f238,plain,
    ( ~ spl12_17
    | spl12_16 ),
    inference(avatar_split_clause,[],[f232,f218,f234])).

fof(f234,plain,
    ( spl12_17
  <=> r2_hidden(sK8,k1_relat_1(sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_17])])).

fof(f218,plain,
    ( spl12_16
  <=> sP0(k1_funct_1(sK9,sK8),sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_16])])).

fof(f232,plain,
    ( ~ r2_hidden(sK8,k1_relat_1(sK9))
    | spl12_16 ),
    inference(resolution,[],[f220,f75])).

fof(f75,plain,(
    ! [X2,X1] :
      ( sP0(k1_funct_1(X1,X2),X1)
      | ~ r2_hidden(X2,k1_relat_1(X1)) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1)
      | k1_funct_1(X1,X2) != X0
      | ~ r2_hidden(X2,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ! [X2] :
            ( k1_funct_1(X1,X2) != X0
            | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
      & ( ( k1_funct_1(X1,sK11(X0,X1)) = X0
          & r2_hidden(sK11(X0,X1),k1_relat_1(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f37,f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( k1_funct_1(X1,X3) = X0
          & r2_hidden(X3,k1_relat_1(X1)) )
     => ( k1_funct_1(X1,sK11(X0,X1)) = X0
        & r2_hidden(sK11(X0,X1),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ! [X2] :
            ( k1_funct_1(X1,X2) != X0
            | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
      & ( ? [X3] :
            ( k1_funct_1(X1,X3) = X0
            & r2_hidden(X3,k1_relat_1(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X2,X0] :
      ( ( sP0(X2,X0)
        | ! [X3] :
            ( k1_funct_1(X0,X3) != X2
            | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
      & ( ? [X3] :
            ( k1_funct_1(X0,X3) = X2
            & r2_hidden(X3,k1_relat_1(X0)) )
        | ~ sP0(X2,X0) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X2,X0] :
      ( sP0(X2,X0)
    <=> ? [X3] :
          ( k1_funct_1(X0,X3) = X2
          & r2_hidden(X3,k1_relat_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f220,plain,
    ( ~ sP0(k1_funct_1(sK9,sK8),sK9)
    | spl12_16 ),
    inference(avatar_component_clause,[],[f218])).

fof(f226,plain,
    ( ~ spl12_16
    | ~ spl12_8
    | spl12_15 ),
    inference(avatar_split_clause,[],[f225,f206,f121,f218])).

% (10415)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f121,plain,
    ( spl12_8
  <=> sP2(sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).

fof(f206,plain,
    ( spl12_15
  <=> r2_hidden(k1_funct_1(sK9,sK8),k2_relat_1(sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_15])])).

fof(f225,plain,
    ( ~ sP0(k1_funct_1(sK9,sK8),sK9)
    | ~ spl12_8
    | spl12_15 ),
    inference(subsumption_resolution,[],[f215,f123])).

fof(f123,plain,
    ( sP2(sK9)
    | ~ spl12_8 ),
    inference(avatar_component_clause,[],[f121])).

fof(f215,plain,
    ( ~ sP0(k1_funct_1(sK9,sK8),sK9)
    | ~ sP2(sK9)
    | spl12_15 ),
    inference(resolution,[],[f208,f139])).

fof(f139,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_relat_1(X1))
      | ~ sP0(X0,X1)
      | ~ sP2(X1) ) ),
    inference(resolution,[],[f54,f74])).

fof(f74,plain,(
    ! [X0] :
      ( sP1(X0,k2_relat_1(X0))
      | ~ sP2(X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | k2_relat_1(X0) != X1
      | ~ sP2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ~ sP1(X0,X1) )
          & ( sP1(X0,X1)
            | k2_relat_1(X0) != X1 ) )
      | ~ sP2(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> sP1(X0,X1) )
      | ~ sP2(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( ~ sP1(X0,X1)
      | ~ sP0(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ( ( ~ sP0(sK10(X0,X1),X0)
            | ~ r2_hidden(sK10(X0,X1),X1) )
          & ( sP0(sK10(X0,X1),X0)
            | r2_hidden(sK10(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ sP0(X3,X0) )
            & ( sP0(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f33,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ sP0(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( sP0(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ sP0(sK10(X0,X1),X0)
          | ~ r2_hidden(sK10(X0,X1),X1) )
        & ( sP0(sK10(X0,X1),X0)
          | r2_hidden(sK10(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ? [X2] :
            ( ( ~ sP0(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( sP0(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ sP0(X3,X0) )
            & ( sP0(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ? [X2] :
            ( ( ~ sP0(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( sP0(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ sP0(X2,X0) )
            & ( sP0(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> sP0(X2,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f208,plain,
    ( ~ r2_hidden(k1_funct_1(sK9,sK8),k2_relat_1(sK9))
    | spl12_15 ),
    inference(avatar_component_clause,[],[f206])).

fof(f209,plain,
    ( ~ spl12_15
    | spl12_1
    | ~ spl12_14 ),
    inference(avatar_split_clause,[],[f202,f198,f81,f206])).

fof(f81,plain,
    ( spl12_1
  <=> r2_hidden(k1_funct_1(sK9,sK8),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f198,plain,
    ( spl12_14
  <=> m1_subset_1(k2_relat_1(sK9),k1_zfmisc_1(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_14])])).

fof(f202,plain,
    ( ~ r2_hidden(k1_funct_1(sK9,sK8),k2_relat_1(sK9))
    | spl12_1
    | ~ spl12_14 ),
    inference(unit_resulting_resolution,[],[f83,f200,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f200,plain,
    ( m1_subset_1(k2_relat_1(sK9),k1_zfmisc_1(sK7))
    | ~ spl12_14 ),
    inference(avatar_component_clause,[],[f198])).

fof(f83,plain,
    ( ~ r2_hidden(k1_funct_1(sK9,sK8),sK7)
    | spl12_1 ),
    inference(avatar_component_clause,[],[f81])).

fof(f201,plain,
    ( spl12_14
    | ~ spl12_4
    | ~ spl12_13 ),
    inference(avatar_split_clause,[],[f196,f184,f96,f198])).

fof(f96,plain,
    ( spl12_4
  <=> m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).

fof(f184,plain,
    ( spl12_13
  <=> k2_relat_1(sK9) = k2_relset_1(sK6,sK7,sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_13])])).

fof(f196,plain,
    ( m1_subset_1(k2_relat_1(sK9),k1_zfmisc_1(sK7))
    | ~ spl12_4
    | ~ spl12_13 ),
    inference(forward_demodulation,[],[f188,f186])).

fof(f186,plain,
    ( k2_relat_1(sK9) = k2_relset_1(sK6,sK7,sK9)
    | ~ spl12_13 ),
    inference(avatar_component_clause,[],[f184])).

fof(f188,plain,
    ( m1_subset_1(k2_relset_1(sK6,sK7,sK9),k1_zfmisc_1(sK7))
    | ~ spl12_4 ),
    inference(unit_resulting_resolution,[],[f98,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f98,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    | ~ spl12_4 ),
    inference(avatar_component_clause,[],[f96])).

fof(f187,plain,
    ( spl12_13
    | ~ spl12_4 ),
    inference(avatar_split_clause,[],[f182,f96,f184])).

fof(f182,plain,
    ( k2_relat_1(sK9) = k2_relset_1(sK6,sK7,sK9)
    | ~ spl12_4 ),
    inference(unit_resulting_resolution,[],[f98,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f181,plain,
    ( spl12_12
    | ~ spl12_4 ),
    inference(avatar_split_clause,[],[f176,f96,f178])).

fof(f178,plain,
    ( spl12_12
  <=> k1_relset_1(sK6,sK7,sK9) = k1_relat_1(sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_12])])).

fof(f176,plain,
    ( k1_relset_1(sK6,sK7,sK9) = k1_relat_1(sK9)
    | ~ spl12_4 ),
    inference(unit_resulting_resolution,[],[f98,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f161,plain,
    ( spl12_10
    | ~ spl12_4 ),
    inference(avatar_split_clause,[],[f155,f96,f157])).

fof(f155,plain,
    ( sP4(sK6,sK9,sK7)
    | ~ spl12_4 ),
    inference(resolution,[],[f72,f98])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP4(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( sP5(X2,X1,X0)
        & sP4(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f20,f27,f26,f25])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP5(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f124,plain,
    ( spl12_8
    | ~ spl12_6
    | ~ spl12_7 ),
    inference(avatar_split_clause,[],[f119,f114,f106,f121])).

% (10430)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% (10423)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% (10422)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
fof(f106,plain,
    ( spl12_6
  <=> v1_funct_1(sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).

fof(f114,plain,
    ( spl12_7
  <=> v1_relat_1(sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_7])])).

fof(f119,plain,
    ( sP2(sK9)
    | ~ spl12_6
    | ~ spl12_7 ),
    inference(unit_resulting_resolution,[],[f108,f116,f60])).

fof(f60,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f13,f23,f22,f21])).

% (10431)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% (10417)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% (10431)Refutation not found, incomplete strategy% (10431)------------------------------
% (10431)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f116,plain,
    ( v1_relat_1(sK9)
    | ~ spl12_7 ),
    inference(avatar_component_clause,[],[f114])).

fof(f108,plain,
    ( v1_funct_1(sK9)
    | ~ spl12_6 ),
    inference(avatar_component_clause,[],[f106])).

fof(f118,plain,
    ( spl12_7
    | ~ spl12_4 ),
    inference(avatar_split_clause,[],[f112,f96,f114])).

fof(f112,plain,
    ( v1_relat_1(sK9)
    | ~ spl12_4 ),
    inference(resolution,[],[f62,f98])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f109,plain,(
    spl12_6 ),
    inference(avatar_split_clause,[],[f45,f106])).

fof(f45,plain,(
    v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ~ r2_hidden(k1_funct_1(sK9,sK8),sK7)
    & k1_xboole_0 != sK7
    & r2_hidden(sK8,sK6)
    & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    & v1_funct_2(sK9,sK6,sK7)
    & v1_funct_1(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f11,f29])).

fof(f29,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r2_hidden(k1_funct_1(X3,X2),X1)
        & k1_xboole_0 != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ~ r2_hidden(k1_funct_1(sK9,sK8),sK7)
      & k1_xboole_0 != sK7
      & r2_hidden(sK8,sK6)
      & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
      & v1_funct_2(sK9,sK6,sK7)
      & v1_funct_1(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_hidden(k1_funct_1(X3,X2),X1)
      & k1_xboole_0 != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_hidden(k1_funct_1(X3,X2),X1)
      & k1_xboole_0 != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => ( r2_hidden(k1_funct_1(X3,X2),X1)
            | k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

fof(f104,plain,(
    spl12_5 ),
    inference(avatar_split_clause,[],[f46,f101])).

fof(f46,plain,(
    v1_funct_2(sK9,sK6,sK7) ),
    inference(cnf_transformation,[],[f30])).

fof(f99,plain,(
    spl12_4 ),
    inference(avatar_split_clause,[],[f47,f96])).

fof(f47,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
    inference(cnf_transformation,[],[f30])).

fof(f94,plain,(
    spl12_3 ),
    inference(avatar_split_clause,[],[f48,f91])).

fof(f91,plain,
    ( spl12_3
  <=> r2_hidden(sK8,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f48,plain,(
    r2_hidden(sK8,sK6) ),
    inference(cnf_transformation,[],[f30])).

fof(f89,plain,(
    ~ spl12_2 ),
    inference(avatar_split_clause,[],[f49,f86])).

fof(f49,plain,(
    k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f30])).

fof(f84,plain,(
    ~ spl12_1 ),
    inference(avatar_split_clause,[],[f50,f81])).

fof(f50,plain,(
    ~ r2_hidden(k1_funct_1(sK9,sK8),sK7) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:28:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (10419)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.47  % (10424)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.47  % (10427)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.48  % (10427)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f279,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f84,f89,f94,f99,f104,f109,f118,f124,f161,f181,f187,f201,f209,f226,f238,f264,f278])).
% 0.21/0.48  fof(f278,plain,(
% 0.21/0.48    sK6 != k1_relset_1(sK6,sK7,sK9) | k1_relset_1(sK6,sK7,sK9) != k1_relat_1(sK9) | r2_hidden(sK8,k1_relat_1(sK9)) | ~r2_hidden(sK8,sK6)),
% 0.21/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.48  fof(f264,plain,(
% 0.21/0.48    spl12_19 | spl12_2 | ~spl12_5 | ~spl12_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f255,f157,f101,f86,f261])).
% 0.21/0.48  fof(f261,plain,(
% 0.21/0.48    spl12_19 <=> sK6 = k1_relset_1(sK6,sK7,sK9)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl12_19])])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    spl12_2 <=> k1_xboole_0 = sK7),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    spl12_5 <=> v1_funct_2(sK9,sK6,sK7)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl12_5])])).
% 0.21/0.48  fof(f157,plain,(
% 0.21/0.48    spl12_10 <=> sP4(sK6,sK9,sK7)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).
% 0.21/0.48  fof(f255,plain,(
% 0.21/0.48    sK6 = k1_relset_1(sK6,sK7,sK9) | (spl12_2 | ~spl12_5 | ~spl12_10)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f110,f159,f103,f68])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | sP3(X0,X2) | ~sP4(X0,X1,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP3(X0,X2) | ~sP4(X0,X1,X2))),
% 0.21/0.48    inference(rectify,[],[f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP3(X0,X1) | ~sP4(X0,X2,X1))),
% 0.21/0.48    inference(nnf_transformation,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP3(X0,X1) | ~sP4(X0,X2,X1))),
% 0.21/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    v1_funct_2(sK9,sK6,sK7) | ~spl12_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f101])).
% 0.21/0.48  fof(f159,plain,(
% 0.21/0.48    sP4(sK6,sK9,sK7) | ~spl12_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f157])).
% 0.21/0.48  fof(f110,plain,(
% 0.21/0.48    ( ! [X0] : (~sP3(X0,sK7)) ) | spl12_2),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f88,f70])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~sP3(X0,X1) | k1_xboole_0 = X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP3(X0,X1))),
% 0.21/0.48    inference(nnf_transformation,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP3(X0,X1))),
% 0.21/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    k1_xboole_0 != sK7 | spl12_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f86])).
% 0.21/0.48  fof(f238,plain,(
% 0.21/0.48    ~spl12_17 | spl12_16),
% 0.21/0.48    inference(avatar_split_clause,[],[f232,f218,f234])).
% 0.21/0.48  fof(f234,plain,(
% 0.21/0.48    spl12_17 <=> r2_hidden(sK8,k1_relat_1(sK9))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl12_17])])).
% 0.21/0.48  fof(f218,plain,(
% 0.21/0.48    spl12_16 <=> sP0(k1_funct_1(sK9,sK8),sK9)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl12_16])])).
% 0.21/0.48  fof(f232,plain,(
% 0.21/0.48    ~r2_hidden(sK8,k1_relat_1(sK9)) | spl12_16),
% 0.21/0.48    inference(resolution,[],[f220,f75])).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    ( ! [X2,X1] : (sP0(k1_funct_1(X1,X2),X1) | ~r2_hidden(X2,k1_relat_1(X1))) )),
% 0.21/0.48    inference(equality_resolution,[],[f59])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (sP0(X0,X1) | k1_funct_1(X1,X2) != X0 | ~r2_hidden(X2,k1_relat_1(X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ! [X0,X1] : ((sP0(X0,X1) | ! [X2] : (k1_funct_1(X1,X2) != X0 | ~r2_hidden(X2,k1_relat_1(X1)))) & ((k1_funct_1(X1,sK11(X0,X1)) = X0 & r2_hidden(sK11(X0,X1),k1_relat_1(X1))) | ~sP0(X0,X1)))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f37,f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ! [X1,X0] : (? [X3] : (k1_funct_1(X1,X3) = X0 & r2_hidden(X3,k1_relat_1(X1))) => (k1_funct_1(X1,sK11(X0,X1)) = X0 & r2_hidden(sK11(X0,X1),k1_relat_1(X1))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ! [X0,X1] : ((sP0(X0,X1) | ! [X2] : (k1_funct_1(X1,X2) != X0 | ~r2_hidden(X2,k1_relat_1(X1)))) & (? [X3] : (k1_funct_1(X1,X3) = X0 & r2_hidden(X3,k1_relat_1(X1))) | ~sP0(X0,X1)))),
% 0.21/0.48    inference(rectify,[],[f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ! [X2,X0] : ((sP0(X2,X0) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X2,X0)))),
% 0.21/0.48    inference(nnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X2,X0] : (sP0(X2,X0) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))),
% 0.21/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.48  fof(f220,plain,(
% 0.21/0.48    ~sP0(k1_funct_1(sK9,sK8),sK9) | spl12_16),
% 0.21/0.48    inference(avatar_component_clause,[],[f218])).
% 0.21/0.48  fof(f226,plain,(
% 0.21/0.48    ~spl12_16 | ~spl12_8 | spl12_15),
% 0.21/0.48    inference(avatar_split_clause,[],[f225,f206,f121,f218])).
% 0.21/0.48  % (10415)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.48  fof(f121,plain,(
% 0.21/0.48    spl12_8 <=> sP2(sK9)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).
% 0.21/0.48  fof(f206,plain,(
% 0.21/0.48    spl12_15 <=> r2_hidden(k1_funct_1(sK9,sK8),k2_relat_1(sK9))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl12_15])])).
% 0.21/0.48  fof(f225,plain,(
% 0.21/0.48    ~sP0(k1_funct_1(sK9,sK8),sK9) | (~spl12_8 | spl12_15)),
% 0.21/0.48    inference(subsumption_resolution,[],[f215,f123])).
% 0.21/0.48  fof(f123,plain,(
% 0.21/0.48    sP2(sK9) | ~spl12_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f121])).
% 0.21/0.48  fof(f215,plain,(
% 0.21/0.48    ~sP0(k1_funct_1(sK9,sK8),sK9) | ~sP2(sK9) | spl12_15),
% 0.21/0.48    inference(resolution,[],[f208,f139])).
% 0.21/0.48  fof(f139,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r2_hidden(X0,k2_relat_1(X1)) | ~sP0(X0,X1) | ~sP2(X1)) )),
% 0.21/0.48    inference(resolution,[],[f54,f74])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    ( ! [X0] : (sP1(X0,k2_relat_1(X0)) | ~sP2(X0)) )),
% 0.21/0.48    inference(equality_resolution,[],[f51])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ( ! [X0,X1] : (sP1(X0,X1) | k2_relat_1(X0) != X1 | ~sP2(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ~sP1(X0,X1)) & (sP1(X0,X1) | k2_relat_1(X0) != X1)) | ~sP2(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> sP1(X0,X1)) | ~sP2(X0))),
% 0.21/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ( ! [X0,X3,X1] : (~sP1(X0,X1) | ~sP0(X3,X0) | r2_hidden(X3,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ! [X0,X1] : ((sP1(X0,X1) | ((~sP0(sK10(X0,X1),X0) | ~r2_hidden(sK10(X0,X1),X1)) & (sP0(sK10(X0,X1),X0) | r2_hidden(sK10(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~sP0(X3,X0)) & (sP0(X3,X0) | ~r2_hidden(X3,X1))) | ~sP1(X0,X1)))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f33,f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ! [X1,X0] : (? [X2] : ((~sP0(X2,X0) | ~r2_hidden(X2,X1)) & (sP0(X2,X0) | r2_hidden(X2,X1))) => ((~sP0(sK10(X0,X1),X0) | ~r2_hidden(sK10(X0,X1),X1)) & (sP0(sK10(X0,X1),X0) | r2_hidden(sK10(X0,X1),X1))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ! [X0,X1] : ((sP1(X0,X1) | ? [X2] : ((~sP0(X2,X0) | ~r2_hidden(X2,X1)) & (sP0(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~sP0(X3,X0)) & (sP0(X3,X0) | ~r2_hidden(X3,X1))) | ~sP1(X0,X1)))),
% 0.21/0.48    inference(rectify,[],[f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ! [X0,X1] : ((sP1(X0,X1) | ? [X2] : ((~sP0(X2,X0) | ~r2_hidden(X2,X1)) & (sP0(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~sP0(X2,X0)) & (sP0(X2,X0) | ~r2_hidden(X2,X1))) | ~sP1(X0,X1)))),
% 0.21/0.48    inference(nnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0,X1] : (sP1(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> sP0(X2,X0)))),
% 0.21/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.48  fof(f208,plain,(
% 0.21/0.48    ~r2_hidden(k1_funct_1(sK9,sK8),k2_relat_1(sK9)) | spl12_15),
% 0.21/0.48    inference(avatar_component_clause,[],[f206])).
% 0.21/0.48  fof(f209,plain,(
% 0.21/0.48    ~spl12_15 | spl12_1 | ~spl12_14),
% 0.21/0.48    inference(avatar_split_clause,[],[f202,f198,f81,f206])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    spl12_1 <=> r2_hidden(k1_funct_1(sK9,sK8),sK7)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).
% 0.21/0.48  fof(f198,plain,(
% 0.21/0.48    spl12_14 <=> m1_subset_1(k2_relat_1(sK9),k1_zfmisc_1(sK7))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl12_14])])).
% 0.21/0.48  fof(f202,plain,(
% 0.21/0.48    ~r2_hidden(k1_funct_1(sK9,sK8),k2_relat_1(sK9)) | (spl12_1 | ~spl12_14)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f83,f200,f61])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.48  fof(f200,plain,(
% 0.21/0.48    m1_subset_1(k2_relat_1(sK9),k1_zfmisc_1(sK7)) | ~spl12_14),
% 0.21/0.48    inference(avatar_component_clause,[],[f198])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    ~r2_hidden(k1_funct_1(sK9,sK8),sK7) | spl12_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f81])).
% 0.21/0.48  fof(f201,plain,(
% 0.21/0.48    spl12_14 | ~spl12_4 | ~spl12_13),
% 0.21/0.48    inference(avatar_split_clause,[],[f196,f184,f96,f198])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    spl12_4 <=> m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).
% 0.21/0.48  fof(f184,plain,(
% 0.21/0.48    spl12_13 <=> k2_relat_1(sK9) = k2_relset_1(sK6,sK7,sK9)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl12_13])])).
% 0.21/0.48  fof(f196,plain,(
% 0.21/0.48    m1_subset_1(k2_relat_1(sK9),k1_zfmisc_1(sK7)) | (~spl12_4 | ~spl12_13)),
% 0.21/0.48    inference(forward_demodulation,[],[f188,f186])).
% 0.21/0.48  fof(f186,plain,(
% 0.21/0.48    k2_relat_1(sK9) = k2_relset_1(sK6,sK7,sK9) | ~spl12_13),
% 0.21/0.48    inference(avatar_component_clause,[],[f184])).
% 0.21/0.48  fof(f188,plain,(
% 0.21/0.48    m1_subset_1(k2_relset_1(sK6,sK7,sK9),k1_zfmisc_1(sK7)) | ~spl12_4),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f98,f65])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) | ~spl12_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f96])).
% 0.21/0.48  fof(f187,plain,(
% 0.21/0.48    spl12_13 | ~spl12_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f182,f96,f184])).
% 0.21/0.48  fof(f182,plain,(
% 0.21/0.48    k2_relat_1(sK9) = k2_relset_1(sK6,sK7,sK9) | ~spl12_4),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f98,f64])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.48  fof(f181,plain,(
% 0.21/0.48    spl12_12 | ~spl12_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f176,f96,f178])).
% 0.21/0.48  fof(f178,plain,(
% 0.21/0.48    spl12_12 <=> k1_relset_1(sK6,sK7,sK9) = k1_relat_1(sK9)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl12_12])])).
% 0.21/0.48  fof(f176,plain,(
% 0.21/0.48    k1_relset_1(sK6,sK7,sK9) = k1_relat_1(sK9) | ~spl12_4),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f98,f63])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.48  fof(f161,plain,(
% 0.21/0.48    spl12_10 | ~spl12_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f155,f96,f157])).
% 0.21/0.48  fof(f155,plain,(
% 0.21/0.48    sP4(sK6,sK9,sK7) | ~spl12_4),
% 0.21/0.48    inference(resolution,[],[f72,f98])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP4(X0,X2,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((sP5(X2,X1,X0) & sP4(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(definition_folding,[],[f20,f27,f26,f25])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP5(X2,X1,X0))),
% 0.21/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(flattening,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.48  fof(f124,plain,(
% 0.21/0.48    spl12_8 | ~spl12_6 | ~spl12_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f119,f114,f106,f121])).
% 0.21/0.48  % (10430)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.48  % (10423)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (10422)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    spl12_6 <=> v1_funct_1(sK9)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    spl12_7 <=> v1_relat_1(sK9)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl12_7])])).
% 0.21/0.48  fof(f119,plain,(
% 0.21/0.48    sP2(sK9) | (~spl12_6 | ~spl12_7)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f108,f116,f60])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    ( ! [X0] : (sP2(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0] : (sP2(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(definition_folding,[],[f13,f23,f22,f21])).
% 0.21/0.48  % (10431)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (10417)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (10431)Refutation not found, incomplete strategy% (10431)------------------------------
% 0.21/0.49  % (10431)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 0.21/0.49  fof(f116,plain,(
% 0.21/0.49    v1_relat_1(sK9) | ~spl12_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f114])).
% 0.21/0.49  fof(f108,plain,(
% 0.21/0.49    v1_funct_1(sK9) | ~spl12_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f106])).
% 0.21/0.49  fof(f118,plain,(
% 0.21/0.49    spl12_7 | ~spl12_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f112,f96,f114])).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    v1_relat_1(sK9) | ~spl12_4),
% 0.21/0.49    inference(resolution,[],[f62,f98])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    spl12_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f45,f106])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    v1_funct_1(sK9)),
% 0.21/0.49    inference(cnf_transformation,[],[f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ~r2_hidden(k1_funct_1(sK9,sK8),sK7) & k1_xboole_0 != sK7 & r2_hidden(sK8,sK6) & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) & v1_funct_2(sK9,sK6,sK7) & v1_funct_1(sK9)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f11,f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : (~r2_hidden(k1_funct_1(X3,X2),X1) & k1_xboole_0 != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_hidden(k1_funct_1(sK9,sK8),sK7) & k1_xboole_0 != sK7 & r2_hidden(sK8,sK6) & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) & v1_funct_2(sK9,sK6,sK7) & v1_funct_1(sK9))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : (~r2_hidden(k1_funct_1(X3,X2),X1) & k1_xboole_0 != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.21/0.49    inference(flattening,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : (((~r2_hidden(k1_funct_1(X3,X2),X1) & k1_xboole_0 != X1) & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 0.21/0.49    inference(negated_conjecture,[],[f8])).
% 0.21/0.49  fof(f8,conjecture,(
% 0.21/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    spl12_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f46,f101])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    v1_funct_2(sK9,sK6,sK7)),
% 0.21/0.49    inference(cnf_transformation,[],[f30])).
% 0.21/0.49  fof(f99,plain,(
% 0.21/0.49    spl12_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f47,f96])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))),
% 0.21/0.49    inference(cnf_transformation,[],[f30])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    spl12_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f48,f91])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    spl12_3 <=> r2_hidden(sK8,sK6)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    r2_hidden(sK8,sK6)),
% 0.21/0.49    inference(cnf_transformation,[],[f30])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    ~spl12_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f49,f86])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    k1_xboole_0 != sK7),
% 0.21/0.49    inference(cnf_transformation,[],[f30])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    ~spl12_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f50,f81])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ~r2_hidden(k1_funct_1(sK9,sK8),sK7)),
% 0.21/0.49    inference(cnf_transformation,[],[f30])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (10427)------------------------------
% 0.21/0.49  % (10427)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (10427)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (10427)Memory used [KB]: 10746
% 0.21/0.49  % (10427)Time elapsed: 0.074 s
% 0.21/0.49  % (10427)------------------------------
% 0.21/0.49  % (10427)------------------------------
% 0.21/0.49  % (10425)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (10414)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (10412)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (10410)Success in time 0.13 s
%------------------------------------------------------------------------------
