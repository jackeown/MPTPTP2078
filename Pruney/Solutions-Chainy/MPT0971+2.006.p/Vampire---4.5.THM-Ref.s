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
% DateTime   : Thu Dec  3 13:01:00 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 177 expanded)
%              Number of leaves         :   27 (  70 expanded)
%              Depth                    :   10
%              Number of atoms          :  368 ( 604 expanded)
%              Number of equality atoms :   42 (  77 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f245,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f79,f89,f97,f104,f131,f155,f176,f193,f204,f209,f237,f244])).

fof(f244,plain,
    ( ~ spl11_5
    | ~ spl11_10
    | ~ spl11_14
    | spl11_17 ),
    inference(avatar_contradiction_clause,[],[f243])).

fof(f243,plain,
    ( $false
    | ~ spl11_5
    | ~ spl11_10
    | ~ spl11_14
    | spl11_17 ),
    inference(subsumption_resolution,[],[f242,f203])).

fof(f203,plain,
    ( r2_hidden(sK10(sK7,sK8),k1_relat_1(sK8))
    | ~ spl11_14 ),
    inference(avatar_component_clause,[],[f201])).

fof(f201,plain,
    ( spl11_14
  <=> r2_hidden(sK10(sK7,sK8),k1_relat_1(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).

fof(f242,plain,
    ( ~ r2_hidden(sK10(sK7,sK8),k1_relat_1(sK8))
    | ~ spl11_5
    | ~ spl11_10
    | spl11_17 ),
    inference(forward_demodulation,[],[f239,f154])).

fof(f154,plain,
    ( sK8 = k7_relat_1(sK8,sK5)
    | ~ spl11_10 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl11_10
  <=> sK8 = k7_relat_1(sK8,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f239,plain,
    ( ~ r2_hidden(sK10(sK7,sK8),k1_relat_1(k7_relat_1(sK8,sK5)))
    | ~ spl11_5
    | spl11_17 ),
    inference(unit_resulting_resolution,[],[f98,f238,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(k7_relat_1(X2,X0)))
      | sP3(X2,X1,X0)
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X1,k1_relat_1(k7_relat_1(X2,X0)))
          | ~ sP3(X2,X1,X0) )
        & ( sP3(X2,X1,X0)
          | ~ r2_hidden(X1,k1_relat_1(k7_relat_1(X2,X0))) ) )
      | ~ sP4(X0,X1,X2) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X1,X0,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ sP3(X2,X0,X1) )
        & ( sP3(X2,X0,X1)
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ sP4(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X1,X0,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> sP3(X2,X0,X1) )
      | ~ sP4(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f238,plain,
    ( ! [X0] : ~ sP3(X0,sK10(sK7,sK8),sK5)
    | spl11_17 ),
    inference(unit_resulting_resolution,[],[f235,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(X0,X1,X2)
      | r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ~ r2_hidden(X1,k1_relat_1(X0))
        | ~ r2_hidden(X1,X2) )
      & ( ( r2_hidden(X1,k1_relat_1(X0))
          & r2_hidden(X1,X2) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ( sP3(X2,X0,X1)
        | ~ r2_hidden(X0,k1_relat_1(X2))
        | ~ r2_hidden(X0,X1) )
      & ( ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) )
        | ~ sP3(X2,X0,X1) ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ( sP3(X2,X0,X1)
        | ~ r2_hidden(X0,k1_relat_1(X2))
        | ~ r2_hidden(X0,X1) )
      & ( ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) )
        | ~ sP3(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( sP3(X2,X0,X1)
    <=> ( r2_hidden(X0,k1_relat_1(X2))
        & r2_hidden(X0,X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f235,plain,
    ( ~ r2_hidden(sK10(sK7,sK8),sK5)
    | spl11_17 ),
    inference(avatar_component_clause,[],[f233])).

fof(f233,plain,
    ( spl11_17
  <=> r2_hidden(sK10(sK7,sK8),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_17])])).

fof(f98,plain,
    ( ! [X0,X1] : sP4(X0,X1,sK8)
    | ~ spl11_5 ),
    inference(unit_resulting_resolution,[],[f95,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( sP4(X1,X0,X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( sP4(X1,X0,X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_folding,[],[f15,f24,f23])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

fof(f95,plain,
    ( v1_relat_1(sK8)
    | ~ spl11_5 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl11_5
  <=> v1_relat_1(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f237,plain,
    ( ~ spl11_17
    | ~ spl11_15 ),
    inference(avatar_split_clause,[],[f231,f206,f233])).

fof(f206,plain,
    ( spl11_15
  <=> sK7 = k1_funct_1(sK8,sK10(sK7,sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_15])])).

fof(f231,plain,
    ( ~ r2_hidden(sK10(sK7,sK8),sK5)
    | ~ spl11_15 ),
    inference(trivial_inequality_removal,[],[f229])).

fof(f229,plain,
    ( sK7 != sK7
    | ~ r2_hidden(sK10(sK7,sK8),sK5)
    | ~ spl11_15 ),
    inference(superposition,[],[f46,f208])).

fof(f208,plain,
    ( sK7 = k1_funct_1(sK8,sK10(sK7,sK8))
    | ~ spl11_15 ),
    inference(avatar_component_clause,[],[f206])).

fof(f46,plain,(
    ! [X4] :
      ( sK7 != k1_funct_1(sK8,X4)
      | ~ r2_hidden(X4,sK5) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ! [X4] :
        ( sK7 != k1_funct_1(sK8,X4)
        | ~ r2_hidden(X4,sK5) )
    & r2_hidden(sK7,k2_relset_1(sK5,sK6,sK8))
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    & v1_funct_2(sK8,sK5,sK6)
    & v1_funct_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f10,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4] :
            ( k1_funct_1(X3,X4) != X2
            | ~ r2_hidden(X4,X0) )
        & r2_hidden(X2,k2_relset_1(X0,X1,X3))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ! [X4] :
          ( sK7 != k1_funct_1(sK8,X4)
          | ~ r2_hidden(X4,sK5) )
      & r2_hidden(sK7,k2_relset_1(sK5,sK6,sK8))
      & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
      & v1_funct_2(sK8,sK5,sK6)
      & v1_funct_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X2
          | ~ r2_hidden(X4,X0) )
      & r2_hidden(X2,k2_relset_1(X0,X1,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X2
          | ~ r2_hidden(X4,X0) )
      & r2_hidden(X2,k2_relset_1(X0,X1,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ~ ( k1_funct_1(X3,X4) = X2
                  & r2_hidden(X4,X0) )
            & r2_hidden(X2,k2_relset_1(X0,X1,X3)) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ~ ( k1_funct_1(X3,X4) = X2
                & r2_hidden(X4,X0) )
          & r2_hidden(X2,k2_relset_1(X0,X1,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_funct_2)).

fof(f209,plain,
    ( spl11_15
    | ~ spl11_13 ),
    inference(avatar_split_clause,[],[f196,f185,f206])).

fof(f185,plain,
    ( spl11_13
  <=> sP0(sK7,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).

fof(f196,plain,
    ( sK7 = k1_funct_1(sK8,sK10(sK7,sK8))
    | ~ spl11_13 ),
    inference(unit_resulting_resolution,[],[f187,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X1,sK10(X0,X1)) = X0
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ! [X2] :
            ( k1_funct_1(X1,X2) != X0
            | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
      & ( ( k1_funct_1(X1,sK10(X0,X1)) = X0
          & r2_hidden(sK10(X0,X1),k1_relat_1(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f34,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( k1_funct_1(X1,X3) = X0
          & r2_hidden(X3,k1_relat_1(X1)) )
     => ( k1_funct_1(X1,sK10(X0,X1)) = X0
        & r2_hidden(sK10(X0,X1),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ! [X2] :
            ( k1_funct_1(X1,X2) != X0
            | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
      & ( ? [X3] :
            ( k1_funct_1(X1,X3) = X0
            & r2_hidden(X3,k1_relat_1(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X2,X0] :
      ( ( sP0(X2,X0)
        | ! [X3] :
            ( k1_funct_1(X0,X3) != X2
            | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
      & ( ? [X3] :
            ( k1_funct_1(X0,X3) = X2
            & r2_hidden(X3,k1_relat_1(X0)) )
        | ~ sP0(X2,X0) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X2,X0] :
      ( sP0(X2,X0)
    <=> ? [X3] :
          ( k1_funct_1(X0,X3) = X2
          & r2_hidden(X3,k1_relat_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f187,plain,
    ( sP0(sK7,sK8)
    | ~ spl11_13 ),
    inference(avatar_component_clause,[],[f185])).

fof(f204,plain,
    ( spl11_14
    | ~ spl11_13 ),
    inference(avatar_split_clause,[],[f198,f185,f201])).

fof(f198,plain,
    ( r2_hidden(sK10(sK7,sK8),k1_relat_1(sK8))
    | ~ spl11_13 ),
    inference(unit_resulting_resolution,[],[f187,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK10(X0,X1),k1_relat_1(X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f193,plain,
    ( spl11_13
    | ~ spl11_6
    | ~ spl11_12 ),
    inference(avatar_split_clause,[],[f192,f173,f101,f185])).

fof(f101,plain,
    ( spl11_6
  <=> sP2(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f173,plain,
    ( spl11_12
  <=> r2_hidden(sK7,k2_relat_1(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f192,plain,
    ( sP0(sK7,sK8)
    | ~ spl11_6
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f182,f103])).

fof(f103,plain,
    ( sP2(sK8)
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f101])).

fof(f182,plain,
    ( sP0(sK7,sK8)
    | ~ sP2(sK8)
    | ~ spl11_12 ),
    inference(resolution,[],[f175,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_relat_1(X1))
      | sP0(X0,X1)
      | ~ sP2(X1) ) ),
    inference(resolution,[],[f49,f68])).

fof(f68,plain,(
    ! [X0] :
      ( sP1(X0,k2_relat_1(X0))
      | ~ sP2(X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | k2_relat_1(X0) != X1
      | ~ sP2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ~ sP1(X0,X1) )
          & ( sP1(X0,X1)
            | k2_relat_1(X0) != X1 ) )
      | ~ sP2(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> sP1(X0,X1) )
      | ~ sP2(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( ~ sP1(X0,X1)
      | ~ r2_hidden(X3,X1)
      | sP0(X3,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ( ( ~ sP0(sK9(X0,X1),X0)
            | ~ r2_hidden(sK9(X0,X1),X1) )
          & ( sP0(sK9(X0,X1),X0)
            | r2_hidden(sK9(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ sP0(X3,X0) )
            & ( sP0(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f30,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ sP0(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( sP0(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ sP0(sK9(X0,X1),X0)
          | ~ r2_hidden(sK9(X0,X1),X1) )
        & ( sP0(sK9(X0,X1),X0)
          | r2_hidden(sK9(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> sP0(X2,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f175,plain,
    ( r2_hidden(sK7,k2_relat_1(sK8))
    | ~ spl11_12 ),
    inference(avatar_component_clause,[],[f173])).

fof(f176,plain,
    ( spl11_12
    | ~ spl11_1
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f171,f76,f71,f173])).

fof(f71,plain,
    ( spl11_1
  <=> r2_hidden(sK7,k2_relset_1(sK5,sK6,sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f76,plain,
    ( spl11_2
  <=> m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f171,plain,
    ( r2_hidden(sK7,k2_relat_1(sK8))
    | ~ spl11_1
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f165,f78])).

fof(f78,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f165,plain,
    ( r2_hidden(sK7,k2_relat_1(sK8))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ spl11_1 ),
    inference(superposition,[],[f73,f65])).

fof(f65,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f73,plain,
    ( r2_hidden(sK7,k2_relset_1(sK5,sK6,sK8))
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f71])).

fof(f155,plain,
    ( spl11_10
    | ~ spl11_5
    | ~ spl11_8 ),
    inference(avatar_split_clause,[],[f150,f127,f93,f152])).

fof(f127,plain,
    ( spl11_8
  <=> v4_relat_1(sK8,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f150,plain,
    ( sK8 = k7_relat_1(sK8,sK5)
    | ~ spl11_5
    | ~ spl11_8 ),
    inference(unit_resulting_resolution,[],[f95,f129,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f129,plain,
    ( v4_relat_1(sK8,sK5)
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f127])).

fof(f131,plain,
    ( spl11_8
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f125,f76,f127])).

fof(f125,plain,
    ( v4_relat_1(sK8,sK5)
    | ~ spl11_2 ),
    inference(resolution,[],[f66,f78])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f104,plain,
    ( spl11_6
    | ~ spl11_4
    | ~ spl11_5 ),
    inference(avatar_split_clause,[],[f99,f93,f86,f101])).

fof(f86,plain,
    ( spl11_4
  <=> v1_funct_1(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f99,plain,
    ( sP2(sK8)
    | ~ spl11_4
    | ~ spl11_5 ),
    inference(unit_resulting_resolution,[],[f88,f95,f56])).

fof(f56,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f12,f21,f20,f19])).

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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f88,plain,
    ( v1_funct_1(sK8)
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f86])).

fof(f97,plain,
    ( spl11_5
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f91,f76,f93])).

fof(f91,plain,
    ( v1_relat_1(sK8)
    | ~ spl11_2 ),
    inference(resolution,[],[f64,f78])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f89,plain,(
    spl11_4 ),
    inference(avatar_split_clause,[],[f42,f86])).

fof(f42,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f27])).

fof(f79,plain,(
    spl11_2 ),
    inference(avatar_split_clause,[],[f44,f76])).

fof(f44,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f27])).

fof(f74,plain,(
    spl11_1 ),
    inference(avatar_split_clause,[],[f45,f71])).

fof(f45,plain,(
    r2_hidden(sK7,k2_relset_1(sK5,sK6,sK8)) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.32  % Computer   : n007.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:11:06 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.18/0.45  % (16177)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.18/0.45  % (16173)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.18/0.46  % (16181)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.18/0.46  % (16170)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.18/0.47  % (16176)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.18/0.47  % (16179)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.18/0.47  % (16181)Refutation found. Thanks to Tanya!
% 0.18/0.47  % SZS status Theorem for theBenchmark
% 0.18/0.47  % SZS output start Proof for theBenchmark
% 0.18/0.47  fof(f245,plain,(
% 0.18/0.47    $false),
% 0.18/0.47    inference(avatar_sat_refutation,[],[f74,f79,f89,f97,f104,f131,f155,f176,f193,f204,f209,f237,f244])).
% 0.18/0.47  fof(f244,plain,(
% 0.18/0.47    ~spl11_5 | ~spl11_10 | ~spl11_14 | spl11_17),
% 0.18/0.47    inference(avatar_contradiction_clause,[],[f243])).
% 0.18/0.47  fof(f243,plain,(
% 0.18/0.47    $false | (~spl11_5 | ~spl11_10 | ~spl11_14 | spl11_17)),
% 0.18/0.47    inference(subsumption_resolution,[],[f242,f203])).
% 0.18/0.47  fof(f203,plain,(
% 0.18/0.47    r2_hidden(sK10(sK7,sK8),k1_relat_1(sK8)) | ~spl11_14),
% 0.18/0.47    inference(avatar_component_clause,[],[f201])).
% 0.18/0.47  fof(f201,plain,(
% 0.18/0.47    spl11_14 <=> r2_hidden(sK10(sK7,sK8),k1_relat_1(sK8))),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).
% 0.18/0.47  fof(f242,plain,(
% 0.18/0.47    ~r2_hidden(sK10(sK7,sK8),k1_relat_1(sK8)) | (~spl11_5 | ~spl11_10 | spl11_17)),
% 0.18/0.47    inference(forward_demodulation,[],[f239,f154])).
% 0.18/0.47  fof(f154,plain,(
% 0.18/0.47    sK8 = k7_relat_1(sK8,sK5) | ~spl11_10),
% 0.18/0.47    inference(avatar_component_clause,[],[f152])).
% 0.18/0.47  fof(f152,plain,(
% 0.18/0.47    spl11_10 <=> sK8 = k7_relat_1(sK8,sK5)),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).
% 0.18/0.47  fof(f239,plain,(
% 0.18/0.47    ~r2_hidden(sK10(sK7,sK8),k1_relat_1(k7_relat_1(sK8,sK5))) | (~spl11_5 | spl11_17)),
% 0.18/0.47    inference(unit_resulting_resolution,[],[f98,f238,f58])).
% 0.18/0.47  fof(f58,plain,(
% 0.18/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X1,k1_relat_1(k7_relat_1(X2,X0))) | sP3(X2,X1,X0) | ~sP4(X0,X1,X2)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f38])).
% 0.18/0.47  fof(f38,plain,(
% 0.18/0.47    ! [X0,X1,X2] : (((r2_hidden(X1,k1_relat_1(k7_relat_1(X2,X0))) | ~sP3(X2,X1,X0)) & (sP3(X2,X1,X0) | ~r2_hidden(X1,k1_relat_1(k7_relat_1(X2,X0))))) | ~sP4(X0,X1,X2))),
% 0.18/0.47    inference(rectify,[],[f37])).
% 0.18/0.47  fof(f37,plain,(
% 0.18/0.47    ! [X1,X0,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~sP3(X2,X0,X1)) & (sP3(X2,X0,X1) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~sP4(X1,X0,X2))),
% 0.18/0.47    inference(nnf_transformation,[],[f24])).
% 0.18/0.47  fof(f24,plain,(
% 0.18/0.47    ! [X1,X0,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> sP3(X2,X0,X1)) | ~sP4(X1,X0,X2))),
% 0.18/0.47    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 0.18/0.47  fof(f238,plain,(
% 0.18/0.47    ( ! [X0] : (~sP3(X0,sK10(sK7,sK8),sK5)) ) | spl11_17),
% 0.18/0.47    inference(unit_resulting_resolution,[],[f235,f60])).
% 0.18/0.47  fof(f60,plain,(
% 0.18/0.47    ( ! [X2,X0,X1] : (~sP3(X0,X1,X2) | r2_hidden(X1,X2)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f41])).
% 0.18/0.47  fof(f41,plain,(
% 0.18/0.47    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | ~r2_hidden(X1,k1_relat_1(X0)) | ~r2_hidden(X1,X2)) & ((r2_hidden(X1,k1_relat_1(X0)) & r2_hidden(X1,X2)) | ~sP3(X0,X1,X2)))),
% 0.18/0.47    inference(rectify,[],[f40])).
% 0.18/0.47  fof(f40,plain,(
% 0.18/0.47    ! [X2,X0,X1] : ((sP3(X2,X0,X1) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~sP3(X2,X0,X1)))),
% 0.18/0.47    inference(flattening,[],[f39])).
% 0.18/0.48  fof(f39,plain,(
% 0.18/0.48    ! [X2,X0,X1] : ((sP3(X2,X0,X1) | (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~sP3(X2,X0,X1)))),
% 0.18/0.48    inference(nnf_transformation,[],[f23])).
% 0.18/0.48  fof(f23,plain,(
% 0.18/0.48    ! [X2,X0,X1] : (sP3(X2,X0,X1) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)))),
% 0.18/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.18/0.48  fof(f235,plain,(
% 0.18/0.48    ~r2_hidden(sK10(sK7,sK8),sK5) | spl11_17),
% 0.18/0.48    inference(avatar_component_clause,[],[f233])).
% 0.18/0.48  fof(f233,plain,(
% 0.18/0.48    spl11_17 <=> r2_hidden(sK10(sK7,sK8),sK5)),
% 0.18/0.48    introduced(avatar_definition,[new_symbols(naming,[spl11_17])])).
% 0.18/0.48  fof(f98,plain,(
% 0.18/0.48    ( ! [X0,X1] : (sP4(X0,X1,sK8)) ) | ~spl11_5),
% 0.18/0.48    inference(unit_resulting_resolution,[],[f95,f63])).
% 0.18/0.48  fof(f63,plain,(
% 0.18/0.48    ( ! [X2,X0,X1] : (sP4(X1,X0,X2) | ~v1_relat_1(X2)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f25])).
% 0.18/0.48  fof(f25,plain,(
% 0.18/0.48    ! [X0,X1,X2] : (sP4(X1,X0,X2) | ~v1_relat_1(X2))),
% 0.18/0.48    inference(definition_folding,[],[f15,f24,f23])).
% 0.18/0.48  fof(f15,plain,(
% 0.18/0.48    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 0.18/0.48    inference(ennf_transformation,[],[f2])).
% 0.18/0.48  fof(f2,axiom,(
% 0.18/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 0.18/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).
% 0.18/0.48  fof(f95,plain,(
% 0.18/0.48    v1_relat_1(sK8) | ~spl11_5),
% 0.18/0.48    inference(avatar_component_clause,[],[f93])).
% 0.18/0.48  fof(f93,plain,(
% 0.18/0.48    spl11_5 <=> v1_relat_1(sK8)),
% 0.18/0.48    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).
% 0.18/0.48  fof(f237,plain,(
% 0.18/0.48    ~spl11_17 | ~spl11_15),
% 0.18/0.48    inference(avatar_split_clause,[],[f231,f206,f233])).
% 0.18/0.48  fof(f206,plain,(
% 0.18/0.48    spl11_15 <=> sK7 = k1_funct_1(sK8,sK10(sK7,sK8))),
% 0.18/0.48    introduced(avatar_definition,[new_symbols(naming,[spl11_15])])).
% 0.18/0.48  fof(f231,plain,(
% 0.18/0.48    ~r2_hidden(sK10(sK7,sK8),sK5) | ~spl11_15),
% 0.18/0.48    inference(trivial_inequality_removal,[],[f229])).
% 0.18/0.48  fof(f229,plain,(
% 0.18/0.48    sK7 != sK7 | ~r2_hidden(sK10(sK7,sK8),sK5) | ~spl11_15),
% 0.18/0.48    inference(superposition,[],[f46,f208])).
% 0.18/0.48  fof(f208,plain,(
% 0.18/0.48    sK7 = k1_funct_1(sK8,sK10(sK7,sK8)) | ~spl11_15),
% 0.18/0.48    inference(avatar_component_clause,[],[f206])).
% 0.18/0.48  fof(f46,plain,(
% 0.18/0.48    ( ! [X4] : (sK7 != k1_funct_1(sK8,X4) | ~r2_hidden(X4,sK5)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f27])).
% 0.18/0.48  fof(f27,plain,(
% 0.18/0.48    ! [X4] : (sK7 != k1_funct_1(sK8,X4) | ~r2_hidden(X4,sK5)) & r2_hidden(sK7,k2_relset_1(sK5,sK6,sK8)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK8,sK5,sK6) & v1_funct_1(sK8)),
% 0.18/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f10,f26])).
% 0.18/0.48  fof(f26,plain,(
% 0.18/0.48    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X2 | ~r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (sK7 != k1_funct_1(sK8,X4) | ~r2_hidden(X4,sK5)) & r2_hidden(sK7,k2_relset_1(sK5,sK6,sK8)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK8,sK5,sK6) & v1_funct_1(sK8))),
% 0.18/0.48    introduced(choice_axiom,[])).
% 0.18/0.48  fof(f10,plain,(
% 0.18/0.48    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X2 | ~r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.18/0.48    inference(flattening,[],[f9])).
% 0.18/0.48  fof(f9,plain,(
% 0.18/0.48    ? [X0,X1,X2,X3] : ((! [X4] : (k1_funct_1(X3,X4) != X2 | ~r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.18/0.48    inference(ennf_transformation,[],[f8])).
% 0.18/0.48  fof(f8,negated_conjecture,(
% 0.18/0.48    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ~(! [X4] : ~(k1_funct_1(X3,X4) = X2 & r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3))))),
% 0.18/0.48    inference(negated_conjecture,[],[f7])).
% 0.18/0.48  fof(f7,conjecture,(
% 0.18/0.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ~(! [X4] : ~(k1_funct_1(X3,X4) = X2 & r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3))))),
% 0.18/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_funct_2)).
% 0.18/0.48  fof(f209,plain,(
% 0.18/0.48    spl11_15 | ~spl11_13),
% 0.18/0.48    inference(avatar_split_clause,[],[f196,f185,f206])).
% 0.18/0.48  fof(f185,plain,(
% 0.18/0.48    spl11_13 <=> sP0(sK7,sK8)),
% 0.18/0.48    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).
% 0.18/0.48  fof(f196,plain,(
% 0.18/0.48    sK7 = k1_funct_1(sK8,sK10(sK7,sK8)) | ~spl11_13),
% 0.18/0.48    inference(unit_resulting_resolution,[],[f187,f54])).
% 0.18/0.48  fof(f54,plain,(
% 0.18/0.48    ( ! [X0,X1] : (k1_funct_1(X1,sK10(X0,X1)) = X0 | ~sP0(X0,X1)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f36])).
% 0.18/0.48  fof(f36,plain,(
% 0.18/0.48    ! [X0,X1] : ((sP0(X0,X1) | ! [X2] : (k1_funct_1(X1,X2) != X0 | ~r2_hidden(X2,k1_relat_1(X1)))) & ((k1_funct_1(X1,sK10(X0,X1)) = X0 & r2_hidden(sK10(X0,X1),k1_relat_1(X1))) | ~sP0(X0,X1)))),
% 0.18/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f34,f35])).
% 0.18/0.48  fof(f35,plain,(
% 0.18/0.48    ! [X1,X0] : (? [X3] : (k1_funct_1(X1,X3) = X0 & r2_hidden(X3,k1_relat_1(X1))) => (k1_funct_1(X1,sK10(X0,X1)) = X0 & r2_hidden(sK10(X0,X1),k1_relat_1(X1))))),
% 0.18/0.48    introduced(choice_axiom,[])).
% 0.18/0.48  fof(f34,plain,(
% 0.18/0.48    ! [X0,X1] : ((sP0(X0,X1) | ! [X2] : (k1_funct_1(X1,X2) != X0 | ~r2_hidden(X2,k1_relat_1(X1)))) & (? [X3] : (k1_funct_1(X1,X3) = X0 & r2_hidden(X3,k1_relat_1(X1))) | ~sP0(X0,X1)))),
% 0.18/0.48    inference(rectify,[],[f33])).
% 0.18/0.48  fof(f33,plain,(
% 0.18/0.48    ! [X2,X0] : ((sP0(X2,X0) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X2,X0)))),
% 0.18/0.48    inference(nnf_transformation,[],[f19])).
% 0.18/0.48  fof(f19,plain,(
% 0.18/0.48    ! [X2,X0] : (sP0(X2,X0) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))),
% 0.18/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.18/0.48  fof(f187,plain,(
% 0.18/0.48    sP0(sK7,sK8) | ~spl11_13),
% 0.18/0.48    inference(avatar_component_clause,[],[f185])).
% 0.18/0.48  fof(f204,plain,(
% 0.18/0.48    spl11_14 | ~spl11_13),
% 0.18/0.48    inference(avatar_split_clause,[],[f198,f185,f201])).
% 0.18/0.48  fof(f198,plain,(
% 0.18/0.48    r2_hidden(sK10(sK7,sK8),k1_relat_1(sK8)) | ~spl11_13),
% 0.18/0.48    inference(unit_resulting_resolution,[],[f187,f53])).
% 0.18/0.48  fof(f53,plain,(
% 0.18/0.48    ( ! [X0,X1] : (r2_hidden(sK10(X0,X1),k1_relat_1(X1)) | ~sP0(X0,X1)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f36])).
% 0.18/0.48  fof(f193,plain,(
% 0.18/0.48    spl11_13 | ~spl11_6 | ~spl11_12),
% 0.18/0.48    inference(avatar_split_clause,[],[f192,f173,f101,f185])).
% 0.18/0.48  fof(f101,plain,(
% 0.18/0.48    spl11_6 <=> sP2(sK8)),
% 0.18/0.48    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).
% 0.18/0.48  fof(f173,plain,(
% 0.18/0.48    spl11_12 <=> r2_hidden(sK7,k2_relat_1(sK8))),
% 0.18/0.48    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).
% 0.18/0.48  fof(f192,plain,(
% 0.18/0.48    sP0(sK7,sK8) | (~spl11_6 | ~spl11_12)),
% 0.18/0.48    inference(subsumption_resolution,[],[f182,f103])).
% 0.18/0.48  fof(f103,plain,(
% 0.18/0.48    sP2(sK8) | ~spl11_6),
% 0.18/0.48    inference(avatar_component_clause,[],[f101])).
% 0.18/0.48  fof(f182,plain,(
% 0.18/0.48    sP0(sK7,sK8) | ~sP2(sK8) | ~spl11_12),
% 0.18/0.48    inference(resolution,[],[f175,f117])).
% 0.18/0.48  fof(f117,plain,(
% 0.18/0.48    ( ! [X0,X1] : (~r2_hidden(X0,k2_relat_1(X1)) | sP0(X0,X1) | ~sP2(X1)) )),
% 0.18/0.48    inference(resolution,[],[f49,f68])).
% 0.18/0.48  fof(f68,plain,(
% 0.18/0.48    ( ! [X0] : (sP1(X0,k2_relat_1(X0)) | ~sP2(X0)) )),
% 0.18/0.48    inference(equality_resolution,[],[f47])).
% 0.18/0.48  fof(f47,plain,(
% 0.18/0.48    ( ! [X0,X1] : (sP1(X0,X1) | k2_relat_1(X0) != X1 | ~sP2(X0)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f28])).
% 0.18/0.48  fof(f28,plain,(
% 0.18/0.48    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ~sP1(X0,X1)) & (sP1(X0,X1) | k2_relat_1(X0) != X1)) | ~sP2(X0))),
% 0.18/0.48    inference(nnf_transformation,[],[f21])).
% 0.18/0.48  fof(f21,plain,(
% 0.18/0.48    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> sP1(X0,X1)) | ~sP2(X0))),
% 0.18/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.18/0.48  fof(f49,plain,(
% 0.18/0.48    ( ! [X0,X3,X1] : (~sP1(X0,X1) | ~r2_hidden(X3,X1) | sP0(X3,X0)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f32])).
% 0.18/0.48  fof(f32,plain,(
% 0.18/0.48    ! [X0,X1] : ((sP1(X0,X1) | ((~sP0(sK9(X0,X1),X0) | ~r2_hidden(sK9(X0,X1),X1)) & (sP0(sK9(X0,X1),X0) | r2_hidden(sK9(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~sP0(X3,X0)) & (sP0(X3,X0) | ~r2_hidden(X3,X1))) | ~sP1(X0,X1)))),
% 0.18/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f30,f31])).
% 0.18/0.48  fof(f31,plain,(
% 0.18/0.48    ! [X1,X0] : (? [X2] : ((~sP0(X2,X0) | ~r2_hidden(X2,X1)) & (sP0(X2,X0) | r2_hidden(X2,X1))) => ((~sP0(sK9(X0,X1),X0) | ~r2_hidden(sK9(X0,X1),X1)) & (sP0(sK9(X0,X1),X0) | r2_hidden(sK9(X0,X1),X1))))),
% 0.18/0.48    introduced(choice_axiom,[])).
% 0.18/0.48  fof(f30,plain,(
% 0.18/0.48    ! [X0,X1] : ((sP1(X0,X1) | ? [X2] : ((~sP0(X2,X0) | ~r2_hidden(X2,X1)) & (sP0(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~sP0(X3,X0)) & (sP0(X3,X0) | ~r2_hidden(X3,X1))) | ~sP1(X0,X1)))),
% 0.18/0.48    inference(rectify,[],[f29])).
% 0.18/0.48  fof(f29,plain,(
% 0.18/0.48    ! [X0,X1] : ((sP1(X0,X1) | ? [X2] : ((~sP0(X2,X0) | ~r2_hidden(X2,X1)) & (sP0(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~sP0(X2,X0)) & (sP0(X2,X0) | ~r2_hidden(X2,X1))) | ~sP1(X0,X1)))),
% 0.18/0.48    inference(nnf_transformation,[],[f20])).
% 0.18/0.48  fof(f20,plain,(
% 0.18/0.48    ! [X0,X1] : (sP1(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> sP0(X2,X0)))),
% 0.18/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.18/0.48  fof(f175,plain,(
% 0.18/0.48    r2_hidden(sK7,k2_relat_1(sK8)) | ~spl11_12),
% 0.18/0.48    inference(avatar_component_clause,[],[f173])).
% 0.18/0.48  fof(f176,plain,(
% 0.18/0.48    spl11_12 | ~spl11_1 | ~spl11_2),
% 0.18/0.48    inference(avatar_split_clause,[],[f171,f76,f71,f173])).
% 0.18/0.48  fof(f71,plain,(
% 0.18/0.48    spl11_1 <=> r2_hidden(sK7,k2_relset_1(sK5,sK6,sK8))),
% 0.18/0.48    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 0.18/0.48  fof(f76,plain,(
% 0.18/0.48    spl11_2 <=> m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))),
% 0.18/0.48    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 0.18/0.48  fof(f171,plain,(
% 0.18/0.48    r2_hidden(sK7,k2_relat_1(sK8)) | (~spl11_1 | ~spl11_2)),
% 0.18/0.48    inference(subsumption_resolution,[],[f165,f78])).
% 0.18/0.48  fof(f78,plain,(
% 0.18/0.48    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) | ~spl11_2),
% 0.18/0.48    inference(avatar_component_clause,[],[f76])).
% 0.18/0.48  fof(f165,plain,(
% 0.18/0.48    r2_hidden(sK7,k2_relat_1(sK8)) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) | ~spl11_1),
% 0.18/0.48    inference(superposition,[],[f73,f65])).
% 0.18/0.48  fof(f65,plain,(
% 0.18/0.48    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.18/0.48    inference(cnf_transformation,[],[f17])).
% 0.18/0.48  fof(f17,plain,(
% 0.18/0.48    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.48    inference(ennf_transformation,[],[f6])).
% 0.18/0.48  fof(f6,axiom,(
% 0.18/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.18/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.18/0.48  fof(f73,plain,(
% 0.18/0.48    r2_hidden(sK7,k2_relset_1(sK5,sK6,sK8)) | ~spl11_1),
% 0.18/0.48    inference(avatar_component_clause,[],[f71])).
% 0.18/0.48  fof(f155,plain,(
% 0.18/0.48    spl11_10 | ~spl11_5 | ~spl11_8),
% 0.18/0.48    inference(avatar_split_clause,[],[f150,f127,f93,f152])).
% 0.18/0.48  fof(f127,plain,(
% 0.18/0.48    spl11_8 <=> v4_relat_1(sK8,sK5)),
% 0.18/0.48    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).
% 0.18/0.48  fof(f150,plain,(
% 0.18/0.48    sK8 = k7_relat_1(sK8,sK5) | (~spl11_5 | ~spl11_8)),
% 0.18/0.48    inference(unit_resulting_resolution,[],[f95,f129,f57])).
% 0.18/0.48  fof(f57,plain,(
% 0.18/0.48    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f14])).
% 0.18/0.48  fof(f14,plain,(
% 0.18/0.48    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.18/0.48    inference(flattening,[],[f13])).
% 0.18/0.48  fof(f13,plain,(
% 0.18/0.48    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.18/0.48    inference(ennf_transformation,[],[f1])).
% 0.18/0.48  fof(f1,axiom,(
% 0.18/0.48    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.18/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.18/0.48  fof(f129,plain,(
% 0.18/0.48    v4_relat_1(sK8,sK5) | ~spl11_8),
% 0.18/0.48    inference(avatar_component_clause,[],[f127])).
% 0.18/0.48  fof(f131,plain,(
% 0.18/0.48    spl11_8 | ~spl11_2),
% 0.18/0.48    inference(avatar_split_clause,[],[f125,f76,f127])).
% 0.18/0.48  fof(f125,plain,(
% 0.18/0.48    v4_relat_1(sK8,sK5) | ~spl11_2),
% 0.18/0.48    inference(resolution,[],[f66,f78])).
% 0.18/0.48  fof(f66,plain,(
% 0.18/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f18])).
% 0.18/0.48  fof(f18,plain,(
% 0.18/0.48    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.48    inference(ennf_transformation,[],[f5])).
% 0.18/0.48  fof(f5,axiom,(
% 0.18/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.18/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.18/0.48  fof(f104,plain,(
% 0.18/0.48    spl11_6 | ~spl11_4 | ~spl11_5),
% 0.18/0.48    inference(avatar_split_clause,[],[f99,f93,f86,f101])).
% 0.18/0.48  fof(f86,plain,(
% 0.18/0.48    spl11_4 <=> v1_funct_1(sK8)),
% 0.18/0.48    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).
% 0.18/0.48  fof(f99,plain,(
% 0.18/0.48    sP2(sK8) | (~spl11_4 | ~spl11_5)),
% 0.18/0.48    inference(unit_resulting_resolution,[],[f88,f95,f56])).
% 0.18/0.48  fof(f56,plain,(
% 0.18/0.48    ( ! [X0] : (sP2(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f22])).
% 0.18/0.48  fof(f22,plain,(
% 0.18/0.48    ! [X0] : (sP2(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.18/0.48    inference(definition_folding,[],[f12,f21,f20,f19])).
% 0.18/0.48  fof(f12,plain,(
% 0.18/0.48    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.18/0.48    inference(flattening,[],[f11])).
% 0.18/0.48  fof(f11,plain,(
% 0.18/0.48    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.18/0.48    inference(ennf_transformation,[],[f3])).
% 0.18/0.48  fof(f3,axiom,(
% 0.18/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.18/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 0.18/0.48  fof(f88,plain,(
% 0.18/0.48    v1_funct_1(sK8) | ~spl11_4),
% 0.18/0.48    inference(avatar_component_clause,[],[f86])).
% 0.18/0.48  fof(f97,plain,(
% 0.18/0.48    spl11_5 | ~spl11_2),
% 0.18/0.48    inference(avatar_split_clause,[],[f91,f76,f93])).
% 0.18/0.48  fof(f91,plain,(
% 0.18/0.48    v1_relat_1(sK8) | ~spl11_2),
% 0.18/0.48    inference(resolution,[],[f64,f78])).
% 0.18/0.48  fof(f64,plain,(
% 0.18/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f16])).
% 0.18/0.48  fof(f16,plain,(
% 0.18/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.48    inference(ennf_transformation,[],[f4])).
% 0.18/0.48  fof(f4,axiom,(
% 0.18/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.18/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.18/0.48  fof(f89,plain,(
% 0.18/0.48    spl11_4),
% 0.18/0.48    inference(avatar_split_clause,[],[f42,f86])).
% 0.18/0.48  fof(f42,plain,(
% 0.18/0.48    v1_funct_1(sK8)),
% 0.18/0.48    inference(cnf_transformation,[],[f27])).
% 0.18/0.48  fof(f79,plain,(
% 0.18/0.48    spl11_2),
% 0.18/0.48    inference(avatar_split_clause,[],[f44,f76])).
% 0.18/0.48  fof(f44,plain,(
% 0.18/0.48    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))),
% 0.18/0.48    inference(cnf_transformation,[],[f27])).
% 0.18/0.48  fof(f74,plain,(
% 0.18/0.48    spl11_1),
% 0.18/0.48    inference(avatar_split_clause,[],[f45,f71])).
% 0.18/0.48  fof(f45,plain,(
% 0.18/0.48    r2_hidden(sK7,k2_relset_1(sK5,sK6,sK8))),
% 0.18/0.48    inference(cnf_transformation,[],[f27])).
% 0.18/0.48  % SZS output end Proof for theBenchmark
% 0.18/0.48  % (16181)------------------------------
% 0.18/0.48  % (16181)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.48  % (16181)Termination reason: Refutation
% 0.18/0.48  
% 0.18/0.48  % (16181)Memory used [KB]: 10746
% 0.18/0.48  % (16181)Time elapsed: 0.077 s
% 0.18/0.48  % (16181)------------------------------
% 0.18/0.48  % (16181)------------------------------
% 0.18/0.48  % (16171)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.18/0.48  % (16166)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.18/0.48  % (16183)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.18/0.48  % (16184)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.18/0.48  % (16180)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.18/0.48  % (16166)Refutation not found, incomplete strategy% (16166)------------------------------
% 0.18/0.48  % (16166)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.48  % (16166)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.48  
% 0.18/0.48  % (16166)Memory used [KB]: 10618
% 0.18/0.48  % (16166)Time elapsed: 0.065 s
% 0.18/0.48  % (16166)------------------------------
% 0.18/0.48  % (16166)------------------------------
% 0.18/0.48  % (16178)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.18/0.49  % (16168)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.18/0.49  % (16165)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.18/0.49  % (16169)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.18/0.49  % (16164)Success in time 0.148 s
%------------------------------------------------------------------------------
