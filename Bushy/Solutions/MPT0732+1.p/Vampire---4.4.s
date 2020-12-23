%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : ordinal1__t19_ordinal1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:25 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 238 expanded)
%              Number of leaves         :   31 (  96 expanded)
%              Depth                    :    7
%              Number of atoms          :  282 ( 587 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f252,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f67,f74,f81,f88,f98,f109,f116,f131,f138,f147,f154,f164,f172,f191,f198,f215,f222,f233,f245,f247,f249,f251])).

fof(f251,plain,
    ( ~ spl4_4
    | ~ spl4_26
    | spl4_31 ),
    inference(avatar_contradiction_clause,[],[f250])).

fof(f250,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_26
    | ~ spl4_31 ),
    inference(subsumption_resolution,[],[f235,f171])).

fof(f171,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK2))
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl4_26
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f235,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK2))
    | ~ spl4_4
    | ~ spl4_31 ),
    inference(unit_resulting_resolution,[],[f197,f73,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t19_ordinal1.p',t4_subset)).

fof(f73,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl4_4
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f197,plain,
    ( ~ m1_subset_1(sK0,sK2)
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl4_31
  <=> ~ m1_subset_1(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f249,plain,
    ( ~ spl4_4
    | ~ spl4_26
    | spl4_31 ),
    inference(avatar_contradiction_clause,[],[f248])).

fof(f248,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_26
    | ~ spl4_31 ),
    inference(subsumption_resolution,[],[f240,f73])).

fof(f240,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ spl4_26
    | ~ spl4_31 ),
    inference(unit_resulting_resolution,[],[f197,f171,f52])).

fof(f247,plain,
    ( ~ spl4_4
    | ~ spl4_26
    | spl4_31 ),
    inference(avatar_contradiction_clause,[],[f246])).

fof(f246,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_26
    | ~ spl4_31 ),
    inference(subsumption_resolution,[],[f241,f197])).

fof(f241,plain,
    ( m1_subset_1(sK0,sK2)
    | ~ spl4_4
    | ~ spl4_26 ),
    inference(unit_resulting_resolution,[],[f73,f171,f52])).

fof(f245,plain,
    ( ~ spl4_4
    | ~ spl4_26
    | spl4_31 ),
    inference(avatar_contradiction_clause,[],[f242])).

fof(f242,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_26
    | ~ spl4_31 ),
    inference(unit_resulting_resolution,[],[f197,f73,f171,f52])).

fof(f233,plain,
    ( ~ spl4_37
    | spl4_33 ),
    inference(avatar_split_clause,[],[f223,f213,f231])).

fof(f231,plain,
    ( spl4_37
  <=> ~ r1_tarski(sK1,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f213,plain,
    ( spl4_33
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f223,plain,
    ( ~ r1_tarski(sK1,o_0_0_xboole_0)
    | ~ spl4_33 ),
    inference(unit_resulting_resolution,[],[f214,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t19_ordinal1.p',t3_subset)).

fof(f214,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f213])).

fof(f222,plain,
    ( ~ spl4_35
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f204,f79,f65,f220])).

fof(f220,plain,
    ( spl4_35
  <=> ~ m1_subset_1(sK2,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f65,plain,
    ( spl4_2
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f79,plain,
    ( spl4_6
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f204,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f80,f66,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t19_ordinal1.p',t5_subset)).

fof(f66,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f80,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f79])).

fof(f215,plain,
    ( ~ spl4_33
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f203,f72,f65,f213])).

fof(f203,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f73,f66,f53])).

fof(f198,plain,
    ( ~ spl4_31
    | spl4_9
    | spl4_15 ),
    inference(avatar_split_clause,[],[f179,f114,f86,f196])).

fof(f86,plain,
    ( spl4_9
  <=> ~ r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f114,plain,
    ( spl4_15
  <=> ~ v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f179,plain,
    ( ~ m1_subset_1(sK0,sK2)
    | ~ spl4_9
    | ~ spl4_15 ),
    inference(unit_resulting_resolution,[],[f87,f115,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t19_ordinal1.p',t2_subset)).

fof(f115,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f114])).

fof(f87,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f86])).

fof(f191,plain,
    ( ~ spl4_29
    | spl4_13
    | spl4_19 ),
    inference(avatar_split_clause,[],[f176,f136,f107,f189])).

fof(f189,plain,
    ( spl4_29
  <=> ~ m1_subset_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f107,plain,
    ( spl4_13
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f136,plain,
    ( spl4_19
  <=> ~ r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f176,plain,
    ( ~ m1_subset_1(sK2,sK1)
    | ~ spl4_13
    | ~ spl4_19 ),
    inference(unit_resulting_resolution,[],[f137,f108,f46])).

fof(f108,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f107])).

fof(f137,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f136])).

fof(f172,plain,
    ( spl4_26
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f165,f162,f170])).

fof(f162,plain,
    ( spl4_24
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f165,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK2))
    | ~ spl4_24 ),
    inference(unit_resulting_resolution,[],[f163,f49])).

fof(f163,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f162])).

fof(f164,plain,
    ( spl4_24
    | ~ spl4_0
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f157,f79,f58,f162])).

fof(f58,plain,
    ( spl4_0
  <=> v1_ordinal1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_0])])).

fof(f157,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl4_0
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f59,f80,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | ~ r2_hidden(X1,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t19_ordinal1.p',d2_ordinal1)).

fof(f59,plain,
    ( v1_ordinal1(sK2)
    | ~ spl4_0 ),
    inference(avatar_component_clause,[],[f58])).

fof(f154,plain,
    ( spl4_22
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f140,f79,f152])).

fof(f152,plain,
    ( spl4_22
  <=> m1_subset_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f140,plain,
    ( m1_subset_1(sK1,sK2)
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f80,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t19_ordinal1.p',t1_subset)).

fof(f147,plain,
    ( spl4_20
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f139,f72,f145])).

fof(f145,plain,
    ( spl4_20
  <=> m1_subset_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f139,plain,
    ( m1_subset_1(sK0,sK1)
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f73,f48])).

fof(f138,plain,
    ( ~ spl4_19
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f122,f79,f136])).

fof(f122,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f80,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t19_ordinal1.p',antisymmetry_r2_hidden)).

fof(f131,plain,
    ( ~ spl4_17
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f121,f72,f129])).

fof(f129,plain,
    ( spl4_17
  <=> ~ r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f121,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f73,f47])).

fof(f116,plain,
    ( ~ spl4_15
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f100,f79,f114])).

fof(f100,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f80,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t19_ordinal1.p',t7_boole)).

fof(f109,plain,
    ( ~ spl4_13
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f99,f72,f107])).

fof(f99,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f73,f51])).

fof(f98,plain,
    ( spl4_10
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f89,f65,f96])).

fof(f96,plain,
    ( spl4_10
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f89,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f66,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t19_ordinal1.p',t6_boole)).

fof(f88,plain,(
    ~ spl4_9 ),
    inference(avatar_split_clause,[],[f41,f86])).

fof(f41,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ~ r2_hidden(sK0,sK2)
    & r2_hidden(sK1,sK2)
    & r2_hidden(sK0,sK1)
    & v1_ordinal1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f34])).

fof(f34,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X0,X2)
        & r2_hidden(X1,X2)
        & r2_hidden(X0,X1)
        & v1_ordinal1(X2) )
   => ( ~ r2_hidden(sK0,sK2)
      & r2_hidden(sK1,sK2)
      & r2_hidden(sK0,sK1)
      & v1_ordinal1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & r2_hidden(X1,X2)
      & r2_hidden(X0,X1)
      & v1_ordinal1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & r2_hidden(X1,X2)
      & r2_hidden(X0,X1)
      & v1_ordinal1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_ordinal1(X2)
       => ( ( r2_hidden(X1,X2)
            & r2_hidden(X0,X1) )
         => r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( v1_ordinal1(X2)
     => ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X1) )
       => r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t19_ordinal1.p',t19_ordinal1)).

fof(f81,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f40,f79])).

fof(f40,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f74,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f39,f72])).

fof(f39,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f67,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f42,f65])).

fof(f42,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/ordinal1__t19_ordinal1.p',dt_o_0_0_xboole_0)).

fof(f60,plain,(
    spl4_0 ),
    inference(avatar_split_clause,[],[f38,f58])).

fof(f38,plain,(
    v1_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
