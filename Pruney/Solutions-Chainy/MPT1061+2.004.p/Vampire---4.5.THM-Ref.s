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
% DateTime   : Thu Dec  3 13:07:32 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  178 ( 382 expanded)
%              Number of leaves         :   41 ( 149 expanded)
%              Depth                    :   11
%              Number of atoms          :  606 (1469 expanded)
%              Number of equality atoms :   24 (  59 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f674,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f91,f96,f101,f106,f111,f116,f121,f131,f157,f168,f245,f363,f378,f382,f387,f415,f470,f603,f636,f669,f670,f673])).

fof(f673,plain,
    ( ~ spl6_6
    | ~ spl6_8
    | spl6_9
    | spl6_35
    | ~ spl6_55
    | ~ spl6_56 ),
    inference(avatar_contradiction_clause,[],[f672])).

fof(f672,plain,
    ( $false
    | ~ spl6_6
    | ~ spl6_8
    | spl6_9
    | spl6_35
    | ~ spl6_55
    | ~ spl6_56 ),
    inference(subsumption_resolution,[],[f671,f668])).

fof(f668,plain,
    ( m1_subset_1(k7_relat_1(sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
    | ~ spl6_56 ),
    inference(avatar_component_clause,[],[f666])).

fof(f666,plain,
    ( spl6_56
  <=> m1_subset_1(k7_relat_1(sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_56])])).

fof(f671,plain,
    ( ~ m1_subset_1(k7_relat_1(sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
    | ~ spl6_6
    | ~ spl6_8
    | spl6_9
    | spl6_35
    | ~ spl6_55 ),
    inference(unit_resulting_resolution,[],[f115,f403,f455,f662,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_partfun1(X2,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f662,plain,
    ( v1_funct_2(k7_relat_1(sK5,sK2),sK2,sK4)
    | ~ spl6_55 ),
    inference(avatar_component_clause,[],[f660])).

fof(f660,plain,
    ( spl6_55
  <=> v1_funct_2(k7_relat_1(sK5,sK2),sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_55])])).

fof(f455,plain,
    ( ~ v1_partfun1(k7_relat_1(sK5,sK2),sK2)
    | spl6_35 ),
    inference(avatar_component_clause,[],[f453])).

fof(f453,plain,
    ( spl6_35
  <=> v1_partfun1(k7_relat_1(sK5,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f403,plain,
    ( ! [X4] : v1_funct_1(k7_relat_1(sK5,X4))
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f402,f110])).

fof(f110,plain,
    ( v1_funct_1(sK5)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl6_8
  <=> v1_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f402,plain,
    ( ! [X4] :
        ( v1_funct_1(k7_relat_1(sK5,X4))
        | ~ v1_funct_1(sK5) )
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f337,f100])).

fof(f100,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4)))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl6_6
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f337,plain,
    ( ! [X4] :
        ( v1_funct_1(k7_relat_1(sK5,X4))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4)))
        | ~ v1_funct_1(sK5) )
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(superposition,[],[f146,f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f146,plain,
    ( ! [X0] : v1_funct_1(k2_partfun1(sK1,sK4,sK5,X0))
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(unit_resulting_resolution,[],[f110,f100,f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f115,plain,
    ( ~ v1_xboole_0(sK4)
    | spl6_9 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl6_9
  <=> v1_xboole_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f670,plain,
    ( spl6_55
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f653,f140,f108,f98,f660])).

fof(f140,plain,
    ( spl6_12
  <=> sP0(sK4,sK2,sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f653,plain,
    ( v1_funct_2(k7_relat_1(sK5,sK2),sK2,sK4)
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_12 ),
    inference(unit_resulting_resolution,[],[f141,f490])).

fof(f490,plain,
    ( ! [X4] :
        ( v1_funct_2(k7_relat_1(sK5,X4),X4,sK4)
        | ~ sP0(sK4,X4,sK5,sK1) )
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(superposition,[],[f66,f326])).

fof(f326,plain,
    ( ! [X0] : k7_relat_1(sK5,X0) = k2_partfun1(sK1,sK4,sK5,X0)
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(unit_resulting_resolution,[],[f110,f100,f70])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_partfun1(X3,X0,X2,X1),X1,X0)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_partfun1(X3,X0,X2,X1),X1,X0)
        & v1_funct_1(k2_partfun1(X3,X0,X2,X1)) )
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X1,X2,X3,X0] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      | ~ sP0(X1,X2,X3,X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X1,X2,X3,X0] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      | ~ sP0(X1,X2,X3,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f141,plain,
    ( sP0(sK4,sK2,sK5,sK1)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f140])).

fof(f669,plain,
    ( spl6_56
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f664,f140,f108,f98,f666])).

fof(f664,plain,
    ( m1_subset_1(k7_relat_1(sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_12 ),
    inference(forward_demodulation,[],[f654,f326])).

fof(f654,plain,
    ( m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
    | ~ spl6_12 ),
    inference(unit_resulting_resolution,[],[f141,f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f636,plain,
    ( k1_xboole_0 != sK4
    | v1_xboole_0(sK4)
    | ~ v1_xboole_0(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f603,plain,
    ( spl6_46
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | spl6_12 ),
    inference(avatar_split_clause,[],[f586,f140,f108,f103,f98,f93,f600])).

fof(f600,plain,
    ( spl6_46
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f93,plain,
    ( spl6_5
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f103,plain,
    ( spl6_7
  <=> v1_funct_2(sK5,sK1,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f586,plain,
    ( k1_xboole_0 = sK4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | spl6_12 ),
    inference(unit_resulting_resolution,[],[f110,f95,f105,f142,f100,f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(X2,X0)
      | sP0(X1,X2,X3,X0)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( sP0(X1,X2,X3,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(definition_folding,[],[f33,f38])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
            & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
            & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).

fof(f142,plain,
    ( ~ sP0(sK4,sK2,sK5,sK1)
    | spl6_12 ),
    inference(avatar_component_clause,[],[f140])).

fof(f105,plain,
    ( v1_funct_2(sK5,sK1,sK4)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f103])).

fof(f95,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f93])).

fof(f470,plain,
    ( ~ spl6_35
    | ~ spl6_6
    | ~ spl6_8
    | spl6_30
    | ~ spl6_31 ),
    inference(avatar_split_clause,[],[f469,f412,f360,f108,f98,f453])).

fof(f360,plain,
    ( spl6_30
  <=> v1_funct_2(k7_relat_1(sK5,sK2),sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f412,plain,
    ( spl6_31
  <=> m1_subset_1(k7_relat_1(sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f469,plain,
    ( ~ v1_partfun1(k7_relat_1(sK5,sK2),sK2)
    | ~ spl6_6
    | ~ spl6_8
    | spl6_30
    | ~ spl6_31 ),
    inference(subsumption_resolution,[],[f468,f362])).

fof(f362,plain,
    ( ~ v1_funct_2(k7_relat_1(sK5,sK2),sK2,sK3)
    | spl6_30 ),
    inference(avatar_component_clause,[],[f360])).

fof(f468,plain,
    ( ~ v1_partfun1(k7_relat_1(sK5,sK2),sK2)
    | v1_funct_2(k7_relat_1(sK5,sK2),sK2,sK3)
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_31 ),
    inference(subsumption_resolution,[],[f450,f403])).

fof(f450,plain,
    ( ~ v1_partfun1(k7_relat_1(sK5,sK2),sK2)
    | ~ v1_funct_1(k7_relat_1(sK5,sK2))
    | v1_funct_2(k7_relat_1(sK5,sK2),sK2,sK3)
    | ~ spl6_31 ),
    inference(resolution,[],[f414,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

fof(f414,plain,
    ( m1_subset_1(k7_relat_1(sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f412])).

fof(f415,plain,
    ( spl6_31
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f410,f108,f98,f83,f412])).

fof(f83,plain,
    ( spl6_3
  <=> m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f410,plain,
    ( m1_subset_1(k7_relat_1(sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(forward_demodulation,[],[f84,f326])).

fof(f84,plain,
    ( m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f83])).

fof(f387,plain,
    ( ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_13
    | spl6_22 ),
    inference(avatar_contradiction_clause,[],[f386])).

fof(f386,plain,
    ( $false
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | ~ spl6_13
    | spl6_22 ),
    inference(subsumption_resolution,[],[f385,f165])).

fof(f165,plain,
    ( r1_tarski(k9_relat_1(sK5,sK2),sK3)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl6_13
  <=> r1_tarski(k9_relat_1(sK5,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f385,plain,
    ( ~ r1_tarski(k9_relat_1(sK5,sK2),sK3)
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | spl6_22 ),
    inference(forward_demodulation,[],[f384,f136])).

fof(f136,plain,
    ( ! [X0] : k2_relat_1(k7_relat_1(sK5,X0)) = k9_relat_1(sK5,X0)
    | ~ spl6_11 ),
    inference(unit_resulting_resolution,[],[f128,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f128,plain,
    ( v1_relat_1(sK5)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl6_11
  <=> v1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f384,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK5,sK2)),sK3)
    | ~ spl6_6
    | ~ spl6_8
    | spl6_22 ),
    inference(subsumption_resolution,[],[f383,f110])).

fof(f383,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK5,sK2)),sK3)
    | ~ v1_funct_1(sK5)
    | ~ spl6_6
    | spl6_22 ),
    inference(subsumption_resolution,[],[f330,f100])).

fof(f330,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK5,sK2)),sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4)))
    | ~ v1_funct_1(sK5)
    | spl6_22 ),
    inference(superposition,[],[f244,f70])).

fof(f244,plain,
    ( ~ r1_tarski(k2_relat_1(k2_partfun1(sK1,sK4,sK5,sK2)),sK3)
    | spl6_22 ),
    inference(avatar_component_clause,[],[f242])).

fof(f242,plain,
    ( spl6_22
  <=> r1_tarski(k2_relat_1(k2_partfun1(sK1,sK4,sK5,sK2)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f382,plain,
    ( ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | spl6_21 ),
    inference(avatar_contradiction_clause,[],[f381])).

fof(f381,plain,
    ( $false
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | spl6_21 ),
    inference(subsumption_resolution,[],[f380,f110])).

fof(f380,plain,
    ( ~ v1_funct_1(sK5)
    | ~ spl6_6
    | ~ spl6_11
    | spl6_21 ),
    inference(subsumption_resolution,[],[f379,f100])).

fof(f379,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4)))
    | ~ v1_funct_1(sK5)
    | ~ spl6_11
    | spl6_21 ),
    inference(subsumption_resolution,[],[f329,f134])).

fof(f134,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK5,X0)),X0)
    | ~ spl6_11 ),
    inference(unit_resulting_resolution,[],[f128,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(f329,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK5,sK2)),sK2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4)))
    | ~ v1_funct_1(sK5)
    | spl6_21 ),
    inference(superposition,[],[f240,f70])).

fof(f240,plain,
    ( ~ r1_tarski(k1_relat_1(k2_partfun1(sK1,sK4,sK5,sK2)),sK2)
    | spl6_21 ),
    inference(avatar_component_clause,[],[f238])).

fof(f238,plain,
    ( spl6_21
  <=> r1_tarski(k1_relat_1(k2_partfun1(sK1,sK4,sK5,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f378,plain,
    ( ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | spl6_20 ),
    inference(avatar_contradiction_clause,[],[f377])).

fof(f377,plain,
    ( $false
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_11
    | spl6_20 ),
    inference(subsumption_resolution,[],[f376,f110])).

fof(f376,plain,
    ( ~ v1_funct_1(sK5)
    | ~ spl6_6
    | ~ spl6_11
    | spl6_20 ),
    inference(subsumption_resolution,[],[f375,f100])).

fof(f375,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4)))
    | ~ v1_funct_1(sK5)
    | ~ spl6_6
    | ~ spl6_11
    | spl6_20 ),
    inference(subsumption_resolution,[],[f328,f184])).

fof(f184,plain,
    ( ! [X0] : v1_relat_1(k7_relat_1(sK5,X0))
    | ~ spl6_6
    | ~ spl6_11 ),
    inference(unit_resulting_resolution,[],[f54,f169,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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

fof(f169,plain,
    ( ! [X0] : m1_subset_1(k7_relat_1(sK5,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,sK4)))
    | ~ spl6_6
    | ~ spl6_11 ),
    inference(unit_resulting_resolution,[],[f132,f100,f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( r1_tarski(X0,X3)
       => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_relset_1)).

fof(f132,plain,
    ( ! [X0] : r1_tarski(k7_relat_1(sK5,X0),sK5)
    | ~ spl6_11 ),
    inference(unit_resulting_resolution,[],[f128,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

fof(f54,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

% (27575)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f328,plain,
    ( ~ v1_relat_1(k7_relat_1(sK5,sK2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4)))
    | ~ v1_funct_1(sK5)
    | spl6_20 ),
    inference(superposition,[],[f236,f70])).

fof(f236,plain,
    ( ~ v1_relat_1(k2_partfun1(sK1,sK4,sK5,sK2))
    | spl6_20 ),
    inference(avatar_component_clause,[],[f234])).

fof(f234,plain,
    ( spl6_20
  <=> v1_relat_1(k2_partfun1(sK1,sK4,sK5,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f363,plain,
    ( ~ spl6_30
    | spl6_2
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f343,f108,f98,f79,f360])).

fof(f79,plain,
    ( spl6_2
  <=> v1_funct_2(k2_partfun1(sK1,sK4,sK5,sK2),sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f343,plain,
    ( ~ v1_funct_2(k7_relat_1(sK5,sK2),sK2,sK3)
    | spl6_2
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(backward_demodulation,[],[f81,f326])).

fof(f81,plain,
    ( ~ v1_funct_2(k2_partfun1(sK1,sK4,sK5,sK2),sK2,sK3)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f79])).

fof(f245,plain,
    ( ~ spl6_20
    | ~ spl6_21
    | ~ spl6_22
    | spl6_3 ),
    inference(avatar_split_clause,[],[f230,f83,f242,f238,f234])).

fof(f230,plain,
    ( ~ r1_tarski(k2_relat_1(k2_partfun1(sK1,sK4,sK5,sK2)),sK3)
    | ~ r1_tarski(k1_relat_1(k2_partfun1(sK1,sK4,sK5,sK2)),sK2)
    | ~ v1_relat_1(k2_partfun1(sK1,sK4,sK5,sK2))
    | spl6_3 ),
    inference(resolution,[],[f60,f85])).

fof(f85,plain,
    ( ~ m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | spl6_3 ),
    inference(avatar_component_clause,[],[f83])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(f168,plain,
    ( spl6_13
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f167,f98,f88,f163])).

fof(f88,plain,
    ( spl6_4
  <=> r1_tarski(k7_relset_1(sK1,sK4,sK5,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f167,plain,
    ( r1_tarski(k9_relat_1(sK5,sK2),sK3)
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f160,f100])).

fof(f160,plain,
    ( r1_tarski(k9_relat_1(sK5,sK2),sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4)))
    | ~ spl6_4 ),
    inference(superposition,[],[f90,f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f90,plain,
    ( r1_tarski(k7_relset_1(sK1,sK4,sK5,sK2),sK3)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f88])).

fof(f157,plain,
    ( spl6_1
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(avatar_contradiction_clause,[],[f156])).

fof(f156,plain,
    ( $false
    | spl6_1
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f155,f110])).

fof(f155,plain,
    ( ~ v1_funct_1(sK5)
    | spl6_1
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f149,f100])).

fof(f149,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4)))
    | ~ v1_funct_1(sK5)
    | spl6_1 ),
    inference(resolution,[],[f71,f77])).

fof(f77,plain,
    ( ~ v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f75])).

% (27565)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
fof(f75,plain,
    ( spl6_1
  <=> v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f131,plain,
    ( spl6_11
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f130,f98,f126])).

fof(f130,plain,
    ( v1_relat_1(sK5)
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f124,f54])).

fof(f124,plain,
    ( v1_relat_1(sK5)
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK4))
    | ~ spl6_6 ),
    inference(resolution,[],[f53,f100])).

fof(f121,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f52,f118])).

fof(f118,plain,
    ( spl6_10
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f52,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f116,plain,(
    ~ spl6_9 ),
    inference(avatar_split_clause,[],[f45,f113])).

fof(f45,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      | ~ v1_funct_2(k2_partfun1(sK1,sK4,sK5,sK2),sK2,sK3)
      | ~ v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2)) )
    & r1_tarski(k7_relset_1(sK1,sK4,sK5,sK2),sK3)
    & r1_tarski(sK2,sK1)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4)))
    & v1_funct_2(sK5,sK1,sK4)
    & v1_funct_1(sK5)
    & ~ v1_xboole_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f18,f41,f40])).

fof(f40,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ( ~ m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              | ~ v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
              | ~ v1_funct_1(k2_partfun1(X0,X3,X4,X1)) )
            & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
            & r1_tarski(X1,X0)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
            & v1_funct_2(X4,X0,X3)
            & v1_funct_1(X4) )
        & ~ v1_xboole_0(X3) )
   => ( ? [X4] :
          ( ( ~ m1_subset_1(k2_partfun1(sK1,sK4,X4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
            | ~ v1_funct_2(k2_partfun1(sK1,sK4,X4,sK2),sK2,sK3)
            | ~ v1_funct_1(k2_partfun1(sK1,sK4,X4,sK2)) )
          & r1_tarski(k7_relset_1(sK1,sK4,X4,sK2),sK3)
          & r1_tarski(sK2,sK1)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4)))
          & v1_funct_2(X4,sK1,sK4)
          & v1_funct_1(X4) )
      & ~ v1_xboole_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X4] :
        ( ( ~ m1_subset_1(k2_partfun1(sK1,sK4,X4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
          | ~ v1_funct_2(k2_partfun1(sK1,sK4,X4,sK2),sK2,sK3)
          | ~ v1_funct_1(k2_partfun1(sK1,sK4,X4,sK2)) )
        & r1_tarski(k7_relset_1(sK1,sK4,X4,sK2),sK3)
        & r1_tarski(sK2,sK1)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4)))
        & v1_funct_2(X4,sK1,sK4)
        & v1_funct_1(X4) )
   => ( ( ~ m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
        | ~ v1_funct_2(k2_partfun1(sK1,sK4,sK5,sK2),sK2,sK3)
        | ~ v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2)) )
      & r1_tarski(k7_relset_1(sK1,sK4,sK5,sK2),sK3)
      & r1_tarski(sK2,sK1)
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4)))
      & v1_funct_2(sK5,sK1,sK4)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ~ m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            | ~ v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
            | ~ v1_funct_1(k2_partfun1(X0,X3,X4,X1)) )
          & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
          & r1_tarski(X1,X0)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
          & v1_funct_2(X4,X0,X3)
          & v1_funct_1(X4) )
      & ~ v1_xboole_0(X3) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ~ m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            | ~ v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
            | ~ v1_funct_1(k2_partfun1(X0,X3,X4,X1)) )
          & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
          & r1_tarski(X1,X0)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
          & v1_funct_2(X4,X0,X3)
          & v1_funct_1(X4) )
      & ~ v1_xboole_0(X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ~ v1_xboole_0(X3)
       => ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
              & v1_funct_2(X4,X0,X3)
              & v1_funct_1(X4) )
           => ( ( r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
                & r1_tarski(X1,X0) )
             => ( m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
                & v1_funct_1(k2_partfun1(X0,X3,X4,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ~ v1_xboole_0(X3)
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
            & v1_funct_2(X4,X0,X3)
            & v1_funct_1(X4) )
         => ( ( r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
              & r1_tarski(X1,X0) )
           => ( m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
              & v1_funct_1(k2_partfun1(X0,X3,X4,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_funct_2)).

fof(f111,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f46,f108])).

fof(f46,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f42])).

fof(f106,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f47,f103])).

fof(f47,plain,(
    v1_funct_2(sK5,sK1,sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f101,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f48,f98])).

fof(f48,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) ),
    inference(cnf_transformation,[],[f42])).

fof(f96,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f49,f93])).

fof(f49,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f91,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f50,f88])).

fof(f50,plain,(
    r1_tarski(k7_relset_1(sK1,sK4,sK5,sK2),sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f86,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f51,f83,f79,f75])).

fof(f51,plain,
    ( ~ m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_2(k2_partfun1(sK1,sK4,sK5,sK2),sK2,sK3)
    | ~ v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2)) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:52:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.46  % (27581)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.47  % (27572)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.48  % (27567)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.48  % (27569)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.49  % (27578)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.49  % (27571)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.49  % (27576)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.50  % (27581)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % (27568)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f674,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f86,f91,f96,f101,f106,f111,f116,f121,f131,f157,f168,f245,f363,f378,f382,f387,f415,f470,f603,f636,f669,f670,f673])).
% 0.20/0.50  fof(f673,plain,(
% 0.20/0.50    ~spl6_6 | ~spl6_8 | spl6_9 | spl6_35 | ~spl6_55 | ~spl6_56),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f672])).
% 0.20/0.50  fof(f672,plain,(
% 0.20/0.50    $false | (~spl6_6 | ~spl6_8 | spl6_9 | spl6_35 | ~spl6_55 | ~spl6_56)),
% 0.20/0.50    inference(subsumption_resolution,[],[f671,f668])).
% 0.20/0.50  fof(f668,plain,(
% 0.20/0.50    m1_subset_1(k7_relat_1(sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) | ~spl6_56),
% 0.20/0.50    inference(avatar_component_clause,[],[f666])).
% 0.20/0.50  fof(f666,plain,(
% 0.20/0.50    spl6_56 <=> m1_subset_1(k7_relat_1(sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_56])])).
% 0.20/0.50  fof(f671,plain,(
% 0.20/0.50    ~m1_subset_1(k7_relat_1(sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) | (~spl6_6 | ~spl6_8 | spl6_9 | spl6_35 | ~spl6_55)),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f115,f403,f455,f662,f56])).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_partfun1(X2,X0) | v1_xboole_0(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.20/0.50    inference(flattening,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,axiom,(
% 0.20/0.50    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.20/0.50  fof(f662,plain,(
% 0.20/0.50    v1_funct_2(k7_relat_1(sK5,sK2),sK2,sK4) | ~spl6_55),
% 0.20/0.50    inference(avatar_component_clause,[],[f660])).
% 0.20/0.50  fof(f660,plain,(
% 0.20/0.50    spl6_55 <=> v1_funct_2(k7_relat_1(sK5,sK2),sK2,sK4)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_55])])).
% 0.20/0.50  fof(f455,plain,(
% 0.20/0.50    ~v1_partfun1(k7_relat_1(sK5,sK2),sK2) | spl6_35),
% 0.20/0.50    inference(avatar_component_clause,[],[f453])).
% 0.20/0.50  fof(f453,plain,(
% 0.20/0.50    spl6_35 <=> v1_partfun1(k7_relat_1(sK5,sK2),sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).
% 0.20/0.50  fof(f403,plain,(
% 0.20/0.50    ( ! [X4] : (v1_funct_1(k7_relat_1(sK5,X4))) ) | (~spl6_6 | ~spl6_8)),
% 0.20/0.50    inference(subsumption_resolution,[],[f402,f110])).
% 0.20/0.50  fof(f110,plain,(
% 0.20/0.50    v1_funct_1(sK5) | ~spl6_8),
% 0.20/0.50    inference(avatar_component_clause,[],[f108])).
% 0.20/0.50  fof(f108,plain,(
% 0.20/0.50    spl6_8 <=> v1_funct_1(sK5)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.20/0.50  fof(f402,plain,(
% 0.20/0.50    ( ! [X4] : (v1_funct_1(k7_relat_1(sK5,X4)) | ~v1_funct_1(sK5)) ) | (~spl6_6 | ~spl6_8)),
% 0.20/0.50    inference(subsumption_resolution,[],[f337,f100])).
% 0.20/0.50  fof(f100,plain,(
% 0.20/0.50    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) | ~spl6_6),
% 0.20/0.50    inference(avatar_component_clause,[],[f98])).
% 0.20/0.50  fof(f98,plain,(
% 0.20/0.50    spl6_6 <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.20/0.50  fof(f337,plain,(
% 0.20/0.50    ( ! [X4] : (v1_funct_1(k7_relat_1(sK5,X4)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) | ~v1_funct_1(sK5)) ) | (~spl6_6 | ~spl6_8)),
% 0.20/0.50    inference(superposition,[],[f146,f70])).
% 0.20/0.50  fof(f70,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.20/0.50    inference(flattening,[],[f34])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.20/0.50    inference(ennf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,axiom,(
% 0.20/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.20/0.50  fof(f146,plain,(
% 0.20/0.50    ( ! [X0] : (v1_funct_1(k2_partfun1(sK1,sK4,sK5,X0))) ) | (~spl6_6 | ~spl6_8)),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f110,f100,f71])).
% 0.20/0.50  fof(f71,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f37])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.20/0.50    inference(flattening,[],[f36])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.20/0.50    inference(ennf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,axiom,(
% 0.20/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 0.20/0.50  fof(f115,plain,(
% 0.20/0.50    ~v1_xboole_0(sK4) | spl6_9),
% 0.20/0.50    inference(avatar_component_clause,[],[f113])).
% 0.20/0.50  fof(f113,plain,(
% 0.20/0.50    spl6_9 <=> v1_xboole_0(sK4)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.20/0.50  fof(f670,plain,(
% 0.20/0.50    spl6_55 | ~spl6_6 | ~spl6_8 | ~spl6_12),
% 0.20/0.50    inference(avatar_split_clause,[],[f653,f140,f108,f98,f660])).
% 0.20/0.50  fof(f140,plain,(
% 0.20/0.50    spl6_12 <=> sP0(sK4,sK2,sK5,sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.20/0.50  fof(f653,plain,(
% 0.20/0.50    v1_funct_2(k7_relat_1(sK5,sK2),sK2,sK4) | (~spl6_6 | ~spl6_8 | ~spl6_12)),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f141,f490])).
% 0.20/0.50  fof(f490,plain,(
% 0.20/0.50    ( ! [X4] : (v1_funct_2(k7_relat_1(sK5,X4),X4,sK4) | ~sP0(sK4,X4,sK5,sK1)) ) | (~spl6_6 | ~spl6_8)),
% 0.20/0.50    inference(superposition,[],[f66,f326])).
% 0.20/0.50  fof(f326,plain,(
% 0.20/0.50    ( ! [X0] : (k7_relat_1(sK5,X0) = k2_partfun1(sK1,sK4,sK5,X0)) ) | (~spl6_6 | ~spl6_8)),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f110,f100,f70])).
% 0.20/0.50  fof(f66,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (v1_funct_2(k2_partfun1(X3,X0,X2,X1),X1,X0) | ~sP0(X0,X1,X2,X3)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f44])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_partfun1(X3,X0,X2,X1),X1,X0) & v1_funct_1(k2_partfun1(X3,X0,X2,X1))) | ~sP0(X0,X1,X2,X3))),
% 0.20/0.50    inference(rectify,[],[f43])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ! [X1,X2,X3,X0] : ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | ~sP0(X1,X2,X3,X0))),
% 0.20/0.50    inference(nnf_transformation,[],[f38])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ! [X1,X2,X3,X0] : ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | ~sP0(X1,X2,X3,X0))),
% 0.20/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.50  fof(f141,plain,(
% 0.20/0.50    sP0(sK4,sK2,sK5,sK1) | ~spl6_12),
% 0.20/0.50    inference(avatar_component_clause,[],[f140])).
% 0.20/0.50  fof(f669,plain,(
% 0.20/0.50    spl6_56 | ~spl6_6 | ~spl6_8 | ~spl6_12),
% 0.20/0.50    inference(avatar_split_clause,[],[f664,f140,f108,f98,f666])).
% 0.20/0.50  fof(f664,plain,(
% 0.20/0.50    m1_subset_1(k7_relat_1(sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) | (~spl6_6 | ~spl6_8 | ~spl6_12)),
% 0.20/0.50    inference(forward_demodulation,[],[f654,f326])).
% 0.20/0.50  fof(f654,plain,(
% 0.20/0.50    m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) | ~spl6_12),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f141,f67])).
% 0.20/0.50  fof(f67,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~sP0(X0,X1,X2,X3)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f44])).
% 0.20/0.50  fof(f636,plain,(
% 0.20/0.50    k1_xboole_0 != sK4 | v1_xboole_0(sK4) | ~v1_xboole_0(k1_xboole_0)),
% 0.20/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.50  fof(f603,plain,(
% 0.20/0.50    spl6_46 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | spl6_12),
% 0.20/0.50    inference(avatar_split_clause,[],[f586,f140,f108,f103,f98,f93,f600])).
% 0.20/0.50  fof(f600,plain,(
% 0.20/0.50    spl6_46 <=> k1_xboole_0 = sK4),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).
% 0.20/0.50  fof(f93,plain,(
% 0.20/0.50    spl6_5 <=> r1_tarski(sK2,sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.20/0.50  fof(f103,plain,(
% 0.20/0.50    spl6_7 <=> v1_funct_2(sK5,sK1,sK4)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.20/0.50  fof(f586,plain,(
% 0.20/0.50    k1_xboole_0 = sK4 | (~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | spl6_12)),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f110,f95,f105,f142,f100,f68])).
% 0.20/0.50  fof(f68,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~r1_tarski(X2,X0) | sP0(X1,X2,X3,X0) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (sP0(X1,X2,X3,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.20/0.50    inference(definition_folding,[],[f33,f38])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.20/0.50    inference(flattening,[],[f32])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : ((((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.20/0.50    inference(ennf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,axiom,(
% 0.20/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).
% 0.20/0.50  fof(f142,plain,(
% 0.20/0.50    ~sP0(sK4,sK2,sK5,sK1) | spl6_12),
% 0.20/0.50    inference(avatar_component_clause,[],[f140])).
% 0.20/0.50  fof(f105,plain,(
% 0.20/0.50    v1_funct_2(sK5,sK1,sK4) | ~spl6_7),
% 0.20/0.50    inference(avatar_component_clause,[],[f103])).
% 0.20/0.50  fof(f95,plain,(
% 0.20/0.50    r1_tarski(sK2,sK1) | ~spl6_5),
% 0.20/0.50    inference(avatar_component_clause,[],[f93])).
% 0.20/0.50  fof(f470,plain,(
% 0.20/0.50    ~spl6_35 | ~spl6_6 | ~spl6_8 | spl6_30 | ~spl6_31),
% 0.20/0.50    inference(avatar_split_clause,[],[f469,f412,f360,f108,f98,f453])).
% 0.20/0.50  fof(f360,plain,(
% 0.20/0.50    spl6_30 <=> v1_funct_2(k7_relat_1(sK5,sK2),sK2,sK3)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 0.20/0.50  fof(f412,plain,(
% 0.20/0.50    spl6_31 <=> m1_subset_1(k7_relat_1(sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 0.20/0.50  fof(f469,plain,(
% 0.20/0.50    ~v1_partfun1(k7_relat_1(sK5,sK2),sK2) | (~spl6_6 | ~spl6_8 | spl6_30 | ~spl6_31)),
% 0.20/0.50    inference(subsumption_resolution,[],[f468,f362])).
% 0.20/0.50  fof(f362,plain,(
% 0.20/0.50    ~v1_funct_2(k7_relat_1(sK5,sK2),sK2,sK3) | spl6_30),
% 0.20/0.50    inference(avatar_component_clause,[],[f360])).
% 0.20/0.50  fof(f468,plain,(
% 0.20/0.50    ~v1_partfun1(k7_relat_1(sK5,sK2),sK2) | v1_funct_2(k7_relat_1(sK5,sK2),sK2,sK3) | (~spl6_6 | ~spl6_8 | ~spl6_31)),
% 0.20/0.50    inference(subsumption_resolution,[],[f450,f403])).
% 0.20/0.50  fof(f450,plain,(
% 0.20/0.50    ~v1_partfun1(k7_relat_1(sK5,sK2),sK2) | ~v1_funct_1(k7_relat_1(sK5,sK2)) | v1_funct_2(k7_relat_1(sK5,sK2),sK2,sK3) | ~spl6_31),
% 0.20/0.50    inference(resolution,[],[f414,f62])).
% 0.20/0.50  fof(f62,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | v1_funct_2(X2,X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f28])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(flattening,[],[f27])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).
% 0.20/0.50  fof(f414,plain,(
% 0.20/0.50    m1_subset_1(k7_relat_1(sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~spl6_31),
% 0.20/0.50    inference(avatar_component_clause,[],[f412])).
% 0.20/0.50  fof(f415,plain,(
% 0.20/0.50    spl6_31 | ~spl6_3 | ~spl6_6 | ~spl6_8),
% 0.20/0.50    inference(avatar_split_clause,[],[f410,f108,f98,f83,f412])).
% 0.20/0.50  fof(f83,plain,(
% 0.20/0.50    spl6_3 <=> m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.50  fof(f410,plain,(
% 0.20/0.50    m1_subset_1(k7_relat_1(sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | (~spl6_3 | ~spl6_6 | ~spl6_8)),
% 0.20/0.50    inference(forward_demodulation,[],[f84,f326])).
% 0.20/0.50  fof(f84,plain,(
% 0.20/0.50    m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~spl6_3),
% 0.20/0.50    inference(avatar_component_clause,[],[f83])).
% 0.20/0.50  fof(f387,plain,(
% 0.20/0.50    ~spl6_6 | ~spl6_8 | ~spl6_11 | ~spl6_13 | spl6_22),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f386])).
% 0.20/0.50  fof(f386,plain,(
% 0.20/0.50    $false | (~spl6_6 | ~spl6_8 | ~spl6_11 | ~spl6_13 | spl6_22)),
% 0.20/0.50    inference(subsumption_resolution,[],[f385,f165])).
% 0.20/0.50  fof(f165,plain,(
% 0.20/0.50    r1_tarski(k9_relat_1(sK5,sK2),sK3) | ~spl6_13),
% 0.20/0.50    inference(avatar_component_clause,[],[f163])).
% 0.20/0.50  fof(f163,plain,(
% 0.20/0.50    spl6_13 <=> r1_tarski(k9_relat_1(sK5,sK2),sK3)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.20/0.50  fof(f385,plain,(
% 0.20/0.50    ~r1_tarski(k9_relat_1(sK5,sK2),sK3) | (~spl6_6 | ~spl6_8 | ~spl6_11 | spl6_22)),
% 0.20/0.50    inference(forward_demodulation,[],[f384,f136])).
% 0.20/0.50  fof(f136,plain,(
% 0.20/0.50    ( ! [X0] : (k2_relat_1(k7_relat_1(sK5,X0)) = k9_relat_1(sK5,X0)) ) | ~spl6_11),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f128,f59])).
% 0.20/0.50  fof(f59,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.20/0.50  fof(f128,plain,(
% 0.20/0.50    v1_relat_1(sK5) | ~spl6_11),
% 0.20/0.50    inference(avatar_component_clause,[],[f126])).
% 0.20/0.50  fof(f126,plain,(
% 0.20/0.50    spl6_11 <=> v1_relat_1(sK5)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.20/0.50  fof(f384,plain,(
% 0.20/0.50    ~r1_tarski(k2_relat_1(k7_relat_1(sK5,sK2)),sK3) | (~spl6_6 | ~spl6_8 | spl6_22)),
% 0.20/0.50    inference(subsumption_resolution,[],[f383,f110])).
% 0.20/0.50  fof(f383,plain,(
% 0.20/0.50    ~r1_tarski(k2_relat_1(k7_relat_1(sK5,sK2)),sK3) | ~v1_funct_1(sK5) | (~spl6_6 | spl6_22)),
% 0.20/0.50    inference(subsumption_resolution,[],[f330,f100])).
% 0.20/0.50  fof(f330,plain,(
% 0.20/0.50    ~r1_tarski(k2_relat_1(k7_relat_1(sK5,sK2)),sK3) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) | ~v1_funct_1(sK5) | spl6_22),
% 0.20/0.50    inference(superposition,[],[f244,f70])).
% 0.20/0.50  fof(f244,plain,(
% 0.20/0.50    ~r1_tarski(k2_relat_1(k2_partfun1(sK1,sK4,sK5,sK2)),sK3) | spl6_22),
% 0.20/0.50    inference(avatar_component_clause,[],[f242])).
% 0.20/0.50  fof(f242,plain,(
% 0.20/0.50    spl6_22 <=> r1_tarski(k2_relat_1(k2_partfun1(sK1,sK4,sK5,sK2)),sK3)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 0.20/0.50  fof(f382,plain,(
% 0.20/0.50    ~spl6_6 | ~spl6_8 | ~spl6_11 | spl6_21),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f381])).
% 0.20/0.50  fof(f381,plain,(
% 0.20/0.50    $false | (~spl6_6 | ~spl6_8 | ~spl6_11 | spl6_21)),
% 0.20/0.50    inference(subsumption_resolution,[],[f380,f110])).
% 0.20/0.50  fof(f380,plain,(
% 0.20/0.50    ~v1_funct_1(sK5) | (~spl6_6 | ~spl6_11 | spl6_21)),
% 0.20/0.50    inference(subsumption_resolution,[],[f379,f100])).
% 0.20/0.50  fof(f379,plain,(
% 0.20/0.50    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) | ~v1_funct_1(sK5) | (~spl6_11 | spl6_21)),
% 0.20/0.50    inference(subsumption_resolution,[],[f329,f134])).
% 0.20/0.50  fof(f134,plain,(
% 0.20/0.50    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK5,X0)),X0)) ) | ~spl6_11),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f128,f58])).
% 0.20/0.50  fof(f58,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).
% 0.20/0.50  fof(f329,plain,(
% 0.20/0.50    ~r1_tarski(k1_relat_1(k7_relat_1(sK5,sK2)),sK2) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) | ~v1_funct_1(sK5) | spl6_21),
% 0.20/0.50    inference(superposition,[],[f240,f70])).
% 0.20/0.50  fof(f240,plain,(
% 0.20/0.50    ~r1_tarski(k1_relat_1(k2_partfun1(sK1,sK4,sK5,sK2)),sK2) | spl6_21),
% 0.20/0.50    inference(avatar_component_clause,[],[f238])).
% 0.20/0.50  fof(f238,plain,(
% 0.20/0.50    spl6_21 <=> r1_tarski(k1_relat_1(k2_partfun1(sK1,sK4,sK5,sK2)),sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.20/0.50  fof(f378,plain,(
% 0.20/0.50    ~spl6_6 | ~spl6_8 | ~spl6_11 | spl6_20),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f377])).
% 0.20/0.50  fof(f377,plain,(
% 0.20/0.50    $false | (~spl6_6 | ~spl6_8 | ~spl6_11 | spl6_20)),
% 0.20/0.50    inference(subsumption_resolution,[],[f376,f110])).
% 0.20/0.50  fof(f376,plain,(
% 0.20/0.50    ~v1_funct_1(sK5) | (~spl6_6 | ~spl6_11 | spl6_20)),
% 0.20/0.50    inference(subsumption_resolution,[],[f375,f100])).
% 0.20/0.50  fof(f375,plain,(
% 0.20/0.50    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) | ~v1_funct_1(sK5) | (~spl6_6 | ~spl6_11 | spl6_20)),
% 0.20/0.50    inference(subsumption_resolution,[],[f328,f184])).
% 0.20/0.50  fof(f184,plain,(
% 0.20/0.50    ( ! [X0] : (v1_relat_1(k7_relat_1(sK5,X0))) ) | (~spl6_6 | ~spl6_11)),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f54,f169,f53])).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.50  fof(f169,plain,(
% 0.20/0.50    ( ! [X0] : (m1_subset_1(k7_relat_1(sK5,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,sK4)))) ) | (~spl6_6 | ~spl6_11)),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f132,f100,f64])).
% 0.20/0.50  fof(f64,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.20/0.50    inference(flattening,[],[f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.20/0.50    inference(ennf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,axiom,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => (r1_tarski(X0,X3) => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_relset_1)).
% 0.20/0.50  fof(f132,plain,(
% 0.20/0.50    ( ! [X0] : (r1_tarski(k7_relat_1(sK5,X0),sK5)) ) | ~spl6_11),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f128,f57])).
% 0.20/0.50  fof(f57,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f3])).
% 0.20/0.50  % (27575)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.50  fof(f328,plain,(
% 0.20/0.50    ~v1_relat_1(k7_relat_1(sK5,sK2)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) | ~v1_funct_1(sK5) | spl6_20),
% 0.20/0.50    inference(superposition,[],[f236,f70])).
% 0.20/0.50  fof(f236,plain,(
% 0.20/0.50    ~v1_relat_1(k2_partfun1(sK1,sK4,sK5,sK2)) | spl6_20),
% 0.20/0.50    inference(avatar_component_clause,[],[f234])).
% 0.20/0.50  fof(f234,plain,(
% 0.20/0.50    spl6_20 <=> v1_relat_1(k2_partfun1(sK1,sK4,sK5,sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.20/0.50  fof(f363,plain,(
% 0.20/0.50    ~spl6_30 | spl6_2 | ~spl6_6 | ~spl6_8),
% 0.20/0.50    inference(avatar_split_clause,[],[f343,f108,f98,f79,f360])).
% 0.20/0.50  fof(f79,plain,(
% 0.20/0.50    spl6_2 <=> v1_funct_2(k2_partfun1(sK1,sK4,sK5,sK2),sK2,sK3)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.50  fof(f343,plain,(
% 0.20/0.50    ~v1_funct_2(k7_relat_1(sK5,sK2),sK2,sK3) | (spl6_2 | ~spl6_6 | ~spl6_8)),
% 0.20/0.50    inference(backward_demodulation,[],[f81,f326])).
% 0.20/0.50  fof(f81,plain,(
% 0.20/0.50    ~v1_funct_2(k2_partfun1(sK1,sK4,sK5,sK2),sK2,sK3) | spl6_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f79])).
% 0.20/0.50  fof(f245,plain,(
% 0.20/0.50    ~spl6_20 | ~spl6_21 | ~spl6_22 | spl6_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f230,f83,f242,f238,f234])).
% 0.20/0.50  fof(f230,plain,(
% 0.20/0.50    ~r1_tarski(k2_relat_1(k2_partfun1(sK1,sK4,sK5,sK2)),sK3) | ~r1_tarski(k1_relat_1(k2_partfun1(sK1,sK4,sK5,sK2)),sK2) | ~v1_relat_1(k2_partfun1(sK1,sK4,sK5,sK2)) | spl6_3),
% 0.20/0.50    inference(resolution,[],[f60,f85])).
% 0.20/0.50  fof(f85,plain,(
% 0.20/0.50    ~m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | spl6_3),
% 0.20/0.50    inference(avatar_component_clause,[],[f83])).
% 0.20/0.50  fof(f60,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.20/0.50    inference(flattening,[],[f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 0.20/0.50  fof(f168,plain,(
% 0.20/0.50    spl6_13 | ~spl6_4 | ~spl6_6),
% 0.20/0.50    inference(avatar_split_clause,[],[f167,f98,f88,f163])).
% 0.20/0.50  fof(f88,plain,(
% 0.20/0.50    spl6_4 <=> r1_tarski(k7_relset_1(sK1,sK4,sK5,sK2),sK3)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.20/0.50  fof(f167,plain,(
% 0.20/0.50    r1_tarski(k9_relat_1(sK5,sK2),sK3) | (~spl6_4 | ~spl6_6)),
% 0.20/0.50    inference(subsumption_resolution,[],[f160,f100])).
% 0.20/0.50  fof(f160,plain,(
% 0.20/0.50    r1_tarski(k9_relat_1(sK5,sK2),sK3) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) | ~spl6_4),
% 0.20/0.50    inference(superposition,[],[f90,f63])).
% 0.20/0.50  fof(f63,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f29])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.20/0.50  fof(f90,plain,(
% 0.20/0.50    r1_tarski(k7_relset_1(sK1,sK4,sK5,sK2),sK3) | ~spl6_4),
% 0.20/0.50    inference(avatar_component_clause,[],[f88])).
% 0.20/0.50  fof(f157,plain,(
% 0.20/0.50    spl6_1 | ~spl6_6 | ~spl6_8),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f156])).
% 0.20/0.50  fof(f156,plain,(
% 0.20/0.50    $false | (spl6_1 | ~spl6_6 | ~spl6_8)),
% 0.20/0.50    inference(subsumption_resolution,[],[f155,f110])).
% 0.20/0.50  fof(f155,plain,(
% 0.20/0.50    ~v1_funct_1(sK5) | (spl6_1 | ~spl6_6)),
% 0.20/0.50    inference(subsumption_resolution,[],[f149,f100])).
% 0.20/0.50  fof(f149,plain,(
% 0.20/0.50    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) | ~v1_funct_1(sK5) | spl6_1),
% 0.20/0.50    inference(resolution,[],[f71,f77])).
% 0.20/0.50  fof(f77,plain,(
% 0.20/0.50    ~v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2)) | spl6_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f75])).
% 0.20/0.50  % (27565)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.50  fof(f75,plain,(
% 0.20/0.50    spl6_1 <=> v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.50  fof(f131,plain,(
% 0.20/0.50    spl6_11 | ~spl6_6),
% 0.20/0.50    inference(avatar_split_clause,[],[f130,f98,f126])).
% 0.20/0.50  fof(f130,plain,(
% 0.20/0.50    v1_relat_1(sK5) | ~spl6_6),
% 0.20/0.50    inference(subsumption_resolution,[],[f124,f54])).
% 0.20/0.50  fof(f124,plain,(
% 0.20/0.50    v1_relat_1(sK5) | ~v1_relat_1(k2_zfmisc_1(sK1,sK4)) | ~spl6_6),
% 0.20/0.50    inference(resolution,[],[f53,f100])).
% 0.20/0.50  fof(f121,plain,(
% 0.20/0.50    spl6_10),
% 0.20/0.50    inference(avatar_split_clause,[],[f52,f118])).
% 0.20/0.51  fof(f118,plain,(
% 0.20/0.51    spl6_10 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    v1_xboole_0(k1_xboole_0)),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    v1_xboole_0(k1_xboole_0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.51  fof(f116,plain,(
% 0.20/0.51    ~spl6_9),
% 0.20/0.51    inference(avatar_split_clause,[],[f45,f113])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ~v1_xboole_0(sK4)),
% 0.20/0.51    inference(cnf_transformation,[],[f42])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ((~m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~v1_funct_2(k2_partfun1(sK1,sK4,sK5,sK2),sK2,sK3) | ~v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2))) & r1_tarski(k7_relset_1(sK1,sK4,sK5,sK2),sK3) & r1_tarski(sK2,sK1) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) & v1_funct_2(sK5,sK1,sK4) & v1_funct_1(sK5)) & ~v1_xboole_0(sK4)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f18,f41,f40])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ? [X0,X1,X2,X3] : (? [X4] : ((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) & ~v1_xboole_0(X3)) => (? [X4] : ((~m1_subset_1(k2_partfun1(sK1,sK4,X4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~v1_funct_2(k2_partfun1(sK1,sK4,X4,sK2),sK2,sK3) | ~v1_funct_1(k2_partfun1(sK1,sK4,X4,sK2))) & r1_tarski(k7_relset_1(sK1,sK4,X4,sK2),sK3) & r1_tarski(sK2,sK1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) & v1_funct_2(X4,sK1,sK4) & v1_funct_1(X4)) & ~v1_xboole_0(sK4))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ? [X4] : ((~m1_subset_1(k2_partfun1(sK1,sK4,X4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~v1_funct_2(k2_partfun1(sK1,sK4,X4,sK2),sK2,sK3) | ~v1_funct_1(k2_partfun1(sK1,sK4,X4,sK2))) & r1_tarski(k7_relset_1(sK1,sK4,X4,sK2),sK3) & r1_tarski(sK2,sK1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) & v1_funct_2(X4,sK1,sK4) & v1_funct_1(X4)) => ((~m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~v1_funct_2(k2_partfun1(sK1,sK4,sK5,sK2),sK2,sK3) | ~v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2))) & r1_tarski(k7_relset_1(sK1,sK4,sK5,sK2),sK3) & r1_tarski(sK2,sK1) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4))) & v1_funct_2(sK5,sK1,sK4) & v1_funct_1(sK5))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ? [X0,X1,X2,X3] : (? [X4] : ((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) & ~v1_xboole_0(X3))),
% 0.20/0.51    inference(flattening,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ? [X0,X1,X2,X3] : (? [X4] : (((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & (r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4))) & ~v1_xboole_0(X3))),
% 0.20/0.51    inference(ennf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1,X2,X3] : (~v1_xboole_0(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0)) => (m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))))))),
% 0.20/0.51    inference(negated_conjecture,[],[f15])).
% 0.20/0.51  fof(f15,conjecture,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (~v1_xboole_0(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0)) => (m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_funct_2)).
% 0.20/0.51  fof(f111,plain,(
% 0.20/0.51    spl6_8),
% 0.20/0.51    inference(avatar_split_clause,[],[f46,f108])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    v1_funct_1(sK5)),
% 0.20/0.51    inference(cnf_transformation,[],[f42])).
% 0.20/0.51  fof(f106,plain,(
% 0.20/0.51    spl6_7),
% 0.20/0.51    inference(avatar_split_clause,[],[f47,f103])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    v1_funct_2(sK5,sK1,sK4)),
% 0.20/0.51    inference(cnf_transformation,[],[f42])).
% 0.20/0.51  fof(f101,plain,(
% 0.20/0.51    spl6_6),
% 0.20/0.51    inference(avatar_split_clause,[],[f48,f98])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK1,sK4)))),
% 0.20/0.51    inference(cnf_transformation,[],[f42])).
% 0.20/0.51  fof(f96,plain,(
% 0.20/0.51    spl6_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f49,f93])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    r1_tarski(sK2,sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f42])).
% 0.20/0.51  fof(f91,plain,(
% 0.20/0.51    spl6_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f50,f88])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    r1_tarski(k7_relset_1(sK1,sK4,sK5,sK2),sK3)),
% 0.20/0.51    inference(cnf_transformation,[],[f42])).
% 0.20/0.51  fof(f86,plain,(
% 0.20/0.51    ~spl6_1 | ~spl6_2 | ~spl6_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f51,f83,f79,f75])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    ~m1_subset_1(k2_partfun1(sK1,sK4,sK5,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) | ~v1_funct_2(k2_partfun1(sK1,sK4,sK5,sK2),sK2,sK3) | ~v1_funct_1(k2_partfun1(sK1,sK4,sK5,sK2))),
% 0.20/0.51    inference(cnf_transformation,[],[f42])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (27581)------------------------------
% 0.20/0.51  % (27581)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (27581)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (27581)Memory used [KB]: 11257
% 0.20/0.51  % (27581)Time elapsed: 0.076 s
% 0.20/0.51  % (27581)------------------------------
% 0.20/0.51  % (27581)------------------------------
% 0.20/0.51  % (27580)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.51  % (27570)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.51  % (27564)Success in time 0.145 s
%------------------------------------------------------------------------------
