%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:21 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 138 expanded)
%              Number of leaves         :   20 (  54 expanded)
%              Depth                    :   10
%              Number of atoms          :  269 ( 434 expanded)
%              Number of equality atoms :   60 (  81 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f379,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f62,f67,f76,f89,f157,f199,f249,f309,f324,f377])).

fof(f377,plain,
    ( ~ spl4_6
    | ~ spl4_10
    | ~ spl4_22 ),
    inference(avatar_contradiction_clause,[],[f376])).

fof(f376,plain,
    ( $false
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f375,f48])).

fof(f48,plain,(
    ! [X1] : ~ sP0(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f375,plain,
    ( sP0(k1_xboole_0,k1_xboole_0)
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_22 ),
    inference(forward_demodulation,[],[f374,f101])).

fof(f101,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl4_6
  <=> k1_xboole_0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f374,plain,
    ( sP0(k1_relat_1(sK3),k1_xboole_0)
    | ~ spl4_10
    | ~ spl4_22 ),
    inference(forward_demodulation,[],[f322,f135])).

fof(f135,plain,
    ( k1_xboole_0 = k2_relat_1(sK3)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl4_10
  <=> k1_xboole_0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f322,plain,
    ( sP0(k1_relat_1(sK3),k2_relat_1(sK3))
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f320])).

fof(f320,plain,
    ( spl4_22
  <=> sP0(k1_relat_1(sK3),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f324,plain,
    ( spl4_22
    | spl4_2
    | ~ spl4_18
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f289,f246,f195,f54,f320])).

fof(f54,plain,
    ( spl4_2
  <=> v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f195,plain,
    ( spl4_18
  <=> sP1(k1_relat_1(sK3),sK3,k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f246,plain,
    ( spl4_20
  <=> k1_relat_1(sK3) = k1_relset_1(k1_relat_1(sK3),k2_relat_1(sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f289,plain,
    ( sP0(k1_relat_1(sK3),k2_relat_1(sK3))
    | spl4_2
    | ~ spl4_18
    | ~ spl4_20 ),
    inference(unit_resulting_resolution,[],[f197,f56,f248,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) != X0
      | v1_funct_2(X1,X0,X2)
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f248,plain,
    ( k1_relat_1(sK3) = k1_relset_1(k1_relat_1(sK3),k2_relat_1(sK3),sK3)
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f246])).

fof(f56,plain,
    ( ~ v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f197,plain,
    ( sP1(k1_relat_1(sK3),sK3,k2_relat_1(sK3))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f195])).

fof(f309,plain,
    ( spl4_2
    | spl4_10
    | ~ spl4_18
    | ~ spl4_20 ),
    inference(avatar_contradiction_clause,[],[f308])).

fof(f308,plain,
    ( $false
    | spl4_2
    | spl4_10
    | ~ spl4_18
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f307,f197])).

fof(f307,plain,
    ( ~ sP1(k1_relat_1(sK3),sK3,k2_relat_1(sK3))
    | spl4_2
    | spl4_10
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f306,f175])).

fof(f175,plain,
    ( ! [X0] : ~ sP0(X0,k2_relat_1(sK3))
    | spl4_10 ),
    inference(unit_resulting_resolution,[],[f136,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f136,plain,
    ( k1_xboole_0 != k2_relat_1(sK3)
    | spl4_10 ),
    inference(avatar_component_clause,[],[f134])).

fof(f306,plain,
    ( sP0(k1_relat_1(sK3),k2_relat_1(sK3))
    | ~ sP1(k1_relat_1(sK3),sK3,k2_relat_1(sK3))
    | spl4_2
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f294,f56])).

fof(f294,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3))
    | sP0(k1_relat_1(sK3),k2_relat_1(sK3))
    | ~ sP1(k1_relat_1(sK3),sK3,k2_relat_1(sK3))
    | ~ spl4_20 ),
    inference(trivial_inequality_removal,[],[f293])).

fof(f293,plain,
    ( k1_relat_1(sK3) != k1_relat_1(sK3)
    | v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3))
    | sP0(k1_relat_1(sK3),k2_relat_1(sK3))
    | ~ sP1(k1_relat_1(sK3),sK3,k2_relat_1(sK3))
    | ~ spl4_20 ),
    inference(superposition,[],[f40,f248])).

fof(f249,plain,
    ( spl4_20
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f244,f58,f246])).

fof(f58,plain,
    ( spl4_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f244,plain,
    ( k1_relat_1(sK3) = k1_relset_1(k1_relat_1(sK3),k2_relat_1(sK3),sK3)
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f59,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f59,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f199,plain,
    ( spl4_18
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f193,f58,f195])).

fof(f193,plain,
    ( sP1(k1_relat_1(sK3),sK3,k2_relat_1(sK3))
    | ~ spl4_3 ),
    inference(resolution,[],[f43,f59])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X2,X1,X0)
        & sP1(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f14,f17,f16,f15])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP2(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f157,plain,
    ( ~ spl4_10
    | ~ spl4_4
    | spl4_6 ),
    inference(avatar_split_clause,[],[f156,f100,f64,f134])).

fof(f64,plain,
    ( spl4_4
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f156,plain,
    ( k1_xboole_0 != k2_relat_1(sK3)
    | ~ spl4_4
    | spl4_6 ),
    inference(subsumption_resolution,[],[f132,f66])).

fof(f66,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f64])).

fof(f132,plain,
    ( k1_xboole_0 != k2_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl4_6 ),
    inference(trivial_inequality_removal,[],[f126])).

fof(f126,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k2_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl4_6 ),
    inference(superposition,[],[f102,f33])).

fof(f33,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k1_xboole_0
      | k2_relat_1(X0) != k1_xboole_0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( ( k1_relat_1(X0) = k1_xboole_0
          | k2_relat_1(X0) != k1_xboole_0 )
        & ( k2_relat_1(X0) = k1_xboole_0
          | k1_relat_1(X0) != k1_xboole_0 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k1_xboole_0
      <=> k2_relat_1(X0) = k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k1_xboole_0
      <=> k2_relat_1(X0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

fof(f102,plain,
    ( k1_xboole_0 != k1_relat_1(sK3)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f100])).

fof(f89,plain,
    ( spl4_5
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f78,f64,f72])).

fof(f72,plain,
    ( spl4_5
  <=> r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f78,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f66,f31])).

fof(f31,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

fof(f76,plain,
    ( ~ spl4_5
    | spl4_3 ),
    inference(avatar_split_clause,[],[f69,f58,f72])).

fof(f69,plain,
    ( ~ r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))
    | spl4_3 ),
    inference(resolution,[],[f35,f60])).

fof(f60,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f67,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f28,f64])).

fof(f28,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
      | ~ v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3))
      | ~ v1_funct_1(sK3) )
    & v1_funct_1(sK3)
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f9,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
          | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
          | ~ v1_funct_1(X0) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
        | ~ v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3))
        | ~ v1_funct_1(sK3) )
      & v1_funct_1(sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
          & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
          & v1_funct_1(X0) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f62,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f29,f50])).

fof(f50,plain,
    ( spl4_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f29,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f61,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f30,f58,f54,f50])).

fof(f30,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
    | ~ v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3))
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:52:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.44  % (12250)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.45  % (12250)Refutation found. Thanks to Tanya!
% 0.22/0.45  % SZS status Theorem for theBenchmark
% 0.22/0.45  % SZS output start Proof for theBenchmark
% 0.22/0.45  fof(f379,plain,(
% 0.22/0.45    $false),
% 0.22/0.45    inference(avatar_sat_refutation,[],[f61,f62,f67,f76,f89,f157,f199,f249,f309,f324,f377])).
% 0.22/0.45  fof(f377,plain,(
% 0.22/0.45    ~spl4_6 | ~spl4_10 | ~spl4_22),
% 0.22/0.45    inference(avatar_contradiction_clause,[],[f376])).
% 0.22/0.45  fof(f376,plain,(
% 0.22/0.45    $false | (~spl4_6 | ~spl4_10 | ~spl4_22)),
% 0.22/0.45    inference(subsumption_resolution,[],[f375,f48])).
% 0.22/0.45  fof(f48,plain,(
% 0.22/0.45    ( ! [X1] : (~sP0(k1_xboole_0,X1)) )),
% 0.22/0.45    inference(equality_resolution,[],[f42])).
% 0.22/0.45  fof(f42,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k1_xboole_0 != X0 | ~sP0(X0,X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f27])).
% 0.22/0.45  fof(f27,plain,(
% 0.22/0.45    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 0.22/0.45    inference(nnf_transformation,[],[f15])).
% 0.22/0.45  fof(f15,plain,(
% 0.22/0.45    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 0.22/0.45    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.45  fof(f375,plain,(
% 0.22/0.45    sP0(k1_xboole_0,k1_xboole_0) | (~spl4_6 | ~spl4_10 | ~spl4_22)),
% 0.22/0.45    inference(forward_demodulation,[],[f374,f101])).
% 0.22/0.45  fof(f101,plain,(
% 0.22/0.45    k1_xboole_0 = k1_relat_1(sK3) | ~spl4_6),
% 0.22/0.45    inference(avatar_component_clause,[],[f100])).
% 0.22/0.45  fof(f100,plain,(
% 0.22/0.45    spl4_6 <=> k1_xboole_0 = k1_relat_1(sK3)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.45  fof(f374,plain,(
% 0.22/0.45    sP0(k1_relat_1(sK3),k1_xboole_0) | (~spl4_10 | ~spl4_22)),
% 0.22/0.45    inference(forward_demodulation,[],[f322,f135])).
% 0.22/0.45  fof(f135,plain,(
% 0.22/0.45    k1_xboole_0 = k2_relat_1(sK3) | ~spl4_10),
% 0.22/0.45    inference(avatar_component_clause,[],[f134])).
% 0.22/0.45  fof(f134,plain,(
% 0.22/0.45    spl4_10 <=> k1_xboole_0 = k2_relat_1(sK3)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.22/0.45  fof(f322,plain,(
% 0.22/0.45    sP0(k1_relat_1(sK3),k2_relat_1(sK3)) | ~spl4_22),
% 0.22/0.45    inference(avatar_component_clause,[],[f320])).
% 0.22/0.45  fof(f320,plain,(
% 0.22/0.45    spl4_22 <=> sP0(k1_relat_1(sK3),k2_relat_1(sK3))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.22/0.45  fof(f324,plain,(
% 0.22/0.45    spl4_22 | spl4_2 | ~spl4_18 | ~spl4_20),
% 0.22/0.45    inference(avatar_split_clause,[],[f289,f246,f195,f54,f320])).
% 0.22/0.45  fof(f54,plain,(
% 0.22/0.45    spl4_2 <=> v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.45  fof(f195,plain,(
% 0.22/0.45    spl4_18 <=> sP1(k1_relat_1(sK3),sK3,k2_relat_1(sK3))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.22/0.45  fof(f246,plain,(
% 0.22/0.45    spl4_20 <=> k1_relat_1(sK3) = k1_relset_1(k1_relat_1(sK3),k2_relat_1(sK3),sK3)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.22/0.45  fof(f289,plain,(
% 0.22/0.45    sP0(k1_relat_1(sK3),k2_relat_1(sK3)) | (spl4_2 | ~spl4_18 | ~spl4_20)),
% 0.22/0.45    inference(unit_resulting_resolution,[],[f197,f56,f248,f40])).
% 0.22/0.45  fof(f40,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) != X0 | v1_funct_2(X1,X0,X2) | sP0(X0,X2) | ~sP1(X0,X1,X2)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f26])).
% 0.22/0.45  fof(f26,plain,(
% 0.22/0.45    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP0(X0,X2) | ~sP1(X0,X1,X2))),
% 0.22/0.45    inference(rectify,[],[f25])).
% 0.22/0.45  fof(f25,plain,(
% 0.22/0.45    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 0.22/0.45    inference(nnf_transformation,[],[f16])).
% 0.22/0.45  fof(f16,plain,(
% 0.22/0.45    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 0.22/0.45    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.45  fof(f248,plain,(
% 0.22/0.45    k1_relat_1(sK3) = k1_relset_1(k1_relat_1(sK3),k2_relat_1(sK3),sK3) | ~spl4_20),
% 0.22/0.45    inference(avatar_component_clause,[],[f246])).
% 0.22/0.45  fof(f56,plain,(
% 0.22/0.45    ~v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3)) | spl4_2),
% 0.22/0.45    inference(avatar_component_clause,[],[f54])).
% 0.22/0.45  fof(f197,plain,(
% 0.22/0.45    sP1(k1_relat_1(sK3),sK3,k2_relat_1(sK3)) | ~spl4_18),
% 0.22/0.45    inference(avatar_component_clause,[],[f195])).
% 0.22/0.45  fof(f309,plain,(
% 0.22/0.45    spl4_2 | spl4_10 | ~spl4_18 | ~spl4_20),
% 0.22/0.45    inference(avatar_contradiction_clause,[],[f308])).
% 0.22/0.45  fof(f308,plain,(
% 0.22/0.45    $false | (spl4_2 | spl4_10 | ~spl4_18 | ~spl4_20)),
% 0.22/0.45    inference(subsumption_resolution,[],[f307,f197])).
% 0.22/0.45  fof(f307,plain,(
% 0.22/0.45    ~sP1(k1_relat_1(sK3),sK3,k2_relat_1(sK3)) | (spl4_2 | spl4_10 | ~spl4_20)),
% 0.22/0.45    inference(subsumption_resolution,[],[f306,f175])).
% 0.22/0.45  fof(f175,plain,(
% 0.22/0.45    ( ! [X0] : (~sP0(X0,k2_relat_1(sK3))) ) | spl4_10),
% 0.22/0.45    inference(unit_resulting_resolution,[],[f136,f41])).
% 0.22/0.45  fof(f41,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~sP0(X0,X1) | k1_xboole_0 = X1) )),
% 0.22/0.45    inference(cnf_transformation,[],[f27])).
% 0.22/0.45  fof(f136,plain,(
% 0.22/0.45    k1_xboole_0 != k2_relat_1(sK3) | spl4_10),
% 0.22/0.45    inference(avatar_component_clause,[],[f134])).
% 0.22/0.45  fof(f306,plain,(
% 0.22/0.45    sP0(k1_relat_1(sK3),k2_relat_1(sK3)) | ~sP1(k1_relat_1(sK3),sK3,k2_relat_1(sK3)) | (spl4_2 | ~spl4_20)),
% 0.22/0.45    inference(subsumption_resolution,[],[f294,f56])).
% 0.22/0.45  fof(f294,plain,(
% 0.22/0.45    v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3)) | sP0(k1_relat_1(sK3),k2_relat_1(sK3)) | ~sP1(k1_relat_1(sK3),sK3,k2_relat_1(sK3)) | ~spl4_20),
% 0.22/0.45    inference(trivial_inequality_removal,[],[f293])).
% 0.22/0.45  fof(f293,plain,(
% 0.22/0.45    k1_relat_1(sK3) != k1_relat_1(sK3) | v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3)) | sP0(k1_relat_1(sK3),k2_relat_1(sK3)) | ~sP1(k1_relat_1(sK3),sK3,k2_relat_1(sK3)) | ~spl4_20),
% 0.22/0.45    inference(superposition,[],[f40,f248])).
% 0.22/0.45  fof(f249,plain,(
% 0.22/0.45    spl4_20 | ~spl4_3),
% 0.22/0.45    inference(avatar_split_clause,[],[f244,f58,f246])).
% 0.22/0.45  fof(f58,plain,(
% 0.22/0.45    spl4_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.45  fof(f244,plain,(
% 0.22/0.45    k1_relat_1(sK3) = k1_relset_1(k1_relat_1(sK3),k2_relat_1(sK3),sK3) | ~spl4_3),
% 0.22/0.45    inference(unit_resulting_resolution,[],[f59,f36])).
% 0.22/0.45  fof(f36,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f12])).
% 0.22/0.45  fof(f12,plain,(
% 0.22/0.45    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.45    inference(ennf_transformation,[],[f4])).
% 0.22/0.45  fof(f4,axiom,(
% 0.22/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.45  fof(f59,plain,(
% 0.22/0.45    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) | ~spl4_3),
% 0.22/0.45    inference(avatar_component_clause,[],[f58])).
% 0.22/0.45  fof(f199,plain,(
% 0.22/0.45    spl4_18 | ~spl4_3),
% 0.22/0.45    inference(avatar_split_clause,[],[f193,f58,f195])).
% 0.22/0.45  fof(f193,plain,(
% 0.22/0.45    sP1(k1_relat_1(sK3),sK3,k2_relat_1(sK3)) | ~spl4_3),
% 0.22/0.45    inference(resolution,[],[f43,f59])).
% 0.22/0.45  fof(f43,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP1(X0,X2,X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f18])).
% 0.22/0.45  fof(f18,plain,(
% 0.22/0.45    ! [X0,X1,X2] : ((sP2(X2,X1,X0) & sP1(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.45    inference(definition_folding,[],[f14,f17,f16,f15])).
% 0.22/0.45  fof(f17,plain,(
% 0.22/0.45    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP2(X2,X1,X0))),
% 0.22/0.45    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.22/0.45  fof(f14,plain,(
% 0.22/0.45    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.45    inference(flattening,[],[f13])).
% 0.22/0.45  fof(f13,plain,(
% 0.22/0.45    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.45    inference(ennf_transformation,[],[f5])).
% 0.22/0.45  fof(f5,axiom,(
% 0.22/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.45  fof(f157,plain,(
% 0.22/0.45    ~spl4_10 | ~spl4_4 | spl4_6),
% 0.22/0.45    inference(avatar_split_clause,[],[f156,f100,f64,f134])).
% 0.22/0.45  fof(f64,plain,(
% 0.22/0.45    spl4_4 <=> v1_relat_1(sK3)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.45  fof(f156,plain,(
% 0.22/0.45    k1_xboole_0 != k2_relat_1(sK3) | (~spl4_4 | spl4_6)),
% 0.22/0.45    inference(subsumption_resolution,[],[f132,f66])).
% 0.22/0.45  fof(f66,plain,(
% 0.22/0.45    v1_relat_1(sK3) | ~spl4_4),
% 0.22/0.45    inference(avatar_component_clause,[],[f64])).
% 0.22/0.45  fof(f132,plain,(
% 0.22/0.45    k1_xboole_0 != k2_relat_1(sK3) | ~v1_relat_1(sK3) | spl4_6),
% 0.22/0.45    inference(trivial_inequality_removal,[],[f126])).
% 0.22/0.45  fof(f126,plain,(
% 0.22/0.45    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 != k2_relat_1(sK3) | ~v1_relat_1(sK3) | spl4_6),
% 0.22/0.45    inference(superposition,[],[f102,f33])).
% 0.22/0.45  fof(f33,plain,(
% 0.22/0.45    ( ! [X0] : (k1_relat_1(X0) = k1_xboole_0 | k2_relat_1(X0) != k1_xboole_0 | ~v1_relat_1(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f21])).
% 0.22/0.45  fof(f21,plain,(
% 0.22/0.45    ! [X0] : (((k1_relat_1(X0) = k1_xboole_0 | k2_relat_1(X0) != k1_xboole_0) & (k2_relat_1(X0) = k1_xboole_0 | k1_relat_1(X0) != k1_xboole_0)) | ~v1_relat_1(X0))),
% 0.22/0.45    inference(nnf_transformation,[],[f11])).
% 0.22/0.45  fof(f11,plain,(
% 0.22/0.45    ! [X0] : ((k1_relat_1(X0) = k1_xboole_0 <=> k2_relat_1(X0) = k1_xboole_0) | ~v1_relat_1(X0))),
% 0.22/0.45    inference(ennf_transformation,[],[f3])).
% 0.22/0.45  fof(f3,axiom,(
% 0.22/0.45    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k1_xboole_0 <=> k2_relat_1(X0) = k1_xboole_0))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).
% 0.22/0.45  fof(f102,plain,(
% 0.22/0.45    k1_xboole_0 != k1_relat_1(sK3) | spl4_6),
% 0.22/0.45    inference(avatar_component_clause,[],[f100])).
% 0.22/0.45  fof(f89,plain,(
% 0.22/0.45    spl4_5 | ~spl4_4),
% 0.22/0.45    inference(avatar_split_clause,[],[f78,f64,f72])).
% 0.22/0.45  fof(f72,plain,(
% 0.22/0.45    spl4_5 <=> r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.45  fof(f78,plain,(
% 0.22/0.45    r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))) | ~spl4_4),
% 0.22/0.45    inference(unit_resulting_resolution,[],[f66,f31])).
% 0.22/0.45  fof(f31,plain,(
% 0.22/0.45    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f10])).
% 0.22/0.45  fof(f10,plain,(
% 0.22/0.45    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.45    inference(ennf_transformation,[],[f2])).
% 0.22/0.45  fof(f2,axiom,(
% 0.22/0.45    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).
% 0.22/0.45  fof(f76,plain,(
% 0.22/0.45    ~spl4_5 | spl4_3),
% 0.22/0.45    inference(avatar_split_clause,[],[f69,f58,f72])).
% 0.22/0.45  fof(f69,plain,(
% 0.22/0.45    ~r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))) | spl4_3),
% 0.22/0.45    inference(resolution,[],[f35,f60])).
% 0.22/0.45  fof(f60,plain,(
% 0.22/0.45    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) | spl4_3),
% 0.22/0.45    inference(avatar_component_clause,[],[f58])).
% 0.22/0.45  fof(f35,plain,(
% 0.22/0.45    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f22])).
% 0.22/0.45  fof(f22,plain,(
% 0.22/0.45    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.45    inference(nnf_transformation,[],[f1])).
% 0.22/0.45  fof(f1,axiom,(
% 0.22/0.45    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.45  fof(f67,plain,(
% 0.22/0.45    spl4_4),
% 0.22/0.45    inference(avatar_split_clause,[],[f28,f64])).
% 0.22/0.45  fof(f28,plain,(
% 0.22/0.45    v1_relat_1(sK3)),
% 0.22/0.45    inference(cnf_transformation,[],[f20])).
% 0.22/0.45  fof(f20,plain,(
% 0.22/0.45    (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) | ~v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3)) | ~v1_funct_1(sK3)) & v1_funct_1(sK3) & v1_relat_1(sK3)),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f9,f19])).
% 0.22/0.45  fof(f19,plain,(
% 0.22/0.45    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0)) => ((~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) | ~v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3)) | ~v1_funct_1(sK3)) & v1_funct_1(sK3) & v1_relat_1(sK3))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f9,plain,(
% 0.22/0.45    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.22/0.45    inference(flattening,[],[f8])).
% 0.22/0.45  fof(f8,plain,(
% 0.22/0.45    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.22/0.45    inference(ennf_transformation,[],[f7])).
% 0.22/0.45  fof(f7,negated_conjecture,(
% 0.22/0.45    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.22/0.45    inference(negated_conjecture,[],[f6])).
% 0.22/0.45  fof(f6,conjecture,(
% 0.22/0.45    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.22/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 0.22/0.45  fof(f62,plain,(
% 0.22/0.45    spl4_1),
% 0.22/0.45    inference(avatar_split_clause,[],[f29,f50])).
% 0.22/0.45  fof(f50,plain,(
% 0.22/0.45    spl4_1 <=> v1_funct_1(sK3)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.45  fof(f29,plain,(
% 0.22/0.45    v1_funct_1(sK3)),
% 0.22/0.45    inference(cnf_transformation,[],[f20])).
% 0.22/0.45  fof(f61,plain,(
% 0.22/0.45    ~spl4_1 | ~spl4_2 | ~spl4_3),
% 0.22/0.45    inference(avatar_split_clause,[],[f30,f58,f54,f50])).
% 0.22/0.45  fof(f30,plain,(
% 0.22/0.45    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) | ~v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3)) | ~v1_funct_1(sK3)),
% 0.22/0.45    inference(cnf_transformation,[],[f20])).
% 0.22/0.45  % SZS output end Proof for theBenchmark
% 0.22/0.45  % (12250)------------------------------
% 0.22/0.45  % (12250)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (12250)Termination reason: Refutation
% 0.22/0.45  
% 0.22/0.45  % (12250)Memory used [KB]: 10746
% 0.22/0.45  % (12250)Time elapsed: 0.011 s
% 0.22/0.45  % (12250)------------------------------
% 0.22/0.45  % (12250)------------------------------
% 0.22/0.46  % (12232)Success in time 0.089 s
%------------------------------------------------------------------------------
