%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:44 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 122 expanded)
%              Number of leaves         :   23 (  46 expanded)
%              Depth                    :   12
%              Number of atoms          :  197 ( 288 expanded)
%              Number of equality atoms :   68 ( 110 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f127,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f52,f60,f64,f69,f74,f79,f90,f108,f124,f126])).

fof(f126,plain,
    ( k1_xboole_0 != sK2
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f124,plain,
    ( ~ spl4_4
    | spl4_11 ),
    inference(avatar_contradiction_clause,[],[f122])).

fof(f122,plain,
    ( $false
    | ~ spl4_4
    | spl4_11 ),
    inference(resolution,[],[f121,f32])).

fof(f32,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f121,plain,
    ( ! [X0] : ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ spl4_4
    | spl4_11 ),
    inference(trivial_inequality_removal,[],[f120])).

fof(f120,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_xboole_0
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) )
    | ~ spl4_4
    | spl4_11 ),
    inference(forward_demodulation,[],[f119,f59])).

fof(f59,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl4_4
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f119,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) )
    | spl4_11 ),
    inference(superposition,[],[f104,f118])).

fof(f118,plain,(
    ! [X4,X5,X3] :
      ( k1_relat_1(X5) = k10_relat_1(X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(duplicate_literal_removal,[],[f115])).

fof(f115,plain,(
    ! [X4,X5,X3] :
      ( k1_relat_1(X5) = k10_relat_1(X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(superposition,[],[f114,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k10_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k10_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f40,f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

fof(f104,plain,
    ( k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1)
    | spl4_11 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl4_11
  <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f108,plain,
    ( ~ spl4_11
    | ~ spl4_12
    | spl4_1
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f101,f87,f46,f106,f103])).

fof(f106,plain,
    ( spl4_12
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f46,plain,
    ( spl4_1
  <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f87,plain,
    ( spl4_9
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f101,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1)
    | spl4_1
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f100,f88])).

fof(f88,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f87])).

fof(f100,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1)
    | spl4_1
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f99,f44])).

fof(f44,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f99,plain,
    ( k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl4_1
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f97,f88])).

fof(f97,plain,
    ( k1_xboole_0 != k10_relat_1(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl4_1 ),
    inference(superposition,[],[f47,f41])).

fof(f47,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f90,plain,
    ( spl4_9
    | ~ spl4_8
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f84,f67,f77,f87])).

fof(f77,plain,
    ( spl4_8
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f67,plain,
    ( spl4_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f84,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = sK2
    | ~ spl4_6 ),
    inference(resolution,[],[f81,f68])).

fof(f68,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f67])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ v1_xboole_0(X1)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f34,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f79,plain,
    ( spl4_8
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f75,f72,f62,f77])).

fof(f62,plain,
    ( spl4_5
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f72,plain,
    ( spl4_7
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f75,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(superposition,[],[f63,f73])).

fof(f73,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f72])).

fof(f63,plain,
    ( v1_xboole_0(sK3)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f62])).

fof(f74,plain,
    ( spl4_7
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f70,f62,f72])).

fof(f70,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_5 ),
    inference(resolution,[],[f33,f63])).

fof(f69,plain,
    ( spl4_6
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f65,f50,f67])).

fof(f50,plain,
    ( spl4_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f65,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f51,f44])).

fof(f51,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f50])).

fof(f64,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f42,f62])).

fof(f42,plain,(
    v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    v1_xboole_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f2,f26])).

fof(f26,plain,
    ( ? [X0] : v1_xboole_0(X0)
   => v1_xboole_0(sK3) ),
    introduced(choice_axiom,[])).

fof(f2,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(f60,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f30,f58])).

fof(f30,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f52,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f28,f50])).

fof(f28,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) )
   => ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
       => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,plain,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_1(X2) )
       => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_2(X2,k1_xboole_0,X0)
          & v1_funct_1(X2) )
       => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_2(X2,k1_xboole_0,X0)
        & v1_funct_1(X2) )
     => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_funct_2)).

fof(f48,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f29,f46])).

fof(f29,plain,(
    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:32:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.42  % (25808)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.43  % (25808)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f127,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(avatar_sat_refutation,[],[f48,f52,f60,f64,f69,f74,f79,f90,f108,f124,f126])).
% 0.20/0.43  fof(f126,plain,(
% 0.20/0.43    k1_xboole_0 != sK2 | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.43    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.43  fof(f124,plain,(
% 0.20/0.43    ~spl4_4 | spl4_11),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f122])).
% 0.20/0.43  fof(f122,plain,(
% 0.20/0.43    $false | (~spl4_4 | spl4_11)),
% 0.20/0.43    inference(resolution,[],[f121,f32])).
% 0.20/0.43  fof(f32,plain,(
% 0.20/0.43    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f4])).
% 0.20/0.43  fof(f4,axiom,(
% 0.20/0.43    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.20/0.43  fof(f121,plain,(
% 0.20/0.43    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))) ) | (~spl4_4 | spl4_11)),
% 0.20/0.43    inference(trivial_inequality_removal,[],[f120])).
% 0.20/0.43  fof(f120,plain,(
% 0.20/0.43    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))) ) | (~spl4_4 | spl4_11)),
% 0.20/0.43    inference(forward_demodulation,[],[f119,f59])).
% 0.20/0.43  fof(f59,plain,(
% 0.20/0.43    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl4_4),
% 0.20/0.43    inference(avatar_component_clause,[],[f58])).
% 0.20/0.43  fof(f58,plain,(
% 0.20/0.43    spl4_4 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.43  fof(f119,plain,(
% 0.20/0.43    ( ! [X0] : (k1_xboole_0 != k1_relat_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))) ) | spl4_11),
% 0.20/0.43    inference(superposition,[],[f104,f118])).
% 0.20/0.43  fof(f118,plain,(
% 0.20/0.43    ( ! [X4,X5,X3] : (k1_relat_1(X5) = k10_relat_1(X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 0.20/0.43    inference(duplicate_literal_removal,[],[f115])).
% 0.20/0.43  fof(f115,plain,(
% 0.20/0.43    ( ! [X4,X5,X3] : (k1_relat_1(X5) = k10_relat_1(X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 0.20/0.43    inference(superposition,[],[f114,f38])).
% 0.20/0.43  fof(f38,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f19])).
% 0.20/0.43  fof(f19,plain,(
% 0.20/0.43    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.43    inference(ennf_transformation,[],[f8])).
% 0.20/0.43  fof(f8,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.43  fof(f114,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k10_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.43    inference(duplicate_literal_removal,[],[f111])).
% 0.20/0.43  fof(f111,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k10_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.43    inference(superposition,[],[f40,f41])).
% 0.20/0.43  fof(f41,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f21])).
% 0.20/0.43  fof(f21,plain,(
% 0.20/0.43    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.43    inference(ennf_transformation,[],[f9])).
% 0.20/0.43  fof(f9,axiom,(
% 0.20/0.43    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.20/0.43  fof(f40,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f20])).
% 0.20/0.43  fof(f20,plain,(
% 0.20/0.43    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.43    inference(ennf_transformation,[],[f10])).
% 0.20/0.43  fof(f10,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).
% 0.20/0.43  fof(f104,plain,(
% 0.20/0.43    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1) | spl4_11),
% 0.20/0.43    inference(avatar_component_clause,[],[f103])).
% 0.20/0.43  fof(f103,plain,(
% 0.20/0.43    spl4_11 <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.20/0.43  fof(f108,plain,(
% 0.20/0.43    ~spl4_11 | ~spl4_12 | spl4_1 | ~spl4_9),
% 0.20/0.43    inference(avatar_split_clause,[],[f101,f87,f46,f106,f103])).
% 0.20/0.43  fof(f106,plain,(
% 0.20/0.43    spl4_12 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.20/0.43  fof(f46,plain,(
% 0.20/0.43    spl4_1 <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.43  fof(f87,plain,(
% 0.20/0.43    spl4_9 <=> k1_xboole_0 = sK2),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.43  fof(f101,plain,(
% 0.20/0.43    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1) | (spl4_1 | ~spl4_9)),
% 0.20/0.43    inference(forward_demodulation,[],[f100,f88])).
% 0.20/0.43  fof(f88,plain,(
% 0.20/0.43    k1_xboole_0 = sK2 | ~spl4_9),
% 0.20/0.43    inference(avatar_component_clause,[],[f87])).
% 0.20/0.43  fof(f100,plain,(
% 0.20/0.43    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1) | (spl4_1 | ~spl4_9)),
% 0.20/0.43    inference(forward_demodulation,[],[f99,f44])).
% 0.20/0.43  fof(f44,plain,(
% 0.20/0.43    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.43    inference(equality_resolution,[],[f36])).
% 0.20/0.43  fof(f36,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.20/0.43    inference(cnf_transformation,[],[f25])).
% 0.20/0.43  fof(f25,plain,(
% 0.20/0.43    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.43    inference(flattening,[],[f24])).
% 0.20/0.43  fof(f24,plain,(
% 0.20/0.43    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.43    inference(nnf_transformation,[],[f3])).
% 0.20/0.43  fof(f3,axiom,(
% 0.20/0.43    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.43  fof(f99,plain,(
% 0.20/0.43    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl4_1 | ~spl4_9)),
% 0.20/0.43    inference(forward_demodulation,[],[f97,f88])).
% 0.20/0.43  fof(f97,plain,(
% 0.20/0.43    k1_xboole_0 != k10_relat_1(sK2,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | spl4_1),
% 0.20/0.43    inference(superposition,[],[f47,f41])).
% 0.20/0.43  fof(f47,plain,(
% 0.20/0.43    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) | spl4_1),
% 0.20/0.43    inference(avatar_component_clause,[],[f46])).
% 0.20/0.43  fof(f90,plain,(
% 0.20/0.43    spl4_9 | ~spl4_8 | ~spl4_6),
% 0.20/0.43    inference(avatar_split_clause,[],[f84,f67,f77,f87])).
% 0.20/0.43  fof(f77,plain,(
% 0.20/0.43    spl4_8 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.43  fof(f67,plain,(
% 0.20/0.43    spl4_6 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.43  fof(f84,plain,(
% 0.20/0.43    ~v1_xboole_0(k1_xboole_0) | k1_xboole_0 = sK2 | ~spl4_6),
% 0.20/0.43    inference(resolution,[],[f81,f68])).
% 0.20/0.43  fof(f68,plain,(
% 0.20/0.43    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl4_6),
% 0.20/0.43    inference(avatar_component_clause,[],[f67])).
% 0.20/0.43  fof(f81,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~v1_xboole_0(X1) | k1_xboole_0 = X0) )),
% 0.20/0.43    inference(resolution,[],[f34,f33])).
% 0.20/0.43  fof(f33,plain,(
% 0.20/0.43    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  fof(f17,plain,(
% 0.20/0.43    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f1])).
% 0.20/0.43  fof(f1,axiom,(
% 0.20/0.43    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.43  fof(f34,plain,(
% 0.20/0.43    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f18])).
% 0.20/0.43  fof(f18,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f5])).
% 0.20/0.43  fof(f5,axiom,(
% 0.20/0.43    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.20/0.43  fof(f79,plain,(
% 0.20/0.43    spl4_8 | ~spl4_5 | ~spl4_7),
% 0.20/0.43    inference(avatar_split_clause,[],[f75,f72,f62,f77])).
% 0.20/0.43  fof(f62,plain,(
% 0.20/0.43    spl4_5 <=> v1_xboole_0(sK3)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.43  fof(f72,plain,(
% 0.20/0.43    spl4_7 <=> k1_xboole_0 = sK3),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.43  fof(f75,plain,(
% 0.20/0.43    v1_xboole_0(k1_xboole_0) | (~spl4_5 | ~spl4_7)),
% 0.20/0.43    inference(superposition,[],[f63,f73])).
% 0.20/0.43  fof(f73,plain,(
% 0.20/0.43    k1_xboole_0 = sK3 | ~spl4_7),
% 0.20/0.43    inference(avatar_component_clause,[],[f72])).
% 0.20/0.43  fof(f63,plain,(
% 0.20/0.43    v1_xboole_0(sK3) | ~spl4_5),
% 0.20/0.43    inference(avatar_component_clause,[],[f62])).
% 0.20/0.43  fof(f74,plain,(
% 0.20/0.43    spl4_7 | ~spl4_5),
% 0.20/0.43    inference(avatar_split_clause,[],[f70,f62,f72])).
% 0.20/0.43  fof(f70,plain,(
% 0.20/0.43    k1_xboole_0 = sK3 | ~spl4_5),
% 0.20/0.43    inference(resolution,[],[f33,f63])).
% 0.20/0.43  fof(f69,plain,(
% 0.20/0.43    spl4_6 | ~spl4_2),
% 0.20/0.43    inference(avatar_split_clause,[],[f65,f50,f67])).
% 0.20/0.43  fof(f50,plain,(
% 0.20/0.43    spl4_2 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.43  fof(f65,plain,(
% 0.20/0.43    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl4_2),
% 0.20/0.43    inference(forward_demodulation,[],[f51,f44])).
% 0.20/0.43  fof(f51,plain,(
% 0.20/0.43    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | ~spl4_2),
% 0.20/0.43    inference(avatar_component_clause,[],[f50])).
% 0.20/0.43  fof(f64,plain,(
% 0.20/0.43    spl4_5),
% 0.20/0.43    inference(avatar_split_clause,[],[f42,f62])).
% 0.20/0.43  fof(f42,plain,(
% 0.20/0.43    v1_xboole_0(sK3)),
% 0.20/0.43    inference(cnf_transformation,[],[f27])).
% 0.20/0.43  fof(f27,plain,(
% 0.20/0.43    v1_xboole_0(sK3)),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f2,f26])).
% 0.20/0.43  fof(f26,plain,(
% 0.20/0.43    ? [X0] : v1_xboole_0(X0) => v1_xboole_0(sK3)),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f2,axiom,(
% 0.20/0.43    ? [X0] : v1_xboole_0(X0)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).
% 0.20/0.43  fof(f60,plain,(
% 0.20/0.43    spl4_4),
% 0.20/0.43    inference(avatar_split_clause,[],[f30,f58])).
% 0.20/0.43  fof(f30,plain,(
% 0.20/0.43    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.43    inference(cnf_transformation,[],[f7])).
% 0.20/0.43  fof(f7,axiom,(
% 0.20/0.43    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.43  fof(f52,plain,(
% 0.20/0.43    spl4_2),
% 0.20/0.43    inference(avatar_split_clause,[],[f28,f50])).
% 0.20/0.43  fof(f28,plain,(
% 0.20/0.43    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.20/0.43    inference(cnf_transformation,[],[f23])).
% 0.20/0.43  fof(f23,plain,(
% 0.20/0.43    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f22])).
% 0.20/0.43  fof(f22,plain,(
% 0.20/0.43    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) => (k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f16,plain,(
% 0.20/0.43    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))))),
% 0.20/0.43    inference(ennf_transformation,[],[f14])).
% 0.20/0.43  fof(f14,plain,(
% 0.20/0.43    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.20/0.43    inference(pure_predicate_removal,[],[f13])).
% 0.20/0.43  fof(f13,plain,(
% 0.20/0.43    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.20/0.43    inference(pure_predicate_removal,[],[f12])).
% 0.20/0.43  fof(f12,negated_conjecture,(
% 0.20/0.43    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.20/0.43    inference(negated_conjecture,[],[f11])).
% 0.20/0.43  fof(f11,conjecture,(
% 0.20/0.43    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_funct_2)).
% 0.20/0.43  fof(f48,plain,(
% 0.20/0.43    ~spl4_1),
% 0.20/0.43    inference(avatar_split_clause,[],[f29,f46])).
% 0.20/0.43  fof(f29,plain,(
% 0.20/0.43    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.20/0.43    inference(cnf_transformation,[],[f23])).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (25808)------------------------------
% 0.20/0.43  % (25808)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (25808)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (25808)Memory used [KB]: 10618
% 0.20/0.43  % (25808)Time elapsed: 0.009 s
% 0.20/0.43  % (25808)------------------------------
% 0.20/0.43  % (25808)------------------------------
% 0.20/0.43  % (25801)Success in time 0.074 s
%------------------------------------------------------------------------------
