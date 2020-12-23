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
% DateTime   : Thu Dec  3 13:03:44 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 136 expanded)
%              Number of leaves         :   21 (  53 expanded)
%              Depth                    :   12
%              Number of atoms          :  199 ( 328 expanded)
%              Number of equality atoms :   67 ( 132 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f131,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f54,f62,f66,f71,f76,f81,f90,f100,f114,f130])).

fof(f130,plain,
    ( ~ spl4_11
    | ~ spl4_4
    | spl4_12 ),
    inference(avatar_split_clause,[],[f129,f111,f60,f98])).

fof(f98,plain,
    ( spl4_11
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f60,plain,
    ( spl4_4
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f111,plain,
    ( spl4_12
  <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f129,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_4
    | spl4_12 ),
    inference(superposition,[],[f127,f46])).

fof(f46,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f127,plain,
    ( ! [X0] : ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ spl4_4
    | spl4_12 ),
    inference(trivial_inequality_removal,[],[f126])).

fof(f126,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_xboole_0
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) )
    | ~ spl4_4
    | spl4_12 ),
    inference(forward_demodulation,[],[f125,f61])).

fof(f61,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f60])).

fof(f125,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) )
    | spl4_12 ),
    inference(superposition,[],[f112,f124])).

fof(f124,plain,(
    ! [X4,X5,X3] :
      ( k1_relat_1(X5) = k10_relat_1(X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(duplicate_literal_removal,[],[f121])).

fof(f121,plain,(
    ! [X4,X5,X3] :
      ( k1_relat_1(X5) = k10_relat_1(X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(superposition,[],[f120,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k10_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f117])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k10_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f42,f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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

fof(f112,plain,
    ( k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1)
    | spl4_12 ),
    inference(avatar_component_clause,[],[f111])).

fof(f114,plain,
    ( ~ spl4_12
    | ~ spl4_11
    | spl4_1
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f109,f87,f48,f98,f111])).

fof(f48,plain,
    ( spl4_1
  <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f87,plain,
    ( spl4_9
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f109,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1)
    | spl4_1
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f108,f88])).

fof(f88,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f87])).

fof(f108,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1)
    | spl4_1
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f107,f46])).

fof(f107,plain,
    ( k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl4_1
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f105,f88])).

fof(f105,plain,
    ( k1_xboole_0 != k10_relat_1(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl4_1 ),
    inference(superposition,[],[f49,f43])).

fof(f49,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f100,plain,
    ( spl4_11
    | ~ spl4_6
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f92,f87,f69,f98])).

fof(f69,plain,
    ( spl4_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f92,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_6
    | ~ spl4_9 ),
    inference(superposition,[],[f70,f88])).

fof(f70,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f69])).

fof(f90,plain,
    ( spl4_9
    | ~ spl4_8
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f84,f69,f79,f87])).

fof(f79,plain,
    ( spl4_8
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f84,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = sK2
    | ~ spl4_6 ),
    inference(resolution,[],[f83,f70])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ v1_xboole_0(X1)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f35,f34])).

fof(f34,plain,(
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

fof(f35,plain,(
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

fof(f81,plain,
    ( spl4_8
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f77,f74,f64,f79])).

fof(f64,plain,
    ( spl4_5
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f74,plain,
    ( spl4_7
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f77,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(superposition,[],[f65,f75])).

fof(f75,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f74])).

fof(f65,plain,
    ( v1_xboole_0(sK3)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f64])).

fof(f76,plain,
    ( spl4_7
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f72,f64,f74])).

fof(f72,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_5 ),
    inference(resolution,[],[f34,f65])).

fof(f71,plain,
    ( spl4_6
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f67,f52,f69])).

fof(f52,plain,
    ( spl4_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f67,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f53,f46])).

fof(f53,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f66,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f44,f64])).

fof(f44,plain,(
    v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    v1_xboole_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f2,f27])).

fof(f27,plain,
    ( ? [X0] : v1_xboole_0(X0)
   => v1_xboole_0(sK3) ),
    introduced(choice_axiom,[])).

fof(f2,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(f62,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f31,f60])).

fof(f31,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f54,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f29,f52])).

fof(f29,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f23])).

fof(f23,plain,
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
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
       => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,plain,(
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

fof(f50,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f30,f48])).

fof(f30,plain,(
    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:38:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.37  ipcrm: permission denied for id (812056577)
% 0.13/0.37  ipcrm: permission denied for id (812187653)
% 0.13/0.37  ipcrm: permission denied for id (812220422)
% 0.13/0.37  ipcrm: permission denied for id (812285960)
% 0.13/0.38  ipcrm: permission denied for id (815857675)
% 0.13/0.38  ipcrm: permission denied for id (815923213)
% 0.13/0.38  ipcrm: permission denied for id (812449806)
% 0.13/0.38  ipcrm: permission denied for id (815955983)
% 0.13/0.38  ipcrm: permission denied for id (812515344)
% 0.13/0.39  ipcrm: permission denied for id (816021522)
% 0.13/0.39  ipcrm: permission denied for id (816087060)
% 0.13/0.39  ipcrm: permission denied for id (812613653)
% 0.13/0.39  ipcrm: permission denied for id (812679191)
% 0.13/0.39  ipcrm: permission denied for id (816152600)
% 0.13/0.39  ipcrm: permission denied for id (812744729)
% 0.13/0.40  ipcrm: permission denied for id (812810267)
% 0.13/0.40  ipcrm: permission denied for id (812843036)
% 0.13/0.40  ipcrm: permission denied for id (812875805)
% 0.20/0.40  ipcrm: permission denied for id (812941344)
% 0.20/0.40  ipcrm: permission denied for id (816283681)
% 0.20/0.40  ipcrm: permission denied for id (816316450)
% 0.20/0.41  ipcrm: permission denied for id (813039651)
% 0.20/0.41  ipcrm: permission denied for id (816349220)
% 0.20/0.41  ipcrm: permission denied for id (813105189)
% 0.20/0.41  ipcrm: permission denied for id (816447528)
% 0.20/0.41  ipcrm: permission denied for id (816480297)
% 0.20/0.42  ipcrm: permission denied for id (813334572)
% 0.20/0.42  ipcrm: permission denied for id (813367341)
% 0.20/0.42  ipcrm: permission denied for id (816578606)
% 0.20/0.42  ipcrm: permission denied for id (813400111)
% 0.20/0.42  ipcrm: permission denied for id (813432880)
% 0.20/0.42  ipcrm: permission denied for id (816644146)
% 0.20/0.43  ipcrm: permission denied for id (813498420)
% 0.20/0.43  ipcrm: permission denied for id (816709685)
% 0.20/0.43  ipcrm: permission denied for id (816742454)
% 0.20/0.43  ipcrm: permission denied for id (813596727)
% 0.20/0.43  ipcrm: permission denied for id (813629496)
% 0.20/0.43  ipcrm: permission denied for id (816775225)
% 0.20/0.43  ipcrm: permission denied for id (816807994)
% 0.20/0.43  ipcrm: permission denied for id (813727803)
% 0.20/0.44  ipcrm: permission denied for id (813760572)
% 0.20/0.44  ipcrm: permission denied for id (813793341)
% 0.20/0.44  ipcrm: permission denied for id (813826110)
% 0.20/0.44  ipcrm: permission denied for id (813858879)
% 0.20/0.44  ipcrm: permission denied for id (813891648)
% 0.20/0.44  ipcrm: permission denied for id (813924417)
% 0.20/0.45  ipcrm: permission denied for id (814022724)
% 0.20/0.45  ipcrm: permission denied for id (814055494)
% 0.20/0.45  ipcrm: permission denied for id (814088263)
% 0.20/0.45  ipcrm: permission denied for id (814153801)
% 0.20/0.45  ipcrm: permission denied for id (814186570)
% 0.20/0.46  ipcrm: permission denied for id (814317645)
% 0.20/0.46  ipcrm: permission denied for id (817037390)
% 0.20/0.46  ipcrm: permission denied for id (814481490)
% 0.20/0.46  ipcrm: permission denied for id (814514260)
% 0.20/0.47  ipcrm: permission denied for id (814547029)
% 0.20/0.47  ipcrm: permission denied for id (814579798)
% 0.20/0.47  ipcrm: permission denied for id (817201239)
% 0.20/0.47  ipcrm: permission denied for id (814612568)
% 0.20/0.47  ipcrm: permission denied for id (817332316)
% 0.20/0.48  ipcrm: permission denied for id (814710877)
% 0.20/0.48  ipcrm: permission denied for id (814743646)
% 0.20/0.48  ipcrm: permission denied for id (817365087)
% 0.20/0.48  ipcrm: permission denied for id (814841953)
% 0.20/0.48  ipcrm: permission denied for id (817463395)
% 0.20/0.49  ipcrm: permission denied for id (817528933)
% 0.20/0.49  ipcrm: permission denied for id (814940262)
% 0.20/0.49  ipcrm: permission denied for id (814973032)
% 0.20/0.49  ipcrm: permission denied for id (815005801)
% 0.20/0.49  ipcrm: permission denied for id (817627243)
% 0.20/0.50  ipcrm: permission denied for id (817692781)
% 0.20/0.50  ipcrm: permission denied for id (817725550)
% 0.20/0.50  ipcrm: permission denied for id (815202416)
% 0.20/0.50  ipcrm: permission denied for id (817791089)
% 0.20/0.50  ipcrm: permission denied for id (815300723)
% 0.20/0.50  ipcrm: permission denied for id (815333492)
% 0.20/0.51  ipcrm: permission denied for id (817889397)
% 0.20/0.51  ipcrm: permission denied for id (815366262)
% 0.20/0.51  ipcrm: permission denied for id (817922167)
% 0.20/0.51  ipcrm: permission denied for id (817954936)
% 0.20/0.51  ipcrm: permission denied for id (817987705)
% 0.20/0.51  ipcrm: permission denied for id (818086011)
% 0.20/0.51  ipcrm: permission denied for id (818118780)
% 0.20/0.52  ipcrm: permission denied for id (815562878)
% 0.20/0.58  % (12059)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.59  % (12059)Refutation found. Thanks to Tanya!
% 0.20/0.59  % SZS status Theorem for theBenchmark
% 0.20/0.59  % SZS output start Proof for theBenchmark
% 0.20/0.59  fof(f131,plain,(
% 0.20/0.59    $false),
% 0.20/0.59    inference(avatar_sat_refutation,[],[f50,f54,f62,f66,f71,f76,f81,f90,f100,f114,f130])).
% 0.20/0.59  fof(f130,plain,(
% 0.20/0.59    ~spl4_11 | ~spl4_4 | spl4_12),
% 0.20/0.59    inference(avatar_split_clause,[],[f129,f111,f60,f98])).
% 0.20/0.59  fof(f98,plain,(
% 0.20/0.59    spl4_11 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.20/0.59  fof(f60,plain,(
% 0.20/0.59    spl4_4 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.59  fof(f111,plain,(
% 0.20/0.59    spl4_12 <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK1)),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.20/0.59  fof(f129,plain,(
% 0.20/0.59    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl4_4 | spl4_12)),
% 0.20/0.59    inference(superposition,[],[f127,f46])).
% 0.20/0.59  fof(f46,plain,(
% 0.20/0.59    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.59    inference(equality_resolution,[],[f38])).
% 0.20/0.59  fof(f38,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.20/0.59    inference(cnf_transformation,[],[f26])).
% 0.20/0.59  fof(f26,plain,(
% 0.20/0.59    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.59    inference(flattening,[],[f25])).
% 0.20/0.59  fof(f25,plain,(
% 0.20/0.59    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.59    inference(nnf_transformation,[],[f4])).
% 0.20/0.59  fof(f4,axiom,(
% 0.20/0.59    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.59  fof(f127,plain,(
% 0.20/0.59    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))) ) | (~spl4_4 | spl4_12)),
% 0.20/0.59    inference(trivial_inequality_removal,[],[f126])).
% 0.20/0.59  fof(f126,plain,(
% 0.20/0.59    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))) ) | (~spl4_4 | spl4_12)),
% 0.20/0.59    inference(forward_demodulation,[],[f125,f61])).
% 0.20/0.59  fof(f61,plain,(
% 0.20/0.59    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl4_4),
% 0.20/0.59    inference(avatar_component_clause,[],[f60])).
% 0.20/0.59  fof(f125,plain,(
% 0.20/0.59    ( ! [X0] : (k1_xboole_0 != k1_relat_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))) ) | spl4_12),
% 0.20/0.59    inference(superposition,[],[f112,f124])).
% 0.20/0.59  fof(f124,plain,(
% 0.20/0.59    ( ! [X4,X5,X3] : (k1_relat_1(X5) = k10_relat_1(X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 0.20/0.59    inference(duplicate_literal_removal,[],[f121])).
% 0.20/0.59  fof(f121,plain,(
% 0.20/0.59    ( ! [X4,X5,X3] : (k1_relat_1(X5) = k10_relat_1(X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 0.20/0.59    inference(superposition,[],[f120,f40])).
% 0.20/0.59  fof(f40,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.59    inference(cnf_transformation,[],[f20])).
% 0.20/0.59  fof(f20,plain,(
% 0.20/0.59    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.59    inference(ennf_transformation,[],[f8])).
% 0.20/0.59  fof(f8,axiom,(
% 0.20/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.59  fof(f120,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k10_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.59    inference(duplicate_literal_removal,[],[f117])).
% 0.20/0.59  fof(f117,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k10_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.59    inference(superposition,[],[f42,f43])).
% 0.20/0.59  fof(f43,plain,(
% 0.20/0.59    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.59    inference(cnf_transformation,[],[f22])).
% 0.20/0.59  fof(f22,plain,(
% 0.20/0.59    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.59    inference(ennf_transformation,[],[f9])).
% 0.20/0.59  fof(f9,axiom,(
% 0.20/0.59    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.20/0.59  fof(f42,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.59    inference(cnf_transformation,[],[f21])).
% 0.20/0.59  fof(f21,plain,(
% 0.20/0.59    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.59    inference(ennf_transformation,[],[f10])).
% 0.20/0.59  fof(f10,axiom,(
% 0.20/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).
% 0.20/0.59  fof(f112,plain,(
% 0.20/0.59    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1) | spl4_12),
% 0.20/0.59    inference(avatar_component_clause,[],[f111])).
% 0.20/0.59  fof(f114,plain,(
% 0.20/0.59    ~spl4_12 | ~spl4_11 | spl4_1 | ~spl4_9),
% 0.20/0.59    inference(avatar_split_clause,[],[f109,f87,f48,f98,f111])).
% 0.20/0.59  fof(f48,plain,(
% 0.20/0.59    spl4_1 <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.59  fof(f87,plain,(
% 0.20/0.59    spl4_9 <=> k1_xboole_0 = sK2),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.59  fof(f109,plain,(
% 0.20/0.59    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1) | (spl4_1 | ~spl4_9)),
% 0.20/0.59    inference(forward_demodulation,[],[f108,f88])).
% 0.20/0.59  fof(f88,plain,(
% 0.20/0.59    k1_xboole_0 = sK2 | ~spl4_9),
% 0.20/0.59    inference(avatar_component_clause,[],[f87])).
% 0.20/0.59  fof(f108,plain,(
% 0.20/0.59    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1) | (spl4_1 | ~spl4_9)),
% 0.20/0.59    inference(forward_demodulation,[],[f107,f46])).
% 0.20/0.59  fof(f107,plain,(
% 0.20/0.59    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl4_1 | ~spl4_9)),
% 0.20/0.59    inference(forward_demodulation,[],[f105,f88])).
% 0.20/0.59  fof(f105,plain,(
% 0.20/0.59    k1_xboole_0 != k10_relat_1(sK2,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | spl4_1),
% 0.20/0.59    inference(superposition,[],[f49,f43])).
% 0.20/0.59  fof(f49,plain,(
% 0.20/0.59    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) | spl4_1),
% 0.20/0.59    inference(avatar_component_clause,[],[f48])).
% 0.20/0.59  fof(f100,plain,(
% 0.20/0.59    spl4_11 | ~spl4_6 | ~spl4_9),
% 0.20/0.59    inference(avatar_split_clause,[],[f92,f87,f69,f98])).
% 0.20/0.59  fof(f69,plain,(
% 0.20/0.59    spl4_6 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.59  fof(f92,plain,(
% 0.20/0.59    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl4_6 | ~spl4_9)),
% 0.20/0.59    inference(superposition,[],[f70,f88])).
% 0.20/0.59  fof(f70,plain,(
% 0.20/0.59    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl4_6),
% 0.20/0.59    inference(avatar_component_clause,[],[f69])).
% 0.20/0.59  fof(f90,plain,(
% 0.20/0.59    spl4_9 | ~spl4_8 | ~spl4_6),
% 0.20/0.59    inference(avatar_split_clause,[],[f84,f69,f79,f87])).
% 0.20/0.59  fof(f79,plain,(
% 0.20/0.59    spl4_8 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.59  fof(f84,plain,(
% 0.20/0.59    ~v1_xboole_0(k1_xboole_0) | k1_xboole_0 = sK2 | ~spl4_6),
% 0.20/0.59    inference(resolution,[],[f83,f70])).
% 0.20/0.59  fof(f83,plain,(
% 0.20/0.59    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~v1_xboole_0(X1) | k1_xboole_0 = X0) )),
% 0.20/0.59    inference(resolution,[],[f35,f34])).
% 0.20/0.59  fof(f34,plain,(
% 0.20/0.59    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.59    inference(cnf_transformation,[],[f17])).
% 0.20/0.59  fof(f17,plain,(
% 0.20/0.59    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.59    inference(ennf_transformation,[],[f1])).
% 0.20/0.59  fof(f1,axiom,(
% 0.20/0.59    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.59  fof(f35,plain,(
% 0.20/0.59    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f18])).
% 0.20/0.59  fof(f18,plain,(
% 0.20/0.59    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.20/0.59    inference(ennf_transformation,[],[f5])).
% 0.20/0.59  fof(f5,axiom,(
% 0.20/0.59    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.20/0.59  fof(f81,plain,(
% 0.20/0.59    spl4_8 | ~spl4_5 | ~spl4_7),
% 0.20/0.59    inference(avatar_split_clause,[],[f77,f74,f64,f79])).
% 0.20/0.59  fof(f64,plain,(
% 0.20/0.59    spl4_5 <=> v1_xboole_0(sK3)),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.59  fof(f74,plain,(
% 0.20/0.59    spl4_7 <=> k1_xboole_0 = sK3),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.59  fof(f77,plain,(
% 0.20/0.59    v1_xboole_0(k1_xboole_0) | (~spl4_5 | ~spl4_7)),
% 0.20/0.59    inference(superposition,[],[f65,f75])).
% 0.20/0.59  fof(f75,plain,(
% 0.20/0.59    k1_xboole_0 = sK3 | ~spl4_7),
% 0.20/0.59    inference(avatar_component_clause,[],[f74])).
% 0.20/0.59  fof(f65,plain,(
% 0.20/0.59    v1_xboole_0(sK3) | ~spl4_5),
% 0.20/0.59    inference(avatar_component_clause,[],[f64])).
% 0.20/0.59  fof(f76,plain,(
% 0.20/0.59    spl4_7 | ~spl4_5),
% 0.20/0.59    inference(avatar_split_clause,[],[f72,f64,f74])).
% 0.20/0.59  fof(f72,plain,(
% 0.20/0.59    k1_xboole_0 = sK3 | ~spl4_5),
% 0.20/0.59    inference(resolution,[],[f34,f65])).
% 0.20/0.59  fof(f71,plain,(
% 0.20/0.59    spl4_6 | ~spl4_2),
% 0.20/0.59    inference(avatar_split_clause,[],[f67,f52,f69])).
% 0.20/0.59  fof(f52,plain,(
% 0.20/0.59    spl4_2 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.59  fof(f67,plain,(
% 0.20/0.59    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl4_2),
% 0.20/0.59    inference(forward_demodulation,[],[f53,f46])).
% 0.20/0.59  fof(f53,plain,(
% 0.20/0.59    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | ~spl4_2),
% 0.20/0.59    inference(avatar_component_clause,[],[f52])).
% 0.20/0.59  fof(f66,plain,(
% 0.20/0.59    spl4_5),
% 0.20/0.59    inference(avatar_split_clause,[],[f44,f64])).
% 0.20/0.59  fof(f44,plain,(
% 0.20/0.59    v1_xboole_0(sK3)),
% 0.20/0.59    inference(cnf_transformation,[],[f28])).
% 0.20/0.59  fof(f28,plain,(
% 0.20/0.59    v1_xboole_0(sK3)),
% 0.20/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f2,f27])).
% 0.20/0.59  fof(f27,plain,(
% 0.20/0.59    ? [X0] : v1_xboole_0(X0) => v1_xboole_0(sK3)),
% 0.20/0.59    introduced(choice_axiom,[])).
% 0.20/0.59  fof(f2,axiom,(
% 0.20/0.59    ? [X0] : v1_xboole_0(X0)),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).
% 0.20/0.59  fof(f62,plain,(
% 0.20/0.59    spl4_4),
% 0.20/0.59    inference(avatar_split_clause,[],[f31,f60])).
% 0.20/0.59  fof(f31,plain,(
% 0.20/0.59    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.59    inference(cnf_transformation,[],[f7])).
% 0.20/0.59  fof(f7,axiom,(
% 0.20/0.59    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.59  fof(f54,plain,(
% 0.20/0.59    spl4_2),
% 0.20/0.59    inference(avatar_split_clause,[],[f29,f52])).
% 0.20/0.59  fof(f29,plain,(
% 0.20/0.59    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.20/0.59    inference(cnf_transformation,[],[f24])).
% 0.20/0.59  fof(f24,plain,(
% 0.20/0.59    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.20/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f23])).
% 0.20/0.59  fof(f23,plain,(
% 0.20/0.59    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) => (k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))))),
% 0.20/0.59    introduced(choice_axiom,[])).
% 0.20/0.59  fof(f16,plain,(
% 0.20/0.59    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))))),
% 0.20/0.59    inference(ennf_transformation,[],[f15])).
% 0.20/0.59  fof(f15,plain,(
% 0.20/0.59    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.20/0.59    inference(pure_predicate_removal,[],[f14])).
% 0.20/0.59  fof(f14,plain,(
% 0.20/0.59    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.20/0.59    inference(pure_predicate_removal,[],[f12])).
% 0.20/0.59  fof(f12,negated_conjecture,(
% 0.20/0.59    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.20/0.59    inference(negated_conjecture,[],[f11])).
% 0.20/0.59  fof(f11,conjecture,(
% 0.20/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_funct_2)).
% 0.20/0.59  fof(f50,plain,(
% 0.20/0.59    ~spl4_1),
% 0.20/0.59    inference(avatar_split_clause,[],[f30,f48])).
% 0.20/0.59  fof(f30,plain,(
% 0.20/0.59    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.20/0.59    inference(cnf_transformation,[],[f24])).
% 0.20/0.59  % SZS output end Proof for theBenchmark
% 0.20/0.59  % (12059)------------------------------
% 0.20/0.59  % (12059)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.59  % (12059)Termination reason: Refutation
% 0.20/0.59  
% 0.20/0.59  % (12059)Memory used [KB]: 10618
% 0.20/0.59  % (12059)Time elapsed: 0.007 s
% 0.20/0.59  % (12059)------------------------------
% 0.20/0.59  % (12059)------------------------------
% 0.20/0.59  % (11919)Success in time 0.232 s
%------------------------------------------------------------------------------
