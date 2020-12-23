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
% DateTime   : Thu Dec  3 13:07:11 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 183 expanded)
%              Number of leaves         :   22 (  69 expanded)
%              Depth                    :   11
%              Number of atoms          :  175 ( 305 expanded)
%              Number of equality atoms :   54 ( 126 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f330,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f61,f71,f77,f83,f144,f271,f278,f329])).

fof(f329,plain,
    ( spl2_3
    | ~ spl2_18 ),
    inference(avatar_contradiction_clause,[],[f328])).

fof(f328,plain,
    ( $false
    | spl2_3
    | ~ spl2_18 ),
    inference(global_subsumption,[],[f277,f327])).

fof(f327,plain,
    ( sK1 != k3_xboole_0(sK1,sK0)
    | spl2_3 ),
    inference(superposition,[],[f70,f313])).

fof(f313,plain,(
    ! [X0,X1] : k8_relset_1(X0,X0,k6_partfun1(X0),X1) = k3_xboole_0(X1,X0) ),
    inference(forward_demodulation,[],[f304,f181])).

fof(f181,plain,(
    ! [X0,X1] : k3_xboole_0(X1,X0) = k10_relat_1(k6_partfun1(X0),X1) ),
    inference(forward_demodulation,[],[f180,f47])).

fof(f47,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f32,f28])).

fof(f28,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f32,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f180,plain,(
    ! [X0,X1] : k10_relat_1(k6_partfun1(X0),X1) = k1_relat_1(k6_partfun1(k3_xboole_0(X1,X0))) ),
    inference(forward_demodulation,[],[f179,f48])).

fof(f48,plain,(
    ! [X0,X1] : k5_relat_1(k6_partfun1(X1),k6_partfun1(X0)) = k6_partfun1(k3_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f35,f28,f28,f28])).

fof(f35,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

fof(f179,plain,(
    ! [X0,X1] : k1_relat_1(k5_relat_1(k6_partfun1(X0),k6_partfun1(X1))) = k10_relat_1(k6_partfun1(X0),X1) ),
    inference(forward_demodulation,[],[f177,f47])).

fof(f177,plain,(
    ! [X0,X1] : k1_relat_1(k5_relat_1(k6_partfun1(X0),k6_partfun1(X1))) = k10_relat_1(k6_partfun1(X0),k1_relat_1(k6_partfun1(X1))) ),
    inference(unit_resulting_resolution,[],[f42,f42,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f42,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f27,f28])).

fof(f27,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f304,plain,(
    ! [X0,X1] : k8_relset_1(X0,X0,k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1) ),
    inference(unit_resulting_resolution,[],[f43,f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f43,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f29,f28])).

fof(f29,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

fof(f70,plain,
    ( sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl2_3
  <=> sK1 = k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f277,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f275])).

fof(f275,plain,
    ( spl2_18
  <=> sK1 = k3_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f278,plain,
    ( spl2_18
    | ~ spl2_10
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f272,f268,f142,f275])).

fof(f142,plain,
    ( spl2_10
  <=> ! [X0] : k3_xboole_0(sK1,X0) = k9_relat_1(k6_partfun1(sK0),k3_xboole_0(sK1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f268,plain,
    ( spl2_17
  <=> sK1 = k9_relat_1(k6_partfun1(sK0),k3_xboole_0(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f272,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl2_10
    | ~ spl2_17 ),
    inference(superposition,[],[f270,f143])).

fof(f143,plain,
    ( ! [X0] : k3_xboole_0(sK1,X0) = k9_relat_1(k6_partfun1(sK0),k3_xboole_0(sK1,X0))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f142])).

fof(f270,plain,
    ( sK1 = k9_relat_1(k6_partfun1(sK0),k3_xboole_0(sK1,sK0))
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f268])).

fof(f271,plain,
    ( spl2_17
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f244,f58,f268])).

fof(f58,plain,
    ( spl2_2
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f244,plain,
    ( sK1 = k9_relat_1(k6_partfun1(sK0),k3_xboole_0(sK1,sK0))
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f60,f243])).

fof(f243,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k9_relat_1(k6_partfun1(X1),k3_xboole_0(X0,X1)) = X0 ) ),
    inference(global_subsumption,[],[f42,f242])).

fof(f242,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_partfun1(X1),k3_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(k6_partfun1(X1)) ) ),
    inference(forward_demodulation,[],[f241,f181])).

fof(f241,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k9_relat_1(k6_partfun1(X1),k10_relat_1(k6_partfun1(X1),X0)) = X0
      | ~ v1_relat_1(k6_partfun1(X1)) ) ),
    inference(forward_demodulation,[],[f240,f46])).

fof(f46,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f33,f28])).

fof(f33,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f240,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_relat_1(k6_partfun1(X1)))
      | k9_relat_1(k6_partfun1(X1),k10_relat_1(k6_partfun1(X1),X0)) = X0
      | ~ v1_relat_1(k6_partfun1(X1)) ) ),
    inference(resolution,[],[f37,f44])).

fof(f44,plain,(
    ! [X0] : v1_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f31,f28])).

fof(f31,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(f60,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f144,plain,
    ( spl2_10
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f110,f81,f142])).

fof(f81,plain,
    ( spl2_5
  <=> ! [X0] : m1_subset_1(k3_xboole_0(sK1,X0),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f110,plain,
    ( ! [X0] : k3_xboole_0(sK1,X0) = k9_relat_1(k6_partfun1(sK0),k3_xboole_0(sK1,X0))
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f82,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k9_relat_1(k6_partfun1(X0),X1) = X1 ) ),
    inference(definition_unfolding,[],[f36,f28])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

fof(f82,plain,
    ( ! [X0] : m1_subset_1(k3_xboole_0(sK1,X0),k1_zfmisc_1(sK0))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f81])).

fof(f83,plain,
    ( spl2_5
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f79,f75,f81])).

fof(f75,plain,
    ( spl2_4
  <=> ! [X0] : r1_tarski(k3_xboole_0(sK1,X0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f79,plain,
    ( ! [X0] : m1_subset_1(k3_xboole_0(sK1,X0),k1_zfmisc_1(sK0))
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f76,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f76,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(sK1,X0),sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f75])).

fof(f77,plain,
    ( spl2_4
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f72,f58,f75])).

fof(f72,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(sK1,X0),sK0)
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f60,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

fof(f71,plain,(
    ~ spl2_3 ),
    inference(avatar_split_clause,[],[f26,f68])).

fof(f26,plain,(
    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f22])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).

fof(f61,plain,
    ( spl2_2
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f55,f51,f58])).

fof(f51,plain,
    ( spl2_1
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f55,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f53,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f53,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f54,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f25,f51])).

fof(f25,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:14:47 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (771)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.42  % (771)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f330,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(avatar_sat_refutation,[],[f54,f61,f71,f77,f83,f144,f271,f278,f329])).
% 0.21/0.42  fof(f329,plain,(
% 0.21/0.42    spl2_3 | ~spl2_18),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f328])).
% 0.21/0.42  fof(f328,plain,(
% 0.21/0.42    $false | (spl2_3 | ~spl2_18)),
% 0.21/0.42    inference(global_subsumption,[],[f277,f327])).
% 0.21/0.42  fof(f327,plain,(
% 0.21/0.42    sK1 != k3_xboole_0(sK1,sK0) | spl2_3),
% 0.21/0.42    inference(superposition,[],[f70,f313])).
% 0.21/0.42  fof(f313,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.42    inference(forward_demodulation,[],[f304,f181])).
% 0.21/0.42  fof(f181,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k10_relat_1(k6_partfun1(X0),X1)) )),
% 0.21/0.42    inference(forward_demodulation,[],[f180,f47])).
% 0.21/0.42  fof(f47,plain,(
% 0.21/0.42    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 0.21/0.42    inference(definition_unfolding,[],[f32,f28])).
% 0.21/0.42  fof(f28,plain,(
% 0.21/0.42    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f12])).
% 0.21/0.42  fof(f12,axiom,(
% 0.21/0.42    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.21/0.42  fof(f32,plain,(
% 0.21/0.42    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.42    inference(cnf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,axiom,(
% 0.21/0.42    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.42  fof(f180,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k10_relat_1(k6_partfun1(X0),X1) = k1_relat_1(k6_partfun1(k3_xboole_0(X1,X0)))) )),
% 0.21/0.42    inference(forward_demodulation,[],[f179,f48])).
% 0.21/0.42  fof(f48,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k5_relat_1(k6_partfun1(X1),k6_partfun1(X0)) = k6_partfun1(k3_xboole_0(X0,X1))) )),
% 0.21/0.42    inference(definition_unfolding,[],[f35,f28,f28,f28])).
% 0.21/0.42  fof(f35,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f9])).
% 0.21/0.42  fof(f9,axiom,(
% 0.21/0.42    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 0.21/0.42  fof(f179,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(k6_partfun1(X0),k6_partfun1(X1))) = k10_relat_1(k6_partfun1(X0),X1)) )),
% 0.21/0.42    inference(forward_demodulation,[],[f177,f47])).
% 0.21/0.42  fof(f177,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(k6_partfun1(X0),k6_partfun1(X1))) = k10_relat_1(k6_partfun1(X0),k1_relat_1(k6_partfun1(X1)))) )),
% 0.21/0.42    inference(unit_resulting_resolution,[],[f42,f42,f34])).
% 0.21/0.42  fof(f34,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f16])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,axiom,(
% 0.21/0.42    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 0.21/0.42  fof(f42,plain,(
% 0.21/0.42    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 0.21/0.42    inference(definition_unfolding,[],[f27,f28])).
% 0.21/0.42  fof(f27,plain,(
% 0.21/0.42    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.21/0.42  fof(f304,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1)) )),
% 0.21/0.42    inference(unit_resulting_resolution,[],[f43,f41])).
% 0.21/0.42  fof(f41,plain,(
% 0.21/0.42    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f21])).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.42    inference(ennf_transformation,[],[f10])).
% 0.21/0.42  fof(f10,axiom,(
% 0.21/0.42    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.21/0.42  fof(f43,plain,(
% 0.21/0.42    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.21/0.42    inference(definition_unfolding,[],[f29,f28])).
% 0.21/0.42  fof(f29,plain,(
% 0.21/0.42    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f11])).
% 0.21/0.42  fof(f11,axiom,(
% 0.21/0.42    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).
% 0.21/0.42  fof(f70,plain,(
% 0.21/0.42    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) | spl2_3),
% 0.21/0.42    inference(avatar_component_clause,[],[f68])).
% 0.21/0.42  fof(f68,plain,(
% 0.21/0.42    spl2_3 <=> sK1 = k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.42  fof(f277,plain,(
% 0.21/0.42    sK1 = k3_xboole_0(sK1,sK0) | ~spl2_18),
% 0.21/0.42    inference(avatar_component_clause,[],[f275])).
% 0.21/0.42  fof(f275,plain,(
% 0.21/0.42    spl2_18 <=> sK1 = k3_xboole_0(sK1,sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.21/0.42  fof(f278,plain,(
% 0.21/0.42    spl2_18 | ~spl2_10 | ~spl2_17),
% 0.21/0.42    inference(avatar_split_clause,[],[f272,f268,f142,f275])).
% 0.21/0.42  fof(f142,plain,(
% 0.21/0.42    spl2_10 <=> ! [X0] : k3_xboole_0(sK1,X0) = k9_relat_1(k6_partfun1(sK0),k3_xboole_0(sK1,X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.42  fof(f268,plain,(
% 0.21/0.42    spl2_17 <=> sK1 = k9_relat_1(k6_partfun1(sK0),k3_xboole_0(sK1,sK0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.21/0.42  fof(f272,plain,(
% 0.21/0.42    sK1 = k3_xboole_0(sK1,sK0) | (~spl2_10 | ~spl2_17)),
% 0.21/0.42    inference(superposition,[],[f270,f143])).
% 0.21/0.42  fof(f143,plain,(
% 0.21/0.42    ( ! [X0] : (k3_xboole_0(sK1,X0) = k9_relat_1(k6_partfun1(sK0),k3_xboole_0(sK1,X0))) ) | ~spl2_10),
% 0.21/0.42    inference(avatar_component_clause,[],[f142])).
% 0.21/0.42  fof(f270,plain,(
% 0.21/0.42    sK1 = k9_relat_1(k6_partfun1(sK0),k3_xboole_0(sK1,sK0)) | ~spl2_17),
% 0.21/0.42    inference(avatar_component_clause,[],[f268])).
% 0.21/0.42  fof(f271,plain,(
% 0.21/0.42    spl2_17 | ~spl2_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f244,f58,f268])).
% 0.21/0.42  fof(f58,plain,(
% 0.21/0.42    spl2_2 <=> r1_tarski(sK1,sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.42  fof(f244,plain,(
% 0.21/0.42    sK1 = k9_relat_1(k6_partfun1(sK0),k3_xboole_0(sK1,sK0)) | ~spl2_2),
% 0.21/0.42    inference(unit_resulting_resolution,[],[f60,f243])).
% 0.21/0.42  fof(f243,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k9_relat_1(k6_partfun1(X1),k3_xboole_0(X0,X1)) = X0) )),
% 0.21/0.42    inference(global_subsumption,[],[f42,f242])).
% 0.21/0.42  fof(f242,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k9_relat_1(k6_partfun1(X1),k3_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1) | ~v1_relat_1(k6_partfun1(X1))) )),
% 0.21/0.42    inference(forward_demodulation,[],[f241,f181])).
% 0.21/0.42  fof(f241,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k9_relat_1(k6_partfun1(X1),k10_relat_1(k6_partfun1(X1),X0)) = X0 | ~v1_relat_1(k6_partfun1(X1))) )),
% 0.21/0.42    inference(forward_demodulation,[],[f240,f46])).
% 0.21/0.42  fof(f46,plain,(
% 0.21/0.42    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 0.21/0.42    inference(definition_unfolding,[],[f33,f28])).
% 0.21/0.42  fof(f33,plain,(
% 0.21/0.42    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.42    inference(cnf_transformation,[],[f5])).
% 0.21/0.42  fof(f240,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_tarski(X0,k2_relat_1(k6_partfun1(X1))) | k9_relat_1(k6_partfun1(X1),k10_relat_1(k6_partfun1(X1),X0)) = X0 | ~v1_relat_1(k6_partfun1(X1))) )),
% 0.21/0.42    inference(resolution,[],[f37,f44])).
% 0.21/0.42  fof(f44,plain,(
% 0.21/0.42    ( ! [X0] : (v1_funct_1(k6_partfun1(X0))) )),
% 0.21/0.42    inference(definition_unfolding,[],[f31,f28])).
% 0.21/0.42  fof(f31,plain,(
% 0.21/0.42    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f6])).
% 0.21/0.42  fof(f6,axiom,(
% 0.21/0.42    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.21/0.42  fof(f37,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~v1_relat_1(X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f19])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.42    inference(flattening,[],[f18])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.42    inference(ennf_transformation,[],[f7])).
% 0.21/0.42  fof(f7,axiom,(
% 0.21/0.42    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).
% 0.21/0.42  fof(f60,plain,(
% 0.21/0.42    r1_tarski(sK1,sK0) | ~spl2_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f58])).
% 0.21/0.42  fof(f144,plain,(
% 0.21/0.42    spl2_10 | ~spl2_5),
% 0.21/0.42    inference(avatar_split_clause,[],[f110,f81,f142])).
% 0.21/0.42  fof(f81,plain,(
% 0.21/0.42    spl2_5 <=> ! [X0] : m1_subset_1(k3_xboole_0(sK1,X0),k1_zfmisc_1(sK0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.42  fof(f110,plain,(
% 0.21/0.42    ( ! [X0] : (k3_xboole_0(sK1,X0) = k9_relat_1(k6_partfun1(sK0),k3_xboole_0(sK1,X0))) ) | ~spl2_5),
% 0.21/0.42    inference(unit_resulting_resolution,[],[f82,f49])).
% 0.21/0.42  fof(f49,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k9_relat_1(k6_partfun1(X0),X1) = X1) )),
% 0.21/0.42    inference(definition_unfolding,[],[f36,f28])).
% 0.21/0.42  fof(f36,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f17])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f8])).
% 0.21/0.42  fof(f8,axiom,(
% 0.21/0.42    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).
% 0.21/0.42  fof(f82,plain,(
% 0.21/0.42    ( ! [X0] : (m1_subset_1(k3_xboole_0(sK1,X0),k1_zfmisc_1(sK0))) ) | ~spl2_5),
% 0.21/0.42    inference(avatar_component_clause,[],[f81])).
% 0.21/0.42  fof(f83,plain,(
% 0.21/0.42    spl2_5 | ~spl2_4),
% 0.21/0.42    inference(avatar_split_clause,[],[f79,f75,f81])).
% 0.21/0.42  fof(f75,plain,(
% 0.21/0.42    spl2_4 <=> ! [X0] : r1_tarski(k3_xboole_0(sK1,X0),sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.42  fof(f79,plain,(
% 0.21/0.42    ( ! [X0] : (m1_subset_1(k3_xboole_0(sK1,X0),k1_zfmisc_1(sK0))) ) | ~spl2_4),
% 0.21/0.42    inference(unit_resulting_resolution,[],[f76,f39])).
% 0.21/0.42  fof(f39,plain,(
% 0.21/0.42    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f24])).
% 0.21/0.42  fof(f24,plain,(
% 0.21/0.42    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.42    inference(nnf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.42  fof(f76,plain,(
% 0.21/0.42    ( ! [X0] : (r1_tarski(k3_xboole_0(sK1,X0),sK0)) ) | ~spl2_4),
% 0.21/0.42    inference(avatar_component_clause,[],[f75])).
% 0.21/0.42  fof(f77,plain,(
% 0.21/0.42    spl2_4 | ~spl2_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f72,f58,f75])).
% 0.21/0.42  fof(f72,plain,(
% 0.21/0.42    ( ! [X0] : (r1_tarski(k3_xboole_0(sK1,X0),sK0)) ) | ~spl2_2),
% 0.21/0.42    inference(unit_resulting_resolution,[],[f60,f40])).
% 0.21/0.42  fof(f40,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f20])).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).
% 0.21/0.42  fof(f71,plain,(
% 0.21/0.42    ~spl2_3),
% 0.21/0.42    inference(avatar_split_clause,[],[f26,f68])).
% 0.21/0.42  fof(f26,plain,(
% 0.21/0.42    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)),
% 0.21/0.42    inference(cnf_transformation,[],[f23])).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f22])).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    ? [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0))) => (sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    ? [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f14])).
% 0.21/0.42  fof(f14,negated_conjecture,(
% 0.21/0.42    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 0.21/0.42    inference(negated_conjecture,[],[f13])).
% 0.21/0.42  fof(f13,conjecture,(
% 0.21/0.42    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).
% 0.21/0.42  fof(f61,plain,(
% 0.21/0.42    spl2_2 | ~spl2_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f55,f51,f58])).
% 0.21/0.42  fof(f51,plain,(
% 0.21/0.42    spl2_1 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.43  fof(f55,plain,(
% 0.21/0.43    r1_tarski(sK1,sK0) | ~spl2_1),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f53,f38])).
% 0.21/0.43  fof(f38,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f24])).
% 0.21/0.43  fof(f53,plain,(
% 0.21/0.43    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl2_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f51])).
% 0.21/0.43  fof(f54,plain,(
% 0.21/0.43    spl2_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f25,f51])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.43    inference(cnf_transformation,[],[f23])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (771)------------------------------
% 0.21/0.43  % (771)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (771)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (771)Memory used [KB]: 10874
% 0.21/0.43  % (771)Time elapsed: 0.012 s
% 0.21/0.43  % (771)------------------------------
% 0.21/0.43  % (771)------------------------------
% 0.21/0.43  % (748)Success in time 0.076 s
%------------------------------------------------------------------------------
