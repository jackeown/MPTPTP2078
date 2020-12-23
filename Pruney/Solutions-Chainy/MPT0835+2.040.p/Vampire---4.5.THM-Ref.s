%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:21 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 167 expanded)
%              Number of leaves         :   16 (  42 expanded)
%              Depth                    :   14
%              Number of atoms          :  178 ( 370 expanded)
%              Number of equality atoms :   66 ( 173 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f170,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f67,f77,f81,f126,f169])).

fof(f169,plain,
    ( spl3_2
    | ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f166])).

fof(f166,plain,
    ( $false
    | spl3_2
    | ~ spl3_3 ),
    inference(resolution,[],[f165,f50])).

fof(f50,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f165,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2))
    | spl3_2
    | ~ spl3_3 ),
    inference(trivial_inequality_removal,[],[f164])).

fof(f164,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2))
    | spl3_2
    | ~ spl3_3 ),
    inference(superposition,[],[f156,f159])).

fof(f159,plain,
    ( ! [X0] :
        ( k2_relat_1(sK2) = k9_relat_1(sK2,X0)
        | ~ r1_tarski(k1_relat_1(sK2),X0) )
    | ~ spl3_3 ),
    inference(superposition,[],[f84,f83])).

fof(f83,plain,
    ( ! [X1] :
        ( sK2 = k7_relat_1(sK2,X1)
        | ~ r1_tarski(k1_relat_1(sK2),X1) )
    | ~ spl3_3 ),
    inference(resolution,[],[f72,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f72,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl3_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f84,plain,
    ( ! [X2] : k2_relat_1(k7_relat_1(sK2,X2)) = k9_relat_1(sK2,X2)
    | ~ spl3_3 ),
    inference(resolution,[],[f72,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f156,plain,
    ( k2_relat_1(sK2) != k9_relat_1(sK2,k1_relat_1(sK2))
    | spl3_2 ),
    inference(superposition,[],[f155,f56])).

fof(f56,plain,(
    ! [X0] : k7_relset_1(sK1,sK0,sK2,X0) = k9_relat_1(sK2,X0) ),
    inference(resolution,[],[f31,f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f31,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) != k1_relset_1(X1,X0,X2)
        | k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) != k2_relset_1(X1,X0,X2) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
          & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
        & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_relset_1)).

fof(f155,plain,
    ( k2_relat_1(sK2) != k7_relset_1(sK1,sK0,sK2,k1_relat_1(sK2))
    | spl3_2 ),
    inference(forward_demodulation,[],[f154,f111])).

fof(f111,plain,(
    k1_relat_1(sK2) = k10_relat_1(sK2,sK0) ),
    inference(global_subsumption,[],[f31,f110])).

fof(f110,plain,
    ( k1_relat_1(sK2) = k10_relat_1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(forward_demodulation,[],[f108,f51])).

fof(f51,plain,(
    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f31,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f108,plain,
    ( k1_relset_1(sK1,sK0,sK2) = k10_relat_1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(superposition,[],[f57,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(f57,plain,(
    ! [X1] : k8_relset_1(sK1,sK0,sK2,X1) = k10_relat_1(sK2,X1) ),
    inference(resolution,[],[f31,f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f154,plain,
    ( k2_relat_1(sK2) != k7_relset_1(sK1,sK0,sK2,k10_relat_1(sK2,sK0))
    | spl3_2 ),
    inference(forward_demodulation,[],[f153,f57])).

fof(f153,plain,
    ( k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2)
    | spl3_2 ),
    inference(forward_demodulation,[],[f66,f52])).

fof(f52,plain,(
    k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f31,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f66,plain,
    ( k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl3_2
  <=> k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) = k2_relset_1(sK1,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f126,plain,
    ( spl3_1
    | ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f125])).

fof(f125,plain,
    ( $false
    | spl3_1
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f31,f124])).

fof(f124,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_1
    | ~ spl3_3 ),
    inference(trivial_inequality_removal,[],[f123])).

fof(f123,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_1
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f122,f86])).

fof(f86,plain,
    ( k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2))
    | ~ spl3_3 ),
    inference(resolution,[],[f72,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f122,plain,
    ( k1_relat_1(sK2) != k10_relat_1(sK2,k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_1 ),
    inference(superposition,[],[f114,f48])).

fof(f114,plain,
    ( k1_relat_1(sK2) != k8_relset_1(sK1,sK0,sK2,k2_relat_1(sK2))
    | spl3_1 ),
    inference(forward_demodulation,[],[f101,f105])).

fof(f105,plain,(
    k2_relat_1(sK2) = k9_relat_1(sK2,sK1) ),
    inference(global_subsumption,[],[f31,f104])).

fof(f104,plain,
    ( k2_relat_1(sK2) = k9_relat_1(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(forward_demodulation,[],[f102,f52])).

fof(f102,plain,
    ( k2_relset_1(sK1,sK0,sK2) = k9_relat_1(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(superposition,[],[f56,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f101,plain,
    ( k1_relat_1(sK2) != k8_relset_1(sK1,sK0,sK2,k9_relat_1(sK2,sK1))
    | spl3_1 ),
    inference(backward_demodulation,[],[f90,f56])).

fof(f90,plain,
    ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2)
    | spl3_1 ),
    inference(backward_demodulation,[],[f62,f51])).

fof(f62,plain,
    ( k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl3_1
  <=> k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) = k1_relset_1(sK1,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f81,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f79])).

fof(f79,plain,
    ( $false
    | spl3_4 ),
    inference(resolution,[],[f76,f34])).

fof(f34,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f76,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl3_4
  <=> v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f77,plain,
    ( spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f58,f74,f70])).

fof(f58,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK2) ),
    inference(resolution,[],[f31,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f67,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f30,f64,f60])).

fof(f30,plain,
    ( k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2)
    | k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:14:37 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.20/0.46  % (27919)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.47  % (27919)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f170,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f67,f77,f81,f126,f169])).
% 0.20/0.47  fof(f169,plain,(
% 0.20/0.47    spl3_2 | ~spl3_3),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f166])).
% 0.20/0.47  fof(f166,plain,(
% 0.20/0.47    $false | (spl3_2 | ~spl3_3)),
% 0.20/0.47    inference(resolution,[],[f165,f50])).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.47    inference(equality_resolution,[],[f38])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.20/0.47    inference(cnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.47  fof(f165,plain,(
% 0.20/0.47    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) | (spl3_2 | ~spl3_3)),
% 0.20/0.47    inference(trivial_inequality_removal,[],[f164])).
% 0.20/0.47  fof(f164,plain,(
% 0.20/0.47    k2_relat_1(sK2) != k2_relat_1(sK2) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) | (spl3_2 | ~spl3_3)),
% 0.20/0.47    inference(superposition,[],[f156,f159])).
% 0.20/0.47  fof(f159,plain,(
% 0.20/0.47    ( ! [X0] : (k2_relat_1(sK2) = k9_relat_1(sK2,X0) | ~r1_tarski(k1_relat_1(sK2),X0)) ) | ~spl3_3),
% 0.20/0.47    inference(superposition,[],[f84,f83])).
% 0.20/0.47  fof(f83,plain,(
% 0.20/0.47    ( ! [X1] : (sK2 = k7_relat_1(sK2,X1) | ~r1_tarski(k1_relat_1(sK2),X1)) ) | ~spl3_3),
% 0.20/0.47    inference(resolution,[],[f72,f36])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1) )),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(flattening,[],[f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 0.20/0.47  fof(f72,plain,(
% 0.20/0.47    v1_relat_1(sK2) | ~spl3_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f70])).
% 0.20/0.47  fof(f70,plain,(
% 0.20/0.47    spl3_3 <=> v1_relat_1(sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.47  fof(f84,plain,(
% 0.20/0.47    ( ! [X2] : (k2_relat_1(k7_relat_1(sK2,X2)) = k9_relat_1(sK2,X2)) ) | ~spl3_3),
% 0.20/0.47    inference(resolution,[],[f72,f35])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.20/0.47  fof(f156,plain,(
% 0.20/0.47    k2_relat_1(sK2) != k9_relat_1(sK2,k1_relat_1(sK2)) | spl3_2),
% 0.20/0.47    inference(superposition,[],[f155,f56])).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    ( ! [X0] : (k7_relset_1(sK1,sK0,sK2,X0) = k9_relat_1(sK2,X0)) )),
% 0.20/0.47    inference(resolution,[],[f31,f47])).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f28])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f11])).
% 0.20/0.47  fof(f11,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ? [X0,X1,X2] : ((k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) != k1_relset_1(X1,X0,X2) | k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) != k2_relset_1(X1,X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.20/0.47    inference(ennf_transformation,[],[f15])).
% 0.20/0.47  fof(f15,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2)))),
% 0.20/0.47    inference(negated_conjecture,[],[f14])).
% 0.20/0.47  fof(f14,conjecture,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_relset_1)).
% 0.20/0.47  fof(f155,plain,(
% 0.20/0.47    k2_relat_1(sK2) != k7_relset_1(sK1,sK0,sK2,k1_relat_1(sK2)) | spl3_2),
% 0.20/0.47    inference(forward_demodulation,[],[f154,f111])).
% 0.20/0.47  fof(f111,plain,(
% 0.20/0.47    k1_relat_1(sK2) = k10_relat_1(sK2,sK0)),
% 0.20/0.47    inference(global_subsumption,[],[f31,f110])).
% 0.20/0.47  fof(f110,plain,(
% 0.20/0.47    k1_relat_1(sK2) = k10_relat_1(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.47    inference(forward_demodulation,[],[f108,f51])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2)),
% 0.20/0.47    inference(resolution,[],[f31,f41])).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.47  fof(f108,plain,(
% 0.20/0.47    k1_relset_1(sK1,sK0,sK2) = k10_relat_1(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.47    inference(superposition,[],[f57,f46])).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f27])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).
% 0.20/0.47  fof(f57,plain,(
% 0.20/0.47    ( ! [X1] : (k8_relset_1(sK1,sK0,sK2,X1) = k10_relat_1(sK2,X1)) )),
% 0.20/0.47    inference(resolution,[],[f31,f48])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f29])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.20/0.47  fof(f154,plain,(
% 0.20/0.47    k2_relat_1(sK2) != k7_relset_1(sK1,sK0,sK2,k10_relat_1(sK2,sK0)) | spl3_2),
% 0.20/0.47    inference(forward_demodulation,[],[f153,f57])).
% 0.20/0.47  fof(f153,plain,(
% 0.20/0.47    k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relat_1(sK2) | spl3_2),
% 0.20/0.47    inference(forward_demodulation,[],[f66,f52])).
% 0.20/0.47  fof(f52,plain,(
% 0.20/0.47    k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2)),
% 0.20/0.47    inference(resolution,[],[f31,f42])).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.47  fof(f66,plain,(
% 0.20/0.47    k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2) | spl3_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f64])).
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    spl3_2 <=> k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) = k2_relset_1(sK1,sK0,sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.47  fof(f126,plain,(
% 0.20/0.47    spl3_1 | ~spl3_3),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f125])).
% 0.20/0.47  fof(f125,plain,(
% 0.20/0.47    $false | (spl3_1 | ~spl3_3)),
% 0.20/0.47    inference(subsumption_resolution,[],[f31,f124])).
% 0.20/0.47  fof(f124,plain,(
% 0.20/0.47    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (spl3_1 | ~spl3_3)),
% 0.20/0.47    inference(trivial_inequality_removal,[],[f123])).
% 0.20/0.47  fof(f123,plain,(
% 0.20/0.47    k1_relat_1(sK2) != k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (spl3_1 | ~spl3_3)),
% 0.20/0.47    inference(forward_demodulation,[],[f122,f86])).
% 0.20/0.47  fof(f86,plain,(
% 0.20/0.47    k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2)) | ~spl3_3),
% 0.20/0.47    inference(resolution,[],[f72,f32])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 0.20/0.47  fof(f122,plain,(
% 0.20/0.47    k1_relat_1(sK2) != k10_relat_1(sK2,k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl3_1),
% 0.20/0.47    inference(superposition,[],[f114,f48])).
% 0.20/0.47  fof(f114,plain,(
% 0.20/0.47    k1_relat_1(sK2) != k8_relset_1(sK1,sK0,sK2,k2_relat_1(sK2)) | spl3_1),
% 0.20/0.47    inference(forward_demodulation,[],[f101,f105])).
% 0.20/0.47  fof(f105,plain,(
% 0.20/0.47    k2_relat_1(sK2) = k9_relat_1(sK2,sK1)),
% 0.20/0.47    inference(global_subsumption,[],[f31,f104])).
% 0.20/0.47  fof(f104,plain,(
% 0.20/0.47    k2_relat_1(sK2) = k9_relat_1(sK2,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.47    inference(forward_demodulation,[],[f102,f52])).
% 0.20/0.47  fof(f102,plain,(
% 0.20/0.47    k2_relset_1(sK1,sK0,sK2) = k9_relat_1(sK2,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.47    inference(superposition,[],[f56,f45])).
% 0.20/0.47  fof(f45,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f27])).
% 0.20/0.47  fof(f101,plain,(
% 0.20/0.47    k1_relat_1(sK2) != k8_relset_1(sK1,sK0,sK2,k9_relat_1(sK2,sK1)) | spl3_1),
% 0.20/0.47    inference(backward_demodulation,[],[f90,f56])).
% 0.20/0.47  fof(f90,plain,(
% 0.20/0.47    k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relat_1(sK2) | spl3_1),
% 0.20/0.47    inference(backward_demodulation,[],[f62,f51])).
% 0.20/0.47  fof(f62,plain,(
% 0.20/0.47    k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2) | spl3_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f60])).
% 0.20/0.47  fof(f60,plain,(
% 0.20/0.47    spl3_1 <=> k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) = k1_relset_1(sK1,sK0,sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.47  fof(f81,plain,(
% 0.20/0.47    spl3_4),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f79])).
% 0.20/0.47  fof(f79,plain,(
% 0.20/0.47    $false | spl3_4),
% 0.20/0.47    inference(resolution,[],[f76,f34])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.47  fof(f76,plain,(
% 0.20/0.47    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | spl3_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f74])).
% 0.20/0.47  fof(f74,plain,(
% 0.20/0.47    spl3_4 <=> v1_relat_1(k2_zfmisc_1(sK1,sK0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.47  fof(f77,plain,(
% 0.20/0.47    spl3_3 | ~spl3_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f58,f74,f70])).
% 0.20/0.47  fof(f58,plain,(
% 0.20/0.47    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | v1_relat_1(sK2)),
% 0.20/0.47    inference(resolution,[],[f31,f33])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.47  fof(f67,plain,(
% 0.20/0.47    ~spl3_1 | ~spl3_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f30,f64,f60])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    k7_relset_1(sK1,sK0,sK2,k8_relset_1(sK1,sK0,sK2,sK0)) != k2_relset_1(sK1,sK0,sK2) | k8_relset_1(sK1,sK0,sK2,k7_relset_1(sK1,sK0,sK2,sK1)) != k1_relset_1(sK1,sK0,sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (27919)------------------------------
% 0.20/0.47  % (27919)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (27919)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (27919)Memory used [KB]: 10618
% 0.20/0.47  % (27919)Time elapsed: 0.034 s
% 0.20/0.47  % (27919)------------------------------
% 0.20/0.47  % (27919)------------------------------
% 0.20/0.48  % (27896)Success in time 0.116 s
%------------------------------------------------------------------------------
