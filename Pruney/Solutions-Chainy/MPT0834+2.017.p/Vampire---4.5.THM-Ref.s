%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:12 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 241 expanded)
%              Number of leaves         :   19 (  57 expanded)
%              Depth                    :   20
%              Number of atoms          :  202 ( 522 expanded)
%              Number of equality atoms :   77 ( 209 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f292,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f106,f291])).

fof(f291,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f290])).

fof(f290,plain,
    ( $false
    | spl3_1 ),
    inference(trivial_inequality_removal,[],[f289])).

fof(f289,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | spl3_1 ),
    inference(superposition,[],[f107,f277])).

fof(f277,plain,(
    k1_relat_1(sK2) = k10_relat_1(sK2,sK1) ),
    inference(forward_demodulation,[],[f269,f69])).

fof(f69,plain,(
    k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(resolution,[],[f65,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f65,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f51,f36])).

fof(f36,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1)
        | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
          & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f269,plain,(
    k10_relat_1(sK2,k2_relat_1(sK2)) = k10_relat_1(sK2,sK1) ),
    inference(superposition,[],[f92,f258])).

fof(f258,plain,(
    k2_relat_1(sK2) = k3_xboole_0(k2_relat_1(sK2),sK1) ),
    inference(forward_demodulation,[],[f248,f40])).

fof(f40,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f248,plain,(
    k3_xboole_0(k2_relat_1(sK2),sK1) = k1_relat_1(k6_relat_1(k2_relat_1(sK2))) ),
    inference(superposition,[],[f121,f233])).

fof(f233,plain,(
    k6_relat_1(k2_relat_1(sK2)) = k7_relat_1(k6_relat_1(k2_relat_1(sK2)),sK1) ),
    inference(resolution,[],[f227,f77])).

fof(f77,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(resolution,[],[f55,f36])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f227,plain,(
    ! [X0] :
      ( ~ v5_relat_1(sK2,X0)
      | k6_relat_1(k2_relat_1(sK2)) = k7_relat_1(k6_relat_1(k2_relat_1(sK2)),X0) ) ),
    inference(global_subsumption,[],[f65,f226])).

fof(f226,plain,(
    ! [X0] :
      ( k6_relat_1(k2_relat_1(sK2)) = k7_relat_1(k6_relat_1(k2_relat_1(sK2)),X0)
      | ~ v5_relat_1(sK2,X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(forward_demodulation,[],[f221,f88])).

fof(f88,plain,(
    k2_relat_1(sK2) = k9_relat_1(sK2,sK0) ),
    inference(superposition,[],[f81,f87])).

fof(f87,plain,(
    sK2 = k7_relat_1(sK2,sK0) ),
    inference(global_subsumption,[],[f65,f85])).

fof(f85,plain,
    ( ~ v1_relat_1(sK2)
    | sK2 = k7_relat_1(sK2,sK0) ),
    inference(resolution,[],[f50,f76])).

fof(f76,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(resolution,[],[f54,f36])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f81,plain,(
    ! [X2] : k2_relat_1(k7_relat_1(sK2,X2)) = k9_relat_1(sK2,X2) ),
    inference(resolution,[],[f45,f65])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f221,plain,(
    ! [X0] :
      ( ~ v5_relat_1(sK2,X0)
      | ~ v1_relat_1(sK2)
      | k6_relat_1(k9_relat_1(sK2,sK0)) = k7_relat_1(k6_relat_1(k9_relat_1(sK2,sK0)),X0) ) ),
    inference(superposition,[],[f195,f87])).

fof(f195,plain,(
    ! [X4,X3] :
      ( ~ v5_relat_1(k7_relat_1(sK2,X3),X4)
      | ~ v1_relat_1(k7_relat_1(sK2,X3))
      | k6_relat_1(k9_relat_1(sK2,X3)) = k7_relat_1(k6_relat_1(k9_relat_1(sK2,X3)),X4) ) ),
    inference(resolution,[],[f190,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(sK2,X0),X1)
      | ~ v1_relat_1(k7_relat_1(sK2,X0))
      | ~ v5_relat_1(k7_relat_1(sK2,X0),X1) ) ),
    inference(superposition,[],[f48,f81])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f190,plain,(
    ! [X8,X7] :
      ( ~ r1_tarski(X7,X8)
      | k6_relat_1(X7) = k7_relat_1(k6_relat_1(X7),X8) ) ),
    inference(global_subsumption,[],[f37,f183])).

fof(f183,plain,(
    ! [X8,X7] :
      ( ~ r1_tarski(X7,X8)
      | ~ v1_relat_1(k6_relat_1(X7))
      | k6_relat_1(X7) = k7_relat_1(k6_relat_1(X7),X8) ) ),
    inference(resolution,[],[f90,f38])).

fof(f38,plain,(
    ! [X0] : v4_relat_1(k6_relat_1(X0),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v5_relat_1(k6_relat_1(X0),X0)
      & v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc24_relat_1)).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_relat_1(X0,X1)
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X0)
      | k7_relat_1(X0,X2) = X0 ) ),
    inference(duplicate_literal_removal,[],[f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1)
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X0)
      | k7_relat_1(X0,X2) = X0 ) ),
    inference(resolution,[],[f49,f50])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2)
      | ~ v4_relat_1(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X1)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X1)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( ( v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => v4_relat_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t217_relat_1)).

fof(f37,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f121,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k1_relat_1(k7_relat_1(k6_relat_1(X6),X7)) ),
    inference(superposition,[],[f40,f112])).

fof(f112,plain,(
    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(backward_demodulation,[],[f43,f78])).

fof(f78,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(resolution,[],[f44,f37])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f43,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(f92,plain,(
    ! [X2] : k10_relat_1(sK2,X2) = k10_relat_1(sK2,k3_xboole_0(k2_relat_1(sK2),X2)) ),
    inference(resolution,[],[f46,f65])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

fof(f107,plain,
    ( k1_relat_1(sK2) != k10_relat_1(sK2,sK1)
    | spl3_1 ),
    inference(superposition,[],[f95,f103])).

fof(f103,plain,(
    ! [X0] : k10_relat_1(sK2,X0) = k8_relset_1(sK0,sK1,sK2,X0) ),
    inference(resolution,[],[f57,f36])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f95,plain,
    ( k8_relset_1(sK0,sK1,sK2,sK1) != k1_relat_1(sK2)
    | spl3_1 ),
    inference(backward_demodulation,[],[f60,f94])).

fof(f94,plain,(
    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f52,f36])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f60,plain,
    ( k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl3_1
  <=> k1_relset_1(sK0,sK1,sK2) = k8_relset_1(sK0,sK1,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f106,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f105])).

fof(f105,plain,
    ( $false
    | spl3_2 ),
    inference(trivial_inequality_removal,[],[f104])).

fof(f104,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | spl3_2 ),
    inference(superposition,[],[f102,f88])).

fof(f102,plain,
    ( k2_relat_1(sK2) != k9_relat_1(sK2,sK0)
    | spl3_2 ),
    inference(superposition,[],[f101,f100])).

fof(f100,plain,(
    ! [X0] : k9_relat_1(sK2,X0) = k7_relset_1(sK0,sK1,sK2,X0) ),
    inference(resolution,[],[f56,f36])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f101,plain,
    ( k7_relset_1(sK0,sK1,sK2,sK0) != k2_relat_1(sK2)
    | spl3_2 ),
    inference(backward_demodulation,[],[f63,f98])).

fof(f98,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f53,f36])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f63,plain,
    ( k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl3_2
  <=> k2_relset_1(sK0,sK1,sK2) = k7_relset_1(sK0,sK1,sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f64,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f35,f62,f59])).

fof(f35,plain,
    ( k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)
    | k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:46:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (1827)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.47  % (1818)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.48  % (1818)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (1827)Refutation not found, incomplete strategy% (1827)------------------------------
% 0.21/0.48  % (1827)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (1827)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (1827)Memory used [KB]: 6140
% 0.21/0.48  % (1827)Time elapsed: 0.070 s
% 0.21/0.48  % (1827)------------------------------
% 0.21/0.48  % (1827)------------------------------
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f292,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f64,f106,f291])).
% 0.21/0.48  fof(f291,plain,(
% 0.21/0.48    spl3_1),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f290])).
% 0.21/0.48  fof(f290,plain,(
% 0.21/0.48    $false | spl3_1),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f289])).
% 0.21/0.48  fof(f289,plain,(
% 0.21/0.48    k1_relat_1(sK2) != k1_relat_1(sK2) | spl3_1),
% 0.21/0.48    inference(superposition,[],[f107,f277])).
% 0.21/0.48  fof(f277,plain,(
% 0.21/0.48    k1_relat_1(sK2) = k10_relat_1(sK2,sK1)),
% 0.21/0.48    inference(forward_demodulation,[],[f269,f69])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2)),
% 0.21/0.48    inference(resolution,[],[f65,f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    v1_relat_1(sK2)),
% 0.21/0.48    inference(resolution,[],[f51,f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ? [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1) | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 0.21/0.48    inference(negated_conjecture,[],[f17])).
% 0.21/0.48  fof(f17,conjecture,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.48  fof(f269,plain,(
% 0.21/0.48    k10_relat_1(sK2,k2_relat_1(sK2)) = k10_relat_1(sK2,sK1)),
% 0.21/0.48    inference(superposition,[],[f92,f258])).
% 0.21/0.48  fof(f258,plain,(
% 0.21/0.48    k2_relat_1(sK2) = k3_xboole_0(k2_relat_1(sK2),sK1)),
% 0.21/0.48    inference(forward_demodulation,[],[f248,f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.48  fof(f248,plain,(
% 0.21/0.48    k3_xboole_0(k2_relat_1(sK2),sK1) = k1_relat_1(k6_relat_1(k2_relat_1(sK2)))),
% 0.21/0.48    inference(superposition,[],[f121,f233])).
% 0.21/0.48  fof(f233,plain,(
% 0.21/0.48    k6_relat_1(k2_relat_1(sK2)) = k7_relat_1(k6_relat_1(k2_relat_1(sK2)),sK1)),
% 0.21/0.48    inference(resolution,[],[f227,f77])).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    v5_relat_1(sK2,sK1)),
% 0.21/0.48    inference(resolution,[],[f55,f36])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.48  fof(f227,plain,(
% 0.21/0.48    ( ! [X0] : (~v5_relat_1(sK2,X0) | k6_relat_1(k2_relat_1(sK2)) = k7_relat_1(k6_relat_1(k2_relat_1(sK2)),X0)) )),
% 0.21/0.48    inference(global_subsumption,[],[f65,f226])).
% 0.21/0.48  fof(f226,plain,(
% 0.21/0.48    ( ! [X0] : (k6_relat_1(k2_relat_1(sK2)) = k7_relat_1(k6_relat_1(k2_relat_1(sK2)),X0) | ~v5_relat_1(sK2,X0) | ~v1_relat_1(sK2)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f221,f88])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    k2_relat_1(sK2) = k9_relat_1(sK2,sK0)),
% 0.21/0.48    inference(superposition,[],[f81,f87])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    sK2 = k7_relat_1(sK2,sK0)),
% 0.21/0.48    inference(global_subsumption,[],[f65,f85])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    ~v1_relat_1(sK2) | sK2 = k7_relat_1(sK2,sK0)),
% 0.21/0.48    inference(resolution,[],[f50,f76])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    v4_relat_1(sK2,sK0)),
% 0.21/0.48    inference(resolution,[],[f54,f36])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f32])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | ~v1_relat_1(X1) | k7_relat_1(X1,X0) = X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    ( ! [X2] : (k2_relat_1(k7_relat_1(sK2,X2)) = k9_relat_1(sK2,X2)) )),
% 0.21/0.48    inference(resolution,[],[f45,f65])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.48  fof(f221,plain,(
% 0.21/0.48    ( ! [X0] : (~v5_relat_1(sK2,X0) | ~v1_relat_1(sK2) | k6_relat_1(k9_relat_1(sK2,sK0)) = k7_relat_1(k6_relat_1(k9_relat_1(sK2,sK0)),X0)) )),
% 0.21/0.48    inference(superposition,[],[f195,f87])).
% 0.21/0.48  fof(f195,plain,(
% 0.21/0.48    ( ! [X4,X3] : (~v5_relat_1(k7_relat_1(sK2,X3),X4) | ~v1_relat_1(k7_relat_1(sK2,X3)) | k6_relat_1(k9_relat_1(sK2,X3)) = k7_relat_1(k6_relat_1(k9_relat_1(sK2,X3)),X4)) )),
% 0.21/0.48    inference(resolution,[],[f190,f82])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK2,X0),X1) | ~v1_relat_1(k7_relat_1(sK2,X0)) | ~v5_relat_1(k7_relat_1(sK2,X0),X1)) )),
% 0.21/0.48    inference(superposition,[],[f48,f81])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v5_relat_1(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.48  fof(f190,plain,(
% 0.21/0.48    ( ! [X8,X7] : (~r1_tarski(X7,X8) | k6_relat_1(X7) = k7_relat_1(k6_relat_1(X7),X8)) )),
% 0.21/0.48    inference(global_subsumption,[],[f37,f183])).
% 0.21/0.48  fof(f183,plain,(
% 0.21/0.48    ( ! [X8,X7] : (~r1_tarski(X7,X8) | ~v1_relat_1(k6_relat_1(X7)) | k6_relat_1(X7) = k7_relat_1(k6_relat_1(X7),X8)) )),
% 0.21/0.48    inference(resolution,[],[f90,f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X0] : (v4_relat_1(k6_relat_1(X0),X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0] : (v5_relat_1(k6_relat_1(X0),X0) & v4_relat_1(k6_relat_1(X0),X0) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc24_relat_1)).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v4_relat_1(X0,X1) | ~r1_tarski(X1,X2) | ~v1_relat_1(X0) | k7_relat_1(X0,X2) = X0) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f89])).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v4_relat_1(X0,X1) | ~r1_tarski(X1,X2) | ~v1_relat_1(X0) | k7_relat_1(X0,X2) = X0) )),
% 0.21/0.48    inference(resolution,[],[f49,f50])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v4_relat_1(X2,X1) | ~v1_relat_1(X2) | ~v4_relat_1(X2,X0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X1) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2)) | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(flattening,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X1) | (~v4_relat_1(X2,X0) | ~v1_relat_1(X2))) | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : ((v4_relat_1(X2,X0) & v1_relat_1(X2)) => v4_relat_1(X2,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t217_relat_1)).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f121,plain,(
% 0.21/0.48    ( ! [X6,X7] : (k3_xboole_0(X6,X7) = k1_relat_1(k7_relat_1(k6_relat_1(X6),X7))) )),
% 0.21/0.48    inference(superposition,[],[f40,f112])).
% 0.21/0.48  fof(f112,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k6_relat_1(k3_xboole_0(X0,X1)) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 0.21/0.48    inference(backward_demodulation,[],[f43,f78])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 0.21/0.49    inference(resolution,[],[f44,f37])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    ( ! [X2] : (k10_relat_1(sK2,X2) = k10_relat_1(sK2,k3_xboole_0(k2_relat_1(sK2),X2))) )),
% 0.21/0.49    inference(resolution,[],[f46,f65])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).
% 0.21/0.49  fof(f107,plain,(
% 0.21/0.49    k1_relat_1(sK2) != k10_relat_1(sK2,sK1) | spl3_1),
% 0.21/0.49    inference(superposition,[],[f95,f103])).
% 0.21/0.49  fof(f103,plain,(
% 0.21/0.49    ( ! [X0] : (k10_relat_1(sK2,X0) = k8_relset_1(sK0,sK1,sK2,X0)) )),
% 0.21/0.49    inference(resolution,[],[f57,f36])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    k8_relset_1(sK0,sK1,sK2,sK1) != k1_relat_1(sK2) | spl3_1),
% 0.21/0.49    inference(backward_demodulation,[],[f60,f94])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 0.21/0.49    inference(resolution,[],[f52,f36])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) | spl3_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f59])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    spl3_1 <=> k1_relset_1(sK0,sK1,sK2) = k8_relset_1(sK0,sK1,sK2,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.49  fof(f106,plain,(
% 0.21/0.49    spl3_2),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f105])).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    $false | spl3_2),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f104])).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    k2_relat_1(sK2) != k2_relat_1(sK2) | spl3_2),
% 0.21/0.49    inference(superposition,[],[f102,f88])).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    k2_relat_1(sK2) != k9_relat_1(sK2,sK0) | spl3_2),
% 0.21/0.49    inference(superposition,[],[f101,f100])).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    ( ! [X0] : (k9_relat_1(sK2,X0) = k7_relset_1(sK0,sK1,sK2,X0)) )),
% 0.21/0.49    inference(resolution,[],[f56,f36])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    k7_relset_1(sK0,sK1,sK2,sK0) != k2_relat_1(sK2) | spl3_2),
% 0.21/0.49    inference(backward_demodulation,[],[f63,f98])).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.21/0.49    inference(resolution,[],[f53,f36])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0) | spl3_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f62])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    spl3_2 <=> k2_relset_1(sK0,sK1,sK2) = k7_relset_1(sK0,sK1,sK2,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    ~spl3_1 | ~spl3_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f35,f62,f59])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0) | k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (1818)------------------------------
% 0.21/0.49  % (1818)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (1818)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (1818)Memory used [KB]: 10874
% 0.21/0.49  % (1818)Time elapsed: 0.071 s
% 0.21/0.49  % (1818)------------------------------
% 0.21/0.49  % (1818)------------------------------
% 0.21/0.49  % (1805)Success in time 0.133 s
%------------------------------------------------------------------------------
