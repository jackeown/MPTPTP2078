%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:12 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 402 expanded)
%              Number of leaves         :   29 ( 107 expanded)
%              Depth                    :   20
%              Number of atoms          :  417 (1058 expanded)
%              Number of equality atoms :  149 ( 471 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1688,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f96,f275,f757,f771,f1683,f1687])).

fof(f1687,plain,
    ( spl3_2
    | ~ spl3_6 ),
    inference(avatar_contradiction_clause,[],[f1686])).

fof(f1686,plain,
    ( $false
    | spl3_2
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f770,f798])).

fof(f798,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | spl3_2 ),
    inference(subsumption_resolution,[],[f797,f105])).

fof(f105,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f82,f55])).

fof(f55,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,
    ( ( k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)
      | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f50])).

fof(f50,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1)
          | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)
        | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1)
        | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
          & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f797,plain,
    ( ~ v1_relat_1(sK2)
    | ~ r1_tarski(k2_relat_1(sK2),sK1)
    | spl3_2 ),
    inference(trivial_inequality_removal,[],[f796])).

fof(f796,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ r1_tarski(k2_relat_1(sK2),sK1)
    | spl3_2 ),
    inference(superposition,[],[f279,f306])).

fof(f306,plain,(
    ! [X2,X3] :
      ( k1_relat_1(X2) = k10_relat_1(X2,X3)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),X3) ) ),
    inference(duplicate_literal_removal,[],[f296])).

fof(f296,plain,(
    ! [X2,X3] :
      ( k1_relat_1(X2) = k10_relat_1(X2,X3)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),X3)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f183,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

fof(f183,plain,(
    ! [X2,X1] :
      ( k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))) = k10_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f174,f60])).

fof(f60,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f174,plain,(
    ! [X2,X1] :
      ( k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))) = k10_relat_1(X2,X1)
      | ~ v1_relat_1(k6_relat_1(X1))
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f65,f61])).

fof(f61,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f279,plain,
    ( k10_relat_1(sK2,sK1) != k1_relat_1(sK2)
    | spl3_2 ),
    inference(subsumption_resolution,[],[f278,f55])).

fof(f278,plain,
    ( k10_relat_1(sK2,sK1) != k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl3_2 ),
    inference(superposition,[],[f277,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f277,plain,
    ( k1_relset_1(sK0,sK1,sK2) != k10_relat_1(sK2,sK1)
    | spl3_2 ),
    inference(subsumption_resolution,[],[f276,f55])).

fof(f276,plain,
    ( k1_relset_1(sK0,sK1,sK2) != k10_relat_1(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl3_2 ),
    inference(superposition,[],[f95,f87])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f95,plain,
    ( k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl3_2
  <=> k1_relset_1(sK0,sK1,sK2) = k8_relset_1(sK0,sK1,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f770,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f769])).

fof(f769,plain,
    ( spl3_6
  <=> r1_tarski(k2_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f1683,plain,
    ( spl3_2
    | ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f1682])).

fof(f1682,plain,
    ( $false
    | spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f1681,f59])).

fof(f59,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f1681,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | spl3_2
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f1676,f58])).

fof(f58,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f1676,plain,
    ( ~ r1_tarski(k2_relat_1(k1_xboole_0),sK1)
    | spl3_2
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f798,f1610])).

fof(f1610,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_3 ),
    inference(resolution,[],[f1537,f778])).

fof(f778,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f775,f89])).

fof(f89,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f775,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(k1_xboole_0,sK1))
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f99,f331])).

fof(f331,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f330])).

fof(f330,plain,
    ( spl3_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f99,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f75,f55])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f1537,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | k1_xboole_0 = X1 ) ),
    inference(forward_demodulation,[],[f1500,f57])).

fof(f57,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f1500,plain,(
    ! [X1] :
      ( k1_relat_1(k1_xboole_0) = X1
      | ~ r1_tarski(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f61,f590])).

fof(f590,plain,(
    ! [X0] :
      ( k1_xboole_0 = k6_relat_1(X0)
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f544,f59])).

fof(f544,plain,(
    ! [X0] :
      ( k1_xboole_0 = k6_relat_1(X0)
      | ~ r1_tarski(X0,k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,X0) ) ),
    inference(superposition,[],[f249,f198])).

fof(f198,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(equality_resolution,[],[f111])).

fof(f111,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k6_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f110,f60])).

fof(f110,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k6_relat_1(X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f63,f61])).

fof(f63,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f249,plain,(
    ! [X2,X3] :
      ( k6_relat_1(X3) = k6_relat_1(X2)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X3,X2) ) ),
    inference(forward_demodulation,[],[f248,f61])).

fof(f248,plain,(
    ! [X2,X3] :
      ( k6_relat_1(X3) = k6_relat_1(X2)
      | ~ r1_tarski(X3,X2)
      | ~ r1_tarski(k1_relat_1(k6_relat_1(X2)),X3) ) ),
    inference(subsumption_resolution,[],[f243,f60])).

fof(f243,plain,(
    ! [X2,X3] :
      ( k6_relat_1(X3) = k6_relat_1(X2)
      | ~ r1_tarski(X3,X2)
      | ~ r1_tarski(k1_relat_1(k6_relat_1(X2)),X3)
      | ~ v1_relat_1(k6_relat_1(X2)) ) ),
    inference(superposition,[],[f151,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f151,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(forward_demodulation,[],[f150,f62])).

fof(f62,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f150,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(k6_relat_1(X0)),X1) ) ),
    inference(subsumption_resolution,[],[f149,f60])).

fof(f149,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(k6_relat_1(X0)),X1)
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(subsumption_resolution,[],[f147,f60])).

fof(f147,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(k6_relat_1(X0)),X1)
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(superposition,[],[f72,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f771,plain,
    ( spl3_3
    | spl3_4
    | spl3_6 ),
    inference(avatar_split_clause,[],[f763,f769,f333,f330])).

fof(f333,plain,
    ( spl3_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f763,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f99,f171])).

fof(f171,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k2_zfmisc_1(X0,X1))
      | r1_tarski(k2_relat_1(X2),X1)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f170,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f82,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f170,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(X2,k2_zfmisc_1(X0,X1))
      | ~ v1_relat_1(X2)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f167,f68])).

fof(f68,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f167,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(X2,k2_zfmisc_1(X0,X1))
      | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
      | ~ v1_relat_1(X2)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f67,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
        & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(f757,plain,
    ( spl3_2
    | ~ spl3_4 ),
    inference(avatar_contradiction_clause,[],[f756])).

fof(f756,plain,
    ( $false
    | spl3_2
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f755,f344])).

fof(f344,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f342,f88])).

fof(f88,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f342,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,k1_xboole_0))
    | ~ spl3_4 ),
    inference(backward_demodulation,[],[f99,f334])).

fof(f334,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f333])).

fof(f755,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | spl3_2
    | ~ spl3_4 ),
    inference(resolution,[],[f754,f145])).

fof(f145,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(X0),k1_xboole_0)
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f144,f123])).

fof(f123,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f107,f76])).

fof(f107,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | v1_relat_1(X1) ) ),
    inference(superposition,[],[f82,f88])).

fof(f144,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(X0),k1_xboole_0)
      | ~ r1_tarski(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f140,f97])).

fof(f97,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f68,f88])).

fof(f140,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(X0),k1_xboole_0)
      | ~ r1_tarski(X0,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f67,f58])).

fof(f754,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k1_xboole_0)
    | spl3_2
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f723,f105])).

fof(f723,plain,
    ( ~ v1_relat_1(sK2)
    | ~ r1_tarski(k2_relat_1(sK2),k1_xboole_0)
    | spl3_2
    | ~ spl3_4 ),
    inference(trivial_inequality_removal,[],[f722])).

fof(f722,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ r1_tarski(k2_relat_1(sK2),k1_xboole_0)
    | spl3_2
    | ~ spl3_4 ),
    inference(superposition,[],[f339,f306])).

fof(f339,plain,
    ( k1_relat_1(sK2) != k10_relat_1(sK2,k1_xboole_0)
    | spl3_2
    | ~ spl3_4 ),
    inference(backward_demodulation,[],[f279,f334])).

fof(f275,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f274])).

fof(f274,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f273,f114])).

fof(f114,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(resolution,[],[f85,f55])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f273,plain,
    ( ~ v4_relat_1(sK2,sK0)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f272,f105])).

fof(f272,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v4_relat_1(sK2,sK0)
    | spl3_1 ),
    inference(trivial_inequality_removal,[],[f271])).

fof(f271,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v4_relat_1(sK2,sK0)
    | spl3_1 ),
    inference(superposition,[],[f197,f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k9_relat_1(X0,X1)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k9_relat_1(X0,X1)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f71,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f71,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f197,plain,
    ( k9_relat_1(sK2,sK0) != k2_relat_1(sK2)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f196,f55])).

fof(f196,plain,
    ( k9_relat_1(sK2,sK0) != k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl3_1 ),
    inference(superposition,[],[f195,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f195,plain,
    ( k2_relset_1(sK0,sK1,sK2) != k9_relat_1(sK2,sK0)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f194,f55])).

fof(f194,plain,
    ( k2_relset_1(sK0,sK1,sK2) != k9_relat_1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl3_1 ),
    inference(superposition,[],[f92,f86])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f92,plain,
    ( k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl3_1
  <=> k2_relset_1(sK0,sK1,sK2) = k7_relset_1(sK0,sK1,sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f96,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f56,f94,f91])).

fof(f56,plain,
    ( k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)
    | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0) ),
    inference(cnf_transformation,[],[f51])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:08:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (12330)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.48  % (12337)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.49  % (12338)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.50  % (12333)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (12329)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (12334)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.50  % (12343)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.50  % (12339)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.50  % (12329)Refutation not found, incomplete strategy% (12329)------------------------------
% 0.22/0.50  % (12329)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (12329)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (12329)Memory used [KB]: 10618
% 0.22/0.50  % (12329)Time elapsed: 0.067 s
% 0.22/0.50  % (12329)------------------------------
% 0.22/0.50  % (12329)------------------------------
% 0.22/0.50  % (12335)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.51  % (12328)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (12346)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.51  % (12332)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.51  % (12347)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.52  % (12331)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (12340)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (12348)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.52  % (12348)Refutation not found, incomplete strategy% (12348)------------------------------
% 0.22/0.52  % (12348)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (12348)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (12348)Memory used [KB]: 10618
% 0.22/0.52  % (12348)Time elapsed: 0.104 s
% 0.22/0.52  % (12348)------------------------------
% 0.22/0.52  % (12348)------------------------------
% 0.22/0.52  % (12336)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.53  % (12341)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.53  % (12342)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.53  % (12341)Refutation not found, incomplete strategy% (12341)------------------------------
% 0.22/0.53  % (12341)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (12341)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (12341)Memory used [KB]: 1663
% 0.22/0.53  % (12341)Time elapsed: 0.118 s
% 0.22/0.53  % (12341)------------------------------
% 0.22/0.53  % (12341)------------------------------
% 0.22/0.53  % (12345)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.53  % (12344)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.54  % (12331)Refutation not found, incomplete strategy% (12331)------------------------------
% 0.22/0.54  % (12331)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (12331)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (12331)Memory used [KB]: 10746
% 0.22/0.54  % (12331)Time elapsed: 0.105 s
% 0.22/0.54  % (12331)------------------------------
% 0.22/0.54  % (12331)------------------------------
% 0.22/0.54  % (12338)Refutation not found, incomplete strategy% (12338)------------------------------
% 0.22/0.54  % (12338)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (12338)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (12338)Memory used [KB]: 6908
% 0.22/0.54  % (12338)Time elapsed: 0.118 s
% 0.22/0.54  % (12338)------------------------------
% 0.22/0.54  % (12338)------------------------------
% 0.22/0.55  % (12330)Refutation found. Thanks to Tanya!
% 0.22/0.55  % SZS status Theorem for theBenchmark
% 0.22/0.55  % SZS output start Proof for theBenchmark
% 0.22/0.55  fof(f1688,plain,(
% 0.22/0.55    $false),
% 0.22/0.55    inference(avatar_sat_refutation,[],[f96,f275,f757,f771,f1683,f1687])).
% 0.22/0.55  fof(f1687,plain,(
% 0.22/0.55    spl3_2 | ~spl3_6),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f1686])).
% 0.22/0.55  fof(f1686,plain,(
% 0.22/0.55    $false | (spl3_2 | ~spl3_6)),
% 0.22/0.55    inference(subsumption_resolution,[],[f770,f798])).
% 0.22/0.55  fof(f798,plain,(
% 0.22/0.55    ~r1_tarski(k2_relat_1(sK2),sK1) | spl3_2),
% 0.22/0.55    inference(subsumption_resolution,[],[f797,f105])).
% 0.22/0.55  fof(f105,plain,(
% 0.22/0.55    v1_relat_1(sK2)),
% 0.22/0.55    inference(resolution,[],[f82,f55])).
% 0.22/0.55  fof(f55,plain,(
% 0.22/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.55    inference(cnf_transformation,[],[f51])).
% 0.22/0.55  fof(f51,plain,(
% 0.22/0.55    (k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f50])).
% 0.22/0.55  fof(f50,plain,(
% 0.22/0.55    ? [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1) | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f28,plain,(
% 0.22/0.55    ? [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1) | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f25])).
% 0.22/0.55  fof(f25,negated_conjecture,(
% 0.22/0.55    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 0.22/0.55    inference(negated_conjecture,[],[f24])).
% 0.22/0.55  fof(f24,conjecture,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).
% 0.22/0.55  fof(f82,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f44])).
% 0.22/0.55  fof(f44,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f18])).
% 0.22/0.55  fof(f18,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.55  fof(f797,plain,(
% 0.22/0.55    ~v1_relat_1(sK2) | ~r1_tarski(k2_relat_1(sK2),sK1) | spl3_2),
% 0.22/0.55    inference(trivial_inequality_removal,[],[f796])).
% 0.22/0.55  fof(f796,plain,(
% 0.22/0.55    k1_relat_1(sK2) != k1_relat_1(sK2) | ~v1_relat_1(sK2) | ~r1_tarski(k2_relat_1(sK2),sK1) | spl3_2),
% 0.22/0.55    inference(superposition,[],[f279,f306])).
% 0.22/0.55  fof(f306,plain,(
% 0.22/0.55    ( ! [X2,X3] : (k1_relat_1(X2) = k10_relat_1(X2,X3) | ~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),X3)) )),
% 0.22/0.55    inference(duplicate_literal_removal,[],[f296])).
% 0.22/0.55  fof(f296,plain,(
% 0.22/0.55    ( ! [X2,X3] : (k1_relat_1(X2) = k10_relat_1(X2,X3) | ~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),X3) | ~v1_relat_1(X2)) )),
% 0.22/0.55    inference(superposition,[],[f183,f72])).
% 0.22/0.55  fof(f72,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f38])).
% 0.22/0.55  fof(f38,plain,(
% 0.22/0.55    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(flattening,[],[f37])).
% 0.22/0.55  fof(f37,plain,(
% 0.22/0.55    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f14])).
% 0.22/0.55  fof(f14,axiom,(
% 0.22/0.55    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).
% 0.22/0.55  fof(f183,plain,(
% 0.22/0.55    ( ! [X2,X1] : (k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))) = k10_relat_1(X2,X1) | ~v1_relat_1(X2)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f174,f60])).
% 0.22/0.55  fof(f60,plain,(
% 0.22/0.55    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f27])).
% 0.22/0.55  fof(f27,plain,(
% 0.22/0.55    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.55    inference(pure_predicate_removal,[],[f17])).
% 0.22/0.55  fof(f17,axiom,(
% 0.22/0.55    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.22/0.55  fof(f174,plain,(
% 0.22/0.55    ( ! [X2,X1] : (k1_relat_1(k5_relat_1(X2,k6_relat_1(X1))) = k10_relat_1(X2,X1) | ~v1_relat_1(k6_relat_1(X1)) | ~v1_relat_1(X2)) )),
% 0.22/0.55    inference(superposition,[],[f65,f61])).
% 0.22/0.55  fof(f61,plain,(
% 0.22/0.55    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.55    inference(cnf_transformation,[],[f13])).
% 0.22/0.55  fof(f13,axiom,(
% 0.22/0.55    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.22/0.55  fof(f65,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f31])).
% 0.22/0.55  fof(f31,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f7])).
% 0.22/0.55  fof(f7,axiom,(
% 0.22/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 0.22/0.55  fof(f279,plain,(
% 0.22/0.55    k10_relat_1(sK2,sK1) != k1_relat_1(sK2) | spl3_2),
% 0.22/0.55    inference(subsumption_resolution,[],[f278,f55])).
% 0.22/0.55  fof(f278,plain,(
% 0.22/0.55    k10_relat_1(sK2,sK1) != k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl3_2),
% 0.22/0.55    inference(superposition,[],[f277,f84])).
% 0.22/0.55  fof(f84,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f46])).
% 0.22/0.55  fof(f46,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f20])).
% 0.22/0.55  fof(f20,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.55  fof(f277,plain,(
% 0.22/0.55    k1_relset_1(sK0,sK1,sK2) != k10_relat_1(sK2,sK1) | spl3_2),
% 0.22/0.55    inference(subsumption_resolution,[],[f276,f55])).
% 0.22/0.55  fof(f276,plain,(
% 0.22/0.55    k1_relset_1(sK0,sK1,sK2) != k10_relat_1(sK2,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl3_2),
% 0.22/0.55    inference(superposition,[],[f95,f87])).
% 0.22/0.55  fof(f87,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f49])).
% 0.22/0.55  fof(f49,plain,(
% 0.22/0.55    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f23])).
% 0.22/0.55  fof(f23,axiom,(
% 0.22/0.55    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.22/0.55  fof(f95,plain,(
% 0.22/0.55    k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) | spl3_2),
% 0.22/0.55    inference(avatar_component_clause,[],[f94])).
% 0.22/0.55  fof(f94,plain,(
% 0.22/0.55    spl3_2 <=> k1_relset_1(sK0,sK1,sK2) = k8_relset_1(sK0,sK1,sK2,sK1)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.55  fof(f770,plain,(
% 0.22/0.55    r1_tarski(k2_relat_1(sK2),sK1) | ~spl3_6),
% 0.22/0.55    inference(avatar_component_clause,[],[f769])).
% 0.22/0.55  fof(f769,plain,(
% 0.22/0.55    spl3_6 <=> r1_tarski(k2_relat_1(sK2),sK1)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.55  fof(f1683,plain,(
% 0.22/0.55    spl3_2 | ~spl3_3),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f1682])).
% 0.22/0.55  fof(f1682,plain,(
% 0.22/0.55    $false | (spl3_2 | ~spl3_3)),
% 0.22/0.55    inference(subsumption_resolution,[],[f1681,f59])).
% 0.22/0.55  fof(f59,plain,(
% 0.22/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f1])).
% 0.22/0.55  fof(f1,axiom,(
% 0.22/0.55    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.55  fof(f1681,plain,(
% 0.22/0.55    ~r1_tarski(k1_xboole_0,sK1) | (spl3_2 | ~spl3_3)),
% 0.22/0.55    inference(forward_demodulation,[],[f1676,f58])).
% 0.22/0.55  fof(f58,plain,(
% 0.22/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.55    inference(cnf_transformation,[],[f11])).
% 0.22/0.55  fof(f11,axiom,(
% 0.22/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.55  fof(f1676,plain,(
% 0.22/0.55    ~r1_tarski(k2_relat_1(k1_xboole_0),sK1) | (spl3_2 | ~spl3_3)),
% 0.22/0.55    inference(backward_demodulation,[],[f798,f1610])).
% 0.22/0.55  fof(f1610,plain,(
% 0.22/0.55    k1_xboole_0 = sK2 | ~spl3_3),
% 0.22/0.55    inference(resolution,[],[f1537,f778])).
% 0.22/0.55  fof(f778,plain,(
% 0.22/0.55    r1_tarski(sK2,k1_xboole_0) | ~spl3_3),
% 0.22/0.55    inference(forward_demodulation,[],[f775,f89])).
% 0.22/0.55  fof(f89,plain,(
% 0.22/0.55    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.22/0.55    inference(equality_resolution,[],[f78])).
% 0.22/0.55  fof(f78,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.22/0.55    inference(cnf_transformation,[],[f54])).
% 0.22/0.55  fof(f54,plain,(
% 0.22/0.55    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.55    inference(flattening,[],[f53])).
% 0.22/0.55  fof(f53,plain,(
% 0.22/0.55    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.55    inference(nnf_transformation,[],[f2])).
% 0.22/0.55  fof(f2,axiom,(
% 0.22/0.55    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.55  fof(f775,plain,(
% 0.22/0.55    r1_tarski(sK2,k2_zfmisc_1(k1_xboole_0,sK1)) | ~spl3_3),
% 0.22/0.55    inference(backward_demodulation,[],[f99,f331])).
% 0.22/0.55  fof(f331,plain,(
% 0.22/0.55    k1_xboole_0 = sK0 | ~spl3_3),
% 0.22/0.55    inference(avatar_component_clause,[],[f330])).
% 0.22/0.55  fof(f330,plain,(
% 0.22/0.55    spl3_3 <=> k1_xboole_0 = sK0),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.55  fof(f99,plain,(
% 0.22/0.55    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.22/0.55    inference(resolution,[],[f75,f55])).
% 0.22/0.55  fof(f75,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f52])).
% 0.22/0.55  fof(f52,plain,(
% 0.22/0.55    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.55    inference(nnf_transformation,[],[f3])).
% 0.22/0.55  fof(f3,axiom,(
% 0.22/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.55  fof(f1537,plain,(
% 0.22/0.55    ( ! [X1] : (~r1_tarski(X1,k1_xboole_0) | k1_xboole_0 = X1) )),
% 0.22/0.55    inference(forward_demodulation,[],[f1500,f57])).
% 0.22/0.55  fof(f57,plain,(
% 0.22/0.55    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.55    inference(cnf_transformation,[],[f11])).
% 0.22/0.55  fof(f1500,plain,(
% 0.22/0.55    ( ! [X1] : (k1_relat_1(k1_xboole_0) = X1 | ~r1_tarski(X1,k1_xboole_0)) )),
% 0.22/0.55    inference(superposition,[],[f61,f590])).
% 0.22/0.55  fof(f590,plain,(
% 0.22/0.55    ( ! [X0] : (k1_xboole_0 = k6_relat_1(X0) | ~r1_tarski(X0,k1_xboole_0)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f544,f59])).
% 0.22/0.55  fof(f544,plain,(
% 0.22/0.55    ( ! [X0] : (k1_xboole_0 = k6_relat_1(X0) | ~r1_tarski(X0,k1_xboole_0) | ~r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.55    inference(superposition,[],[f249,f198])).
% 0.22/0.55  fof(f198,plain,(
% 0.22/0.55    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.22/0.55    inference(equality_resolution,[],[f111])).
% 0.22/0.55  fof(f111,plain,(
% 0.22/0.55    ( ! [X0] : (k1_xboole_0 != X0 | k1_xboole_0 = k6_relat_1(X0)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f110,f60])).
% 0.22/0.55  fof(f110,plain,(
% 0.22/0.55    ( ! [X0] : (k1_xboole_0 != X0 | k1_xboole_0 = k6_relat_1(X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.55    inference(superposition,[],[f63,f61])).
% 0.22/0.55  fof(f63,plain,(
% 0.22/0.55    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f30])).
% 0.22/0.55  fof(f30,plain,(
% 0.22/0.55    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(flattening,[],[f29])).
% 0.22/0.55  fof(f29,plain,(
% 0.22/0.55    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f12])).
% 0.22/0.55  fof(f12,axiom,(
% 0.22/0.55    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.22/0.55  fof(f249,plain,(
% 0.22/0.55    ( ! [X2,X3] : (k6_relat_1(X3) = k6_relat_1(X2) | ~r1_tarski(X2,X3) | ~r1_tarski(X3,X2)) )),
% 0.22/0.55    inference(forward_demodulation,[],[f248,f61])).
% 0.22/0.55  fof(f248,plain,(
% 0.22/0.55    ( ! [X2,X3] : (k6_relat_1(X3) = k6_relat_1(X2) | ~r1_tarski(X3,X2) | ~r1_tarski(k1_relat_1(k6_relat_1(X2)),X3)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f243,f60])).
% 0.22/0.55  fof(f243,plain,(
% 0.22/0.55    ( ! [X2,X3] : (k6_relat_1(X3) = k6_relat_1(X2) | ~r1_tarski(X3,X2) | ~r1_tarski(k1_relat_1(k6_relat_1(X2)),X3) | ~v1_relat_1(k6_relat_1(X2))) )),
% 0.22/0.55    inference(superposition,[],[f151,f73])).
% 0.22/0.55  fof(f73,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f40])).
% 0.22/0.55  fof(f40,plain,(
% 0.22/0.55    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(flattening,[],[f39])).
% 0.22/0.55  fof(f39,plain,(
% 0.22/0.55    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f16])).
% 0.22/0.55  fof(f16,axiom,(
% 0.22/0.55    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 0.22/0.55  fof(f151,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0) | ~r1_tarski(X0,X1)) )),
% 0.22/0.55    inference(forward_demodulation,[],[f150,f62])).
% 0.22/0.55  fof(f62,plain,(
% 0.22/0.55    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.55    inference(cnf_transformation,[],[f13])).
% 0.22/0.55  fof(f150,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(k6_relat_1(X0)),X1)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f149,f60])).
% 0.22/0.55  fof(f149,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(k6_relat_1(X0)),X1) | ~v1_relat_1(k6_relat_1(X1))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f147,f60])).
% 0.22/0.55  fof(f147,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(k6_relat_1(X0)),X1) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X1))) )),
% 0.22/0.55    inference(superposition,[],[f72,f70])).
% 0.22/0.55  fof(f70,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f35])).
% 0.22/0.55  fof(f35,plain,(
% 0.22/0.55    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f15])).
% 0.22/0.55  fof(f15,axiom,(
% 0.22/0.55    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 0.22/0.55  fof(f771,plain,(
% 0.22/0.55    spl3_3 | spl3_4 | spl3_6),
% 0.22/0.55    inference(avatar_split_clause,[],[f763,f769,f333,f330])).
% 0.22/0.55  fof(f333,plain,(
% 0.22/0.55    spl3_4 <=> k1_xboole_0 = sK1),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.55  fof(f763,plain,(
% 0.22/0.55    r1_tarski(k2_relat_1(sK2),sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.22/0.55    inference(resolution,[],[f99,f171])).
% 0.22/0.55  fof(f171,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~r1_tarski(X2,k2_zfmisc_1(X0,X1)) | r1_tarski(k2_relat_1(X2),X1) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f170,f106])).
% 0.22/0.55  fof(f106,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | v1_relat_1(X0)) )),
% 0.22/0.55    inference(resolution,[],[f82,f76])).
% 0.22/0.55  fof(f76,plain,(
% 0.22/0.55    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f52])).
% 0.22/0.55  fof(f170,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(X2,k2_zfmisc_1(X0,X1)) | ~v1_relat_1(X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f167,f68])).
% 0.22/0.55  fof(f68,plain,(
% 0.22/0.55    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f4])).
% 0.22/0.55  fof(f4,axiom,(
% 0.22/0.55    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.55  fof(f167,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(X2,k2_zfmisc_1(X0,X1)) | ~v1_relat_1(k2_zfmisc_1(X0,X1)) | ~v1_relat_1(X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.55    inference(superposition,[],[f67,f81])).
% 0.22/0.55  fof(f81,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.55    inference(cnf_transformation,[],[f43])).
% 0.22/0.55  fof(f43,plain,(
% 0.22/0.55    ! [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.22/0.55    inference(ennf_transformation,[],[f8])).
% 0.22/0.55  fof(f8,axiom,(
% 0.22/0.55    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).
% 0.22/0.55  fof(f67,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f33])).
% 0.22/0.55  fof(f33,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(flattening,[],[f32])).
% 0.22/0.55  fof(f32,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f10])).
% 0.22/0.55  fof(f10,axiom,(
% 0.22/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).
% 0.22/0.55  fof(f757,plain,(
% 0.22/0.55    spl3_2 | ~spl3_4),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f756])).
% 0.22/0.55  fof(f756,plain,(
% 0.22/0.55    $false | (spl3_2 | ~spl3_4)),
% 0.22/0.55    inference(subsumption_resolution,[],[f755,f344])).
% 0.22/0.55  fof(f344,plain,(
% 0.22/0.55    r1_tarski(sK2,k1_xboole_0) | ~spl3_4),
% 0.22/0.55    inference(forward_demodulation,[],[f342,f88])).
% 0.22/0.55  fof(f88,plain,(
% 0.22/0.55    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.55    inference(equality_resolution,[],[f79])).
% 0.22/0.55  fof(f79,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.22/0.55    inference(cnf_transformation,[],[f54])).
% 0.22/0.55  fof(f342,plain,(
% 0.22/0.55    r1_tarski(sK2,k2_zfmisc_1(sK0,k1_xboole_0)) | ~spl3_4),
% 0.22/0.55    inference(backward_demodulation,[],[f99,f334])).
% 0.22/0.55  fof(f334,plain,(
% 0.22/0.55    k1_xboole_0 = sK1 | ~spl3_4),
% 0.22/0.55    inference(avatar_component_clause,[],[f333])).
% 0.22/0.55  fof(f755,plain,(
% 0.22/0.55    ~r1_tarski(sK2,k1_xboole_0) | (spl3_2 | ~spl3_4)),
% 0.22/0.55    inference(resolution,[],[f754,f145])).
% 0.22/0.55  fof(f145,plain,(
% 0.22/0.55    ( ! [X0] : (r1_tarski(k2_relat_1(X0),k1_xboole_0) | ~r1_tarski(X0,k1_xboole_0)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f144,f123])).
% 0.22/0.55  fof(f123,plain,(
% 0.22/0.55    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | v1_relat_1(X0)) )),
% 0.22/0.55    inference(resolution,[],[f107,f76])).
% 0.22/0.55  fof(f107,plain,(
% 0.22/0.55    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | v1_relat_1(X1)) )),
% 0.22/0.55    inference(superposition,[],[f82,f88])).
% 0.22/0.55  fof(f144,plain,(
% 0.22/0.55    ( ! [X0] : (r1_tarski(k2_relat_1(X0),k1_xboole_0) | ~r1_tarski(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f140,f97])).
% 0.22/0.55  fof(f97,plain,(
% 0.22/0.55    v1_relat_1(k1_xboole_0)),
% 0.22/0.55    inference(superposition,[],[f68,f88])).
% 0.22/0.55  fof(f140,plain,(
% 0.22/0.55    ( ! [X0] : (r1_tarski(k2_relat_1(X0),k1_xboole_0) | ~r1_tarski(X0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.22/0.55    inference(superposition,[],[f67,f58])).
% 0.22/0.55  fof(f754,plain,(
% 0.22/0.55    ~r1_tarski(k2_relat_1(sK2),k1_xboole_0) | (spl3_2 | ~spl3_4)),
% 0.22/0.55    inference(subsumption_resolution,[],[f723,f105])).
% 0.22/0.55  fof(f723,plain,(
% 0.22/0.55    ~v1_relat_1(sK2) | ~r1_tarski(k2_relat_1(sK2),k1_xboole_0) | (spl3_2 | ~spl3_4)),
% 0.22/0.55    inference(trivial_inequality_removal,[],[f722])).
% 0.22/0.55  fof(f722,plain,(
% 0.22/0.55    k1_relat_1(sK2) != k1_relat_1(sK2) | ~v1_relat_1(sK2) | ~r1_tarski(k2_relat_1(sK2),k1_xboole_0) | (spl3_2 | ~spl3_4)),
% 0.22/0.55    inference(superposition,[],[f339,f306])).
% 0.22/0.55  fof(f339,plain,(
% 0.22/0.55    k1_relat_1(sK2) != k10_relat_1(sK2,k1_xboole_0) | (spl3_2 | ~spl3_4)),
% 0.22/0.55    inference(backward_demodulation,[],[f279,f334])).
% 0.22/0.55  fof(f275,plain,(
% 0.22/0.55    spl3_1),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f274])).
% 0.22/0.55  fof(f274,plain,(
% 0.22/0.55    $false | spl3_1),
% 0.22/0.55    inference(subsumption_resolution,[],[f273,f114])).
% 0.22/0.55  fof(f114,plain,(
% 0.22/0.55    v4_relat_1(sK2,sK0)),
% 0.22/0.55    inference(resolution,[],[f85,f55])).
% 0.22/0.55  fof(f85,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f47])).
% 0.22/0.55  fof(f47,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f26])).
% 0.22/0.55  fof(f26,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.22/0.55    inference(pure_predicate_removal,[],[f19])).
% 0.22/0.55  fof(f19,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.55  fof(f273,plain,(
% 0.22/0.55    ~v4_relat_1(sK2,sK0) | spl3_1),
% 0.22/0.55    inference(subsumption_resolution,[],[f272,f105])).
% 0.22/0.55  fof(f272,plain,(
% 0.22/0.55    ~v1_relat_1(sK2) | ~v4_relat_1(sK2,sK0) | spl3_1),
% 0.22/0.55    inference(trivial_inequality_removal,[],[f271])).
% 0.22/0.55  fof(f271,plain,(
% 0.22/0.55    k2_relat_1(sK2) != k2_relat_1(sK2) | ~v1_relat_1(sK2) | ~v4_relat_1(sK2,sK0) | spl3_1),
% 0.22/0.55    inference(superposition,[],[f197,f120])).
% 0.22/0.55  fof(f120,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k2_relat_1(X0) = k9_relat_1(X0,X1) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1)) )),
% 0.22/0.55    inference(duplicate_literal_removal,[],[f119])).
% 0.22/0.55  fof(f119,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k2_relat_1(X0) = k9_relat_1(X0,X1) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1) | ~v1_relat_1(X0)) )),
% 0.22/0.55    inference(superposition,[],[f71,f74])).
% 0.22/0.55  fof(f74,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f42])).
% 0.22/0.55  fof(f42,plain,(
% 0.22/0.55    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(flattening,[],[f41])).
% 0.22/0.55  fof(f41,plain,(
% 0.22/0.55    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.55    inference(ennf_transformation,[],[f9])).
% 0.22/0.55  fof(f9,axiom,(
% 0.22/0.55    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.22/0.55  fof(f71,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f36])).
% 0.22/0.55  fof(f36,plain,(
% 0.22/0.55    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f5])).
% 0.22/0.55  fof(f5,axiom,(
% 0.22/0.55    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.22/0.55  fof(f197,plain,(
% 0.22/0.55    k9_relat_1(sK2,sK0) != k2_relat_1(sK2) | spl3_1),
% 0.22/0.55    inference(subsumption_resolution,[],[f196,f55])).
% 0.22/0.55  fof(f196,plain,(
% 0.22/0.55    k9_relat_1(sK2,sK0) != k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl3_1),
% 0.22/0.55    inference(superposition,[],[f195,f83])).
% 0.22/0.55  fof(f83,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f45])).
% 0.22/0.55  fof(f45,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f21])).
% 0.22/0.55  fof(f21,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.55  fof(f195,plain,(
% 0.22/0.55    k2_relset_1(sK0,sK1,sK2) != k9_relat_1(sK2,sK0) | spl3_1),
% 0.22/0.55    inference(subsumption_resolution,[],[f194,f55])).
% 0.22/0.55  fof(f194,plain,(
% 0.22/0.55    k2_relset_1(sK0,sK1,sK2) != k9_relat_1(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl3_1),
% 0.22/0.55    inference(superposition,[],[f92,f86])).
% 0.22/0.55  fof(f86,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f48])).
% 0.22/0.55  fof(f48,plain,(
% 0.22/0.55    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f22])).
% 0.22/0.55  fof(f22,axiom,(
% 0.22/0.55    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.22/0.55  fof(f92,plain,(
% 0.22/0.55    k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0) | spl3_1),
% 0.22/0.55    inference(avatar_component_clause,[],[f91])).
% 0.22/0.55  fof(f91,plain,(
% 0.22/0.55    spl3_1 <=> k2_relset_1(sK0,sK1,sK2) = k7_relset_1(sK0,sK1,sK2,sK0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.55  fof(f96,plain,(
% 0.22/0.55    ~spl3_1 | ~spl3_2),
% 0.22/0.55    inference(avatar_split_clause,[],[f56,f94,f91])).
% 0.22/0.55  fof(f56,plain,(
% 0.22/0.55    k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f51])).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (12330)------------------------------
% 0.22/0.55  % (12330)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (12330)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (12330)Memory used [KB]: 12153
% 0.22/0.55  % (12330)Time elapsed: 0.131 s
% 0.22/0.55  % (12330)------------------------------
% 0.22/0.55  % (12330)------------------------------
% 0.22/0.55  % (12327)Success in time 0.187 s
%------------------------------------------------------------------------------
