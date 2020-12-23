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
% DateTime   : Thu Dec  3 13:03:37 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 241 expanded)
%              Number of leaves         :   11 (  58 expanded)
%              Depth                    :   16
%              Number of atoms          :  224 (1160 expanded)
%              Number of equality atoms :   74 ( 378 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f123,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f87,f122])).

fof(f122,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f121])).

fof(f121,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f120,f95])).

fof(f95,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f30,f57])).

fof(f57,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f30,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2)))
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1) )
   => ( ~ r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2)))
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(sK2,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1) )
       => ( r1_tarski(X2,X0)
         => ( r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X2,X0)
         => ( r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_funct_2)).

fof(f120,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f74,f119])).

fof(f119,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f114,f103])).

fof(f103,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f94,f91])).

fof(f91,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl4_1
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f94,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f29,f57])).

fof(f29,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f26])).

fof(f114,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(superposition,[],[f110,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f110,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f106,f104])).

fof(f104,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f93,f91])).

fof(f93,plain,
    ( v1_funct_2(sK3,k1_xboole_0,sK1)
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f28,f57])).

fof(f28,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f106,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(resolution,[],[f103,f51])).

fof(f51,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f74,plain,(
    ~ r1_tarski(sK2,k1_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f73,f60])).

fof(f60,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f59,f35])).

fof(f35,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f59,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f34,f29])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f73,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f70,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f70,plain,(
    ~ r1_tarski(sK2,k10_relat_1(sK3,k9_relat_1(sK3,sK2))) ),
    inference(subsumption_resolution,[],[f69,f29])).

fof(f69,plain,
    ( ~ r1_tarski(sK2,k10_relat_1(sK3,k9_relat_1(sK3,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f66,f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f66,plain,(
    ~ r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k9_relat_1(sK3,sK2))) ),
    inference(subsumption_resolution,[],[f65,f29])).

fof(f65,plain,
    ( ~ r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k9_relat_1(sK3,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f32,f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f32,plain,(
    ~ r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2))) ),
    inference(cnf_transformation,[],[f26])).

fof(f87,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f86])).

fof(f86,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f85,f30])).

fof(f85,plain,
    ( ~ r1_tarski(sK2,sK0)
    | spl4_1 ),
    inference(backward_demodulation,[],[f74,f84])).

fof(f84,plain,
    ( sK0 = k1_relat_1(sK3)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f80,f29])).

fof(f80,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_1 ),
    inference(superposition,[],[f77,f37])).

fof(f77,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f76,f54])).

fof(f54,plain,
    ( k1_xboole_0 != sK1
    | spl4_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f76,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(subsumption_resolution,[],[f75,f28])).

fof(f75,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f38,f29])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f58,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f31,f56,f53])).

fof(f31,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:44:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.44  % (16198)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.44  % (16190)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.44  % (16190)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.44  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f123,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(avatar_sat_refutation,[],[f58,f87,f122])).
% 0.22/0.44  fof(f122,plain,(
% 0.22/0.44    ~spl4_1 | ~spl4_2),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f121])).
% 0.22/0.44  fof(f121,plain,(
% 0.22/0.44    $false | (~spl4_1 | ~spl4_2)),
% 0.22/0.44    inference(subsumption_resolution,[],[f120,f95])).
% 0.22/0.44  fof(f95,plain,(
% 0.22/0.44    r1_tarski(sK2,k1_xboole_0) | ~spl4_2),
% 0.22/0.44    inference(backward_demodulation,[],[f30,f57])).
% 0.22/0.44  fof(f57,plain,(
% 0.22/0.44    k1_xboole_0 = sK0 | ~spl4_2),
% 0.22/0.44    inference(avatar_component_clause,[],[f56])).
% 0.22/0.44  fof(f56,plain,(
% 0.22/0.44    spl4_2 <=> k1_xboole_0 = sK0),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.44  fof(f30,plain,(
% 0.22/0.44    r1_tarski(sK2,sK0)),
% 0.22/0.44    inference(cnf_transformation,[],[f26])).
% 0.22/0.44  fof(f26,plain,(
% 0.22/0.44    ~r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1)),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f25])).
% 0.22/0.44  fof(f25,plain,(
% 0.22/0.44    ? [X0,X1,X2,X3] : (~r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1)) => (~r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f14,plain,(
% 0.22/0.44    ? [X0,X1,X2,X3] : (~r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1))),
% 0.22/0.44    inference(flattening,[],[f13])).
% 0.22/0.44  fof(f13,plain,(
% 0.22/0.44    ? [X0,X1,X2,X3] : (((~r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1)))),
% 0.22/0.44    inference(ennf_transformation,[],[f12])).
% 0.22/0.44  fof(f12,plain,(
% 0.22/0.44    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1)) => (r1_tarski(X2,X0) => (r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.22/0.44    inference(pure_predicate_removal,[],[f11])).
% 0.22/0.44  fof(f11,negated_conjecture,(
% 0.22/0.44    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => (r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.22/0.44    inference(negated_conjecture,[],[f10])).
% 0.22/0.44  fof(f10,conjecture,(
% 0.22/0.44    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => (r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_funct_2)).
% 0.22/0.44  fof(f120,plain,(
% 0.22/0.44    ~r1_tarski(sK2,k1_xboole_0) | (~spl4_1 | ~spl4_2)),
% 0.22/0.44    inference(backward_demodulation,[],[f74,f119])).
% 0.22/0.44  fof(f119,plain,(
% 0.22/0.44    k1_xboole_0 = k1_relat_1(sK3) | (~spl4_1 | ~spl4_2)),
% 0.22/0.44    inference(subsumption_resolution,[],[f114,f103])).
% 0.22/0.44  fof(f103,plain,(
% 0.22/0.44    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl4_1 | ~spl4_2)),
% 0.22/0.44    inference(backward_demodulation,[],[f94,f91])).
% 0.22/0.44  fof(f91,plain,(
% 0.22/0.44    k1_xboole_0 = sK1 | ~spl4_1),
% 0.22/0.44    inference(avatar_component_clause,[],[f53])).
% 0.22/0.44  fof(f53,plain,(
% 0.22/0.44    spl4_1 <=> k1_xboole_0 = sK1),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.44  fof(f94,plain,(
% 0.22/0.44    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | ~spl4_2),
% 0.22/0.44    inference(backward_demodulation,[],[f29,f57])).
% 0.22/0.44  fof(f29,plain,(
% 0.22/0.44    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.44    inference(cnf_transformation,[],[f26])).
% 0.22/0.44  fof(f114,plain,(
% 0.22/0.44    k1_xboole_0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl4_1 | ~spl4_2)),
% 0.22/0.44    inference(superposition,[],[f110,f37])).
% 0.22/0.44  fof(f37,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f18])).
% 0.22/0.44  fof(f18,plain,(
% 0.22/0.44    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.44    inference(ennf_transformation,[],[f6])).
% 0.22/0.44  fof(f6,axiom,(
% 0.22/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.44  fof(f110,plain,(
% 0.22/0.44    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl4_1 | ~spl4_2)),
% 0.22/0.44    inference(subsumption_resolution,[],[f106,f104])).
% 0.22/0.44  fof(f104,plain,(
% 0.22/0.44    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl4_1 | ~spl4_2)),
% 0.22/0.44    inference(backward_demodulation,[],[f93,f91])).
% 0.22/0.44  fof(f93,plain,(
% 0.22/0.44    v1_funct_2(sK3,k1_xboole_0,sK1) | ~spl4_2),
% 0.22/0.44    inference(backward_demodulation,[],[f28,f57])).
% 0.22/0.44  fof(f28,plain,(
% 0.22/0.44    v1_funct_2(sK3,sK0,sK1)),
% 0.22/0.44    inference(cnf_transformation,[],[f26])).
% 0.22/0.44  fof(f106,plain,(
% 0.22/0.44    ~v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | (~spl4_1 | ~spl4_2)),
% 0.22/0.44    inference(resolution,[],[f103,f51])).
% 0.22/0.44  fof(f51,plain,(
% 0.22/0.44    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)) )),
% 0.22/0.44    inference(equality_resolution,[],[f39])).
% 0.22/0.44  fof(f39,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f27])).
% 0.22/0.44  fof(f27,plain,(
% 0.22/0.44    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.44    inference(nnf_transformation,[],[f20])).
% 0.22/0.44  fof(f20,plain,(
% 0.22/0.44    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.44    inference(flattening,[],[f19])).
% 0.22/0.44  fof(f19,plain,(
% 0.22/0.44    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.44    inference(ennf_transformation,[],[f9])).
% 0.22/0.44  fof(f9,axiom,(
% 0.22/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.44  fof(f74,plain,(
% 0.22/0.44    ~r1_tarski(sK2,k1_relat_1(sK3))),
% 0.22/0.44    inference(subsumption_resolution,[],[f73,f60])).
% 0.22/0.44  fof(f60,plain,(
% 0.22/0.44    v1_relat_1(sK3)),
% 0.22/0.44    inference(subsumption_resolution,[],[f59,f35])).
% 0.22/0.44  fof(f35,plain,(
% 0.22/0.44    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f4])).
% 0.22/0.44  fof(f4,axiom,(
% 0.22/0.44    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.44  fof(f59,plain,(
% 0.22/0.44    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.22/0.44    inference(resolution,[],[f34,f29])).
% 0.22/0.44  fof(f34,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f15])).
% 0.22/0.44  fof(f15,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f3])).
% 0.22/0.44  fof(f3,axiom,(
% 0.22/0.44    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.44  fof(f73,plain,(
% 0.22/0.44    ~r1_tarski(sK2,k1_relat_1(sK3)) | ~v1_relat_1(sK3)),
% 0.22/0.44    inference(resolution,[],[f70,f36])).
% 0.22/0.44  fof(f36,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f17])).
% 0.22/0.44  fof(f17,plain,(
% 0.22/0.44    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.22/0.44    inference(flattening,[],[f16])).
% 0.22/0.44  fof(f16,plain,(
% 0.22/0.44    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f5])).
% 0.22/0.44  fof(f5,axiom,(
% 0.22/0.44    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 0.22/0.44  fof(f70,plain,(
% 0.22/0.44    ~r1_tarski(sK2,k10_relat_1(sK3,k9_relat_1(sK3,sK2)))),
% 0.22/0.44    inference(subsumption_resolution,[],[f69,f29])).
% 0.22/0.44  fof(f69,plain,(
% 0.22/0.44    ~r1_tarski(sK2,k10_relat_1(sK3,k9_relat_1(sK3,sK2))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.44    inference(superposition,[],[f66,f46])).
% 0.22/0.44  fof(f46,plain,(
% 0.22/0.44    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f24])).
% 0.22/0.44  fof(f24,plain,(
% 0.22/0.44    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.44    inference(ennf_transformation,[],[f8])).
% 0.22/0.44  fof(f8,axiom,(
% 0.22/0.44    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.22/0.44  fof(f66,plain,(
% 0.22/0.44    ~r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k9_relat_1(sK3,sK2)))),
% 0.22/0.44    inference(subsumption_resolution,[],[f65,f29])).
% 0.22/0.44  fof(f65,plain,(
% 0.22/0.44    ~r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k9_relat_1(sK3,sK2))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.44    inference(superposition,[],[f32,f45])).
% 0.22/0.44  fof(f45,plain,(
% 0.22/0.44    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f23])).
% 0.22/0.44  fof(f23,plain,(
% 0.22/0.44    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.44    inference(ennf_transformation,[],[f7])).
% 0.22/0.44  fof(f7,axiom,(
% 0.22/0.44    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.22/0.44  fof(f32,plain,(
% 0.22/0.44    ~r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2)))),
% 0.22/0.44    inference(cnf_transformation,[],[f26])).
% 0.22/0.44  fof(f87,plain,(
% 0.22/0.44    spl4_1),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f86])).
% 0.22/0.44  fof(f86,plain,(
% 0.22/0.44    $false | spl4_1),
% 0.22/0.44    inference(subsumption_resolution,[],[f85,f30])).
% 0.22/0.44  fof(f85,plain,(
% 0.22/0.44    ~r1_tarski(sK2,sK0) | spl4_1),
% 0.22/0.44    inference(backward_demodulation,[],[f74,f84])).
% 0.22/0.44  fof(f84,plain,(
% 0.22/0.44    sK0 = k1_relat_1(sK3) | spl4_1),
% 0.22/0.44    inference(subsumption_resolution,[],[f80,f29])).
% 0.22/0.44  fof(f80,plain,(
% 0.22/0.44    sK0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl4_1),
% 0.22/0.44    inference(superposition,[],[f77,f37])).
% 0.22/0.44  fof(f77,plain,(
% 0.22/0.44    sK0 = k1_relset_1(sK0,sK1,sK3) | spl4_1),
% 0.22/0.44    inference(subsumption_resolution,[],[f76,f54])).
% 0.22/0.44  fof(f54,plain,(
% 0.22/0.44    k1_xboole_0 != sK1 | spl4_1),
% 0.22/0.44    inference(avatar_component_clause,[],[f53])).
% 0.22/0.44  fof(f76,plain,(
% 0.22/0.44    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.22/0.44    inference(subsumption_resolution,[],[f75,f28])).
% 0.22/0.44  fof(f75,plain,(
% 0.22/0.44    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.22/0.44    inference(resolution,[],[f38,f29])).
% 0.22/0.44  fof(f38,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.22/0.44    inference(cnf_transformation,[],[f27])).
% 0.22/0.44  fof(f58,plain,(
% 0.22/0.44    ~spl4_1 | spl4_2),
% 0.22/0.44    inference(avatar_split_clause,[],[f31,f56,f53])).
% 0.22/0.44  fof(f31,plain,(
% 0.22/0.44    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 0.22/0.44    inference(cnf_transformation,[],[f26])).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (16190)------------------------------
% 0.22/0.44  % (16190)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (16190)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (16190)Memory used [KB]: 10618
% 0.22/0.44  % (16190)Time elapsed: 0.041 s
% 0.22/0.44  % (16190)------------------------------
% 0.22/0.44  % (16190)------------------------------
% 0.22/0.44  % (16187)Success in time 0.082 s
%------------------------------------------------------------------------------
