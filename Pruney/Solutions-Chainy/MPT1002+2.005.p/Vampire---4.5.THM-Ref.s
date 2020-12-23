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
% DateTime   : Thu Dec  3 13:03:37 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 245 expanded)
%              Number of leaves         :   19 (  67 expanded)
%              Depth                    :   15
%              Number of atoms          :  262 (1144 expanded)
%              Number of equality atoms :   58 ( 306 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f185,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f86,f109,f126,f144,f171,f184])).

fof(f184,plain,
    ( ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f183])).

fof(f183,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f182,f43])).

fof(f43,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f182,plain,
    ( ~ r1_tarski(k1_xboole_0,k10_relat_1(sK3,k9_relat_1(sK3,k1_xboole_0)))
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f136,f172])).

fof(f172,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f85,f75])).

fof(f75,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f85,plain,
    ( sK0 = sK2
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl4_4
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f136,plain,(
    ~ r1_tarski(sK2,k10_relat_1(sK3,k9_relat_1(sK3,sK2))) ),
    inference(backward_demodulation,[],[f120,f88])).

fof(f88,plain,(
    ! [X1] : k7_relset_1(sK0,sK1,sK3,X1) = k9_relat_1(sK3,X1) ),
    inference(resolution,[],[f39,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f39,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ~ r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2)))
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f29])).

fof(f29,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2)))
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(sK2,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X2,X0)
         => ( r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_funct_2)).

fof(f120,plain,(
    ~ r1_tarski(sK2,k10_relat_1(sK3,k7_relset_1(sK0,sK1,sK3,sK2))) ),
    inference(backward_demodulation,[],[f42,f87])).

fof(f87,plain,(
    ! [X0] : k8_relset_1(sK0,sK1,sK3,X0) = k10_relat_1(sK3,X0) ),
    inference(resolution,[],[f39,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f42,plain,(
    ~ r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2))) ),
    inference(cnf_transformation,[],[f30])).

fof(f171,plain,
    ( ~ spl4_2
    | spl4_3 ),
    inference(avatar_contradiction_clause,[],[f170])).

fof(f170,plain,
    ( $false
    | ~ spl4_2
    | spl4_3 ),
    inference(subsumption_resolution,[],[f168,f43])).

fof(f168,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | ~ spl4_2
    | spl4_3 ),
    inference(backward_demodulation,[],[f81,f75])).

fof(f81,plain,
    ( ~ r1_tarski(sK0,sK2)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl4_3
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f144,plain,(
    ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f143])).

fof(f143,plain,
    ( $false
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f142,f40])).

fof(f40,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f142,plain,
    ( ~ r1_tarski(sK2,sK0)
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f141,f108])).

fof(f108,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl4_6
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f141,plain,(
    ~ r1_tarski(sK2,k1_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f140,f96])).

fof(f96,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f92,f45])).

fof(f45,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f92,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f39,f44])).

fof(f44,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f140,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f136,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(f126,plain,
    ( spl4_1
    | spl4_5 ),
    inference(avatar_contradiction_clause,[],[f125])).

fof(f125,plain,
    ( $false
    | spl4_1
    | spl4_5 ),
    inference(subsumption_resolution,[],[f124,f96])).

fof(f124,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_1
    | spl4_5 ),
    inference(subsumption_resolution,[],[f123,f104])).

fof(f104,plain,
    ( ~ r1_tarski(sK0,k1_relat_1(sK3))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl4_5
  <=> r1_tarski(sK0,k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f123,plain,
    ( r1_tarski(sK0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | spl4_1 ),
    inference(superposition,[],[f46,f121])).

fof(f121,plain,
    ( sK0 = k10_relat_1(sK3,sK1)
    | spl4_1 ),
    inference(superposition,[],[f87,f95])).

fof(f95,plain,
    ( sK0 = k8_relset_1(sK0,sK1,sK3,sK1)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f94,f37])).

fof(f37,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f94,plain,
    ( sK0 = k8_relset_1(sK0,sK1,sK3,sK1)
    | ~ v1_funct_1(sK3)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f93,f38])).

fof(f38,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f93,plain,
    ( sK0 = k8_relset_1(sK0,sK1,sK3,sK1)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ v1_funct_1(sK3)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f89,f71])).

fof(f71,plain,
    ( k1_xboole_0 != sK1
    | spl4_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl4_1
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f89,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k8_relset_1(sK0,sK1,sK3,sK1)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f39,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k8_relset_1(X0,X1,X2,X1) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_2)).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(f109,plain,
    ( ~ spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f100,f106,f102])).

fof(f100,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ r1_tarski(sK0,k1_relat_1(sK3)) ),
    inference(resolution,[],[f98,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f98,plain,(
    r1_tarski(k1_relat_1(sK3),sK0) ),
    inference(subsumption_resolution,[],[f97,f96])).

fof(f97,plain,
    ( r1_tarski(k1_relat_1(sK3),sK0)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f90,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f90,plain,(
    v4_relat_1(sK3,sK0) ),
    inference(resolution,[],[f39,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f86,plain,
    ( ~ spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f77,f83,f79])).

fof(f77,plain,
    ( sK0 = sK2
    | ~ r1_tarski(sK0,sK2) ),
    inference(resolution,[],[f40,f52])).

fof(f76,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f41,f73,f69])).

fof(f41,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:30:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (8642)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.48  % (8659)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.51  % (8647)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.51  % (8657)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.51  % (8639)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (8649)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (8656)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.52  % (8641)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.52  % (8654)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.52  % (8640)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.52  % (8643)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.52  % (8648)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (8653)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.52  % (8636)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (8641)Refutation not found, incomplete strategy% (8641)------------------------------
% 0.22/0.52  % (8641)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (8641)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (8641)Memory used [KB]: 10618
% 0.22/0.52  % (8641)Time elapsed: 0.067 s
% 0.22/0.52  % (8641)------------------------------
% 0.22/0.52  % (8641)------------------------------
% 0.22/0.52  % (8637)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.52  % (8636)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f185,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f76,f86,f109,f126,f144,f171,f184])).
% 0.22/0.52  fof(f184,plain,(
% 0.22/0.52    ~spl4_2 | ~spl4_4),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f183])).
% 0.22/0.52  fof(f183,plain,(
% 0.22/0.52    $false | (~spl4_2 | ~spl4_4)),
% 0.22/0.52    inference(subsumption_resolution,[],[f182,f43])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.52  fof(f182,plain,(
% 0.22/0.52    ~r1_tarski(k1_xboole_0,k10_relat_1(sK3,k9_relat_1(sK3,k1_xboole_0))) | (~spl4_2 | ~spl4_4)),
% 0.22/0.52    inference(backward_demodulation,[],[f136,f172])).
% 0.22/0.52  fof(f172,plain,(
% 0.22/0.52    k1_xboole_0 = sK2 | (~spl4_2 | ~spl4_4)),
% 0.22/0.52    inference(forward_demodulation,[],[f85,f75])).
% 0.22/0.52  fof(f75,plain,(
% 0.22/0.52    k1_xboole_0 = sK0 | ~spl4_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f73])).
% 0.22/0.52  fof(f73,plain,(
% 0.22/0.52    spl4_2 <=> k1_xboole_0 = sK0),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.52  fof(f85,plain,(
% 0.22/0.52    sK0 = sK2 | ~spl4_4),
% 0.22/0.52    inference(avatar_component_clause,[],[f83])).
% 0.22/0.52  fof(f83,plain,(
% 0.22/0.52    spl4_4 <=> sK0 = sK2),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.52  fof(f136,plain,(
% 0.22/0.52    ~r1_tarski(sK2,k10_relat_1(sK3,k9_relat_1(sK3,sK2)))),
% 0.22/0.52    inference(backward_demodulation,[],[f120,f88])).
% 0.22/0.52  fof(f88,plain,(
% 0.22/0.52    ( ! [X1] : (k7_relset_1(sK0,sK1,sK3,X1) = k9_relat_1(sK3,X1)) )),
% 0.22/0.52    inference(resolution,[],[f39,f61])).
% 0.22/0.52  fof(f61,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.52    inference(cnf_transformation,[],[f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ~r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ? [X0,X1,X2,X3] : (~r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ? [X0,X1,X2,X3] : (~r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.22/0.52    inference(flattening,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ? [X0,X1,X2,X3] : (((~r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.22/0.52    inference(ennf_transformation,[],[f15])).
% 0.22/0.52  fof(f15,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => (r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.22/0.52    inference(negated_conjecture,[],[f14])).
% 0.22/0.52  fof(f14,conjecture,(
% 0.22/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => (r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_funct_2)).
% 0.22/0.52  fof(f120,plain,(
% 0.22/0.52    ~r1_tarski(sK2,k10_relat_1(sK3,k7_relset_1(sK0,sK1,sK3,sK2)))),
% 0.22/0.52    inference(backward_demodulation,[],[f42,f87])).
% 0.22/0.52  fof(f87,plain,(
% 0.22/0.52    ( ! [X0] : (k8_relset_1(sK0,sK1,sK3,X0) = k10_relat_1(sK3,X0)) )),
% 0.22/0.52    inference(resolution,[],[f39,f62])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ~r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2)))),
% 0.22/0.52    inference(cnf_transformation,[],[f30])).
% 0.22/0.52  fof(f171,plain,(
% 0.22/0.52    ~spl4_2 | spl4_3),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f170])).
% 0.22/0.53  fof(f170,plain,(
% 0.22/0.53    $false | (~spl4_2 | spl4_3)),
% 0.22/0.53    inference(subsumption_resolution,[],[f168,f43])).
% 0.22/0.53  fof(f168,plain,(
% 0.22/0.53    ~r1_tarski(k1_xboole_0,sK2) | (~spl4_2 | spl4_3)),
% 0.22/0.53    inference(backward_demodulation,[],[f81,f75])).
% 0.22/0.53  fof(f81,plain,(
% 0.22/0.53    ~r1_tarski(sK0,sK2) | spl4_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f79])).
% 0.22/0.53  fof(f79,plain,(
% 0.22/0.53    spl4_3 <=> r1_tarski(sK0,sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.53  fof(f144,plain,(
% 0.22/0.53    ~spl4_6),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f143])).
% 0.22/0.53  fof(f143,plain,(
% 0.22/0.53    $false | ~spl4_6),
% 0.22/0.53    inference(subsumption_resolution,[],[f142,f40])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    r1_tarski(sK2,sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f30])).
% 0.22/0.53  fof(f142,plain,(
% 0.22/0.53    ~r1_tarski(sK2,sK0) | ~spl4_6),
% 0.22/0.53    inference(forward_demodulation,[],[f141,f108])).
% 0.22/0.53  fof(f108,plain,(
% 0.22/0.53    sK0 = k1_relat_1(sK3) | ~spl4_6),
% 0.22/0.53    inference(avatar_component_clause,[],[f106])).
% 0.22/0.53  fof(f106,plain,(
% 0.22/0.53    spl4_6 <=> sK0 = k1_relat_1(sK3)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.53  fof(f141,plain,(
% 0.22/0.53    ~r1_tarski(sK2,k1_relat_1(sK3))),
% 0.22/0.53    inference(subsumption_resolution,[],[f140,f96])).
% 0.22/0.53  fof(f96,plain,(
% 0.22/0.53    v1_relat_1(sK3)),
% 0.22/0.53    inference(subsumption_resolution,[],[f92,f45])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.53  fof(f92,plain,(
% 0.22/0.53    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.22/0.53    inference(resolution,[],[f39,f44])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.53  fof(f140,plain,(
% 0.22/0.53    ~r1_tarski(sK2,k1_relat_1(sK3)) | ~v1_relat_1(sK3)),
% 0.22/0.53    inference(resolution,[],[f136,f47])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(flattening,[],[f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,axiom,(
% 0.22/0.53    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
% 0.22/0.53  fof(f126,plain,(
% 0.22/0.53    spl4_1 | spl4_5),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f125])).
% 0.22/0.53  fof(f125,plain,(
% 0.22/0.53    $false | (spl4_1 | spl4_5)),
% 0.22/0.53    inference(subsumption_resolution,[],[f124,f96])).
% 0.22/0.53  fof(f124,plain,(
% 0.22/0.53    ~v1_relat_1(sK3) | (spl4_1 | spl4_5)),
% 0.22/0.53    inference(subsumption_resolution,[],[f123,f104])).
% 0.22/0.53  fof(f104,plain,(
% 0.22/0.53    ~r1_tarski(sK0,k1_relat_1(sK3)) | spl4_5),
% 0.22/0.53    inference(avatar_component_clause,[],[f102])).
% 0.22/0.53  fof(f102,plain,(
% 0.22/0.53    spl4_5 <=> r1_tarski(sK0,k1_relat_1(sK3))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.53  fof(f123,plain,(
% 0.22/0.53    r1_tarski(sK0,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | spl4_1),
% 0.22/0.53    inference(superposition,[],[f46,f121])).
% 0.22/0.53  fof(f121,plain,(
% 0.22/0.53    sK0 = k10_relat_1(sK3,sK1) | spl4_1),
% 0.22/0.53    inference(superposition,[],[f87,f95])).
% 0.22/0.53  fof(f95,plain,(
% 0.22/0.53    sK0 = k8_relset_1(sK0,sK1,sK3,sK1) | spl4_1),
% 0.22/0.53    inference(subsumption_resolution,[],[f94,f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    v1_funct_1(sK3)),
% 0.22/0.53    inference(cnf_transformation,[],[f30])).
% 0.22/0.53  fof(f94,plain,(
% 0.22/0.53    sK0 = k8_relset_1(sK0,sK1,sK3,sK1) | ~v1_funct_1(sK3) | spl4_1),
% 0.22/0.53    inference(subsumption_resolution,[],[f93,f38])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    v1_funct_2(sK3,sK0,sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f30])).
% 0.22/0.53  fof(f93,plain,(
% 0.22/0.53    sK0 = k8_relset_1(sK0,sK1,sK3,sK1) | ~v1_funct_2(sK3,sK0,sK1) | ~v1_funct_1(sK3) | spl4_1),
% 0.22/0.53    inference(subsumption_resolution,[],[f89,f71])).
% 0.22/0.53  fof(f71,plain,(
% 0.22/0.53    k1_xboole_0 != sK1 | spl4_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f69])).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    spl4_1 <=> k1_xboole_0 = sK1),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.53  fof(f89,plain,(
% 0.22/0.53    k1_xboole_0 = sK1 | sK0 = k8_relset_1(sK0,sK1,sK3,sK1) | ~v1_funct_2(sK3,sK0,sK1) | ~v1_funct_1(sK3)),
% 0.22/0.53    inference(resolution,[],[f39,f59])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k8_relset_1(X0,X1,X2,X1) = X0 | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.53    inference(flattening,[],[f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.53    inference(ennf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,X1) = X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_2)).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).
% 0.22/0.53  fof(f109,plain,(
% 0.22/0.53    ~spl4_5 | spl4_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f100,f106,f102])).
% 0.22/0.53  fof(f100,plain,(
% 0.22/0.53    sK0 = k1_relat_1(sK3) | ~r1_tarski(sK0,k1_relat_1(sK3))),
% 0.22/0.53    inference(resolution,[],[f98,f52])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.53    inference(flattening,[],[f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.53    inference(nnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.53  fof(f98,plain,(
% 0.22/0.53    r1_tarski(k1_relat_1(sK3),sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f97,f96])).
% 0.22/0.53  fof(f97,plain,(
% 0.22/0.53    r1_tarski(k1_relat_1(sK3),sK0) | ~v1_relat_1(sK3)),
% 0.22/0.53    inference(resolution,[],[f90,f48])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(nnf_transformation,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.22/0.53  fof(f90,plain,(
% 0.22/0.53    v4_relat_1(sK3,sK0)),
% 0.22/0.53    inference(resolution,[],[f39,f58])).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.22/0.53    inference(pure_predicate_removal,[],[f10])).
% 0.22/0.53  fof(f10,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.53  fof(f86,plain,(
% 0.22/0.53    ~spl4_3 | spl4_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f77,f83,f79])).
% 0.22/0.53  fof(f77,plain,(
% 0.22/0.53    sK0 = sK2 | ~r1_tarski(sK0,sK2)),
% 0.22/0.53    inference(resolution,[],[f40,f52])).
% 0.22/0.53  fof(f76,plain,(
% 0.22/0.53    ~spl4_1 | spl4_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f41,f73,f69])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 0.22/0.53    inference(cnf_transformation,[],[f30])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (8636)------------------------------
% 0.22/0.53  % (8636)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (8636)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (8636)Memory used [KB]: 10618
% 0.22/0.53  % (8636)Time elapsed: 0.101 s
% 0.22/0.53  % (8636)------------------------------
% 0.22/0.53  % (8636)------------------------------
% 0.22/0.53  % (8634)Success in time 0.163 s
%------------------------------------------------------------------------------
