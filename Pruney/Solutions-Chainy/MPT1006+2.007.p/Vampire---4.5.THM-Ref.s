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
% DateTime   : Thu Dec  3 13:03:43 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 174 expanded)
%              Number of leaves         :   17 (  44 expanded)
%              Depth                    :   18
%              Number of atoms          :  246 ( 537 expanded)
%              Number of equality atoms :   59 ( 213 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f347,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f88,f109,f138,f161,f346])).

fof(f346,plain,
    ( ~ spl3_4
    | ~ spl3_8 ),
    inference(avatar_contradiction_clause,[],[f345])).

fof(f345,plain,
    ( $false
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f338,f87])).

fof(f87,plain,
    ( v1_xboole_0(sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl3_4
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f338,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl3_8 ),
    inference(duplicate_literal_removal,[],[f337])).

fof(f337,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ v1_xboole_0(sK2)
    | ~ spl3_8 ),
    inference(resolution,[],[f213,f163])).

fof(f163,plain,
    ( ! [X0,X1] :
        ( v1_funct_2(X0,X0,X1)
        | ~ v1_xboole_0(X0) )
    | ~ spl3_8 ),
    inference(superposition,[],[f108,f39])).

fof(f39,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f108,plain,
    ( ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl3_8
  <=> ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f213,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK2,X0,sK1)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f210,f39])).

fof(f210,plain,(
    ~ v1_funct_2(sK2,k1_xboole_0,sK1) ),
    inference(subsumption_resolution,[],[f209,f30])).

fof(f30,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    & v1_funct_2(sK2,k1_xboole_0,sK0)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_2(X2,k1_xboole_0,X0)
        & v1_funct_1(X2) )
   => ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
      & v1_funct_2(sK2,k1_xboole_0,sK0)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      & v1_funct_2(X2,k1_xboole_0,X0)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      & v1_funct_2(X2,k1_xboole_0,X0)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_2(X2,k1_xboole_0,X0)
          & v1_funct_1(X2) )
       => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_2(X2,k1_xboole_0,X0)
        & v1_funct_1(X2) )
     => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_funct_2)).

fof(f209,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f198,f54])).

fof(f54,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f32,f52])).

fof(f52,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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

fof(f32,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f198,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(sK2,k1_xboole_0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(trivial_inequality_removal,[],[f197])).

fof(f197,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(sK2,k1_xboole_0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f117,f122])).

fof(f122,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = k10_relat_1(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_funct_2(X3,k1_xboole_0,X2)
      | ~ v1_funct_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f121])).

fof(f121,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = k10_relat_1(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_funct_2(X3,k1_xboole_0,X2)
      | ~ v1_funct_1(X3) ) ),
    inference(forward_demodulation,[],[f119,f52])).

fof(f119,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = k10_relat_1(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_funct_2(X3,k1_xboole_0,X2)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) ) ),
    inference(superposition,[],[f55,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f55,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k8_relset_1(k1_xboole_0,X1,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f53,f52])).

fof(f53,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k8_relset_1(k1_xboole_0,X1,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_2)).

fof(f117,plain,(
    k1_xboole_0 != k10_relat_1(sK2,sK1) ),
    inference(subsumption_resolution,[],[f116,f54])).

fof(f116,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 != k10_relat_1(sK2,sK1) ),
    inference(forward_demodulation,[],[f115,f52])).

fof(f115,plain,
    ( k1_xboole_0 != k10_relat_1(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(superposition,[],[f33,f50])).

fof(f33,plain,(
    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f161,plain,
    ( ~ spl3_4
    | spl3_7 ),
    inference(avatar_contradiction_clause,[],[f160])).

fof(f160,plain,
    ( $false
    | ~ spl3_4
    | spl3_7 ),
    inference(subsumption_resolution,[],[f159,f87])).

fof(f159,plain,
    ( ~ v1_xboole_0(sK2)
    | spl3_7 ),
    inference(resolution,[],[f129,f30])).

fof(f129,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_xboole_0(X0) )
    | spl3_7 ),
    inference(superposition,[],[f105,f39])).

fof(f105,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl3_7
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f138,plain,(
    ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f137])).

fof(f137,plain,
    ( $false
    | ~ spl3_3 ),
    inference(resolution,[],[f134,f34])).

fof(f34,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f134,plain,
    ( ! [X0] : ~ v1_xboole_0(X0)
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f131,f34])).

fof(f131,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k1_xboole_0)
        | ~ v1_xboole_0(X0) )
    | ~ spl3_3 ),
    inference(superposition,[],[f84,f51])).

fof(f51,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f84,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(k2_zfmisc_1(X0,X1))
        | ~ v1_xboole_0(X0) )
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl3_3
  <=> ! [X1,X0] :
        ( ~ v1_xboole_0(X0)
        | ~ v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f109,plain,
    ( ~ spl3_7
    | spl3_8 ),
    inference(avatar_split_clause,[],[f102,f107,f104])).

fof(f102,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
      | ~ v1_funct_1(k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f101,f37])).

fof(f37,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f101,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,X0)
      | v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
      | ~ v1_funct_1(k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f100,f36])).

fof(f36,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f100,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
      | ~ r1_tarski(k2_relat_1(k1_xboole_0),X0)
      | ~ v1_funct_1(k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f99,f68])).

fof(f68,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f47,f38])).

fof(f38,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f99,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
      | ~ r1_tarski(k2_relat_1(k1_xboole_0),X0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f42,f35])).

fof(f35,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f88,plain,
    ( spl3_3
    | spl3_4 ),
    inference(avatar_split_clause,[],[f78,f86,f83])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(sK2)
      | ~ v1_xboole_0(X0)
      | ~ v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    inference(resolution,[],[f40,f64])).

fof(f64,plain,(
    ! [X0] :
      ( m1_subset_1(sK2,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f54,f39])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X2)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:16:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (17820)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.47  % (17812)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.48  % (17809)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.48  % (17801)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.48  % (17801)Refutation not found, incomplete strategy% (17801)------------------------------
% 0.20/0.48  % (17801)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (17801)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (17801)Memory used [KB]: 6140
% 0.20/0.48  % (17801)Time elapsed: 0.063 s
% 0.20/0.48  % (17801)------------------------------
% 0.20/0.48  % (17801)------------------------------
% 0.20/0.48  % (17802)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (17802)Refutation not found, incomplete strategy% (17802)------------------------------
% 0.20/0.49  % (17802)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (17802)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (17802)Memory used [KB]: 10618
% 0.20/0.49  % (17802)Time elapsed: 0.062 s
% 0.20/0.49  % (17802)------------------------------
% 0.20/0.49  % (17802)------------------------------
% 0.20/0.49  % (17811)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.49  % (17814)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.49  % (17814)Refutation not found, incomplete strategy% (17814)------------------------------
% 0.20/0.49  % (17814)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (17814)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (17814)Memory used [KB]: 1663
% 0.20/0.49  % (17814)Time elapsed: 0.005 s
% 0.20/0.49  % (17814)------------------------------
% 0.20/0.49  % (17814)------------------------------
% 0.20/0.49  % (17806)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.49  % (17803)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.50  % (17805)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.50  % (17808)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.50  % (17821)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.50  % (17807)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.50  % (17821)Refutation not found, incomplete strategy% (17821)------------------------------
% 0.20/0.50  % (17821)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (17821)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (17821)Memory used [KB]: 10490
% 0.20/0.50  % (17821)Time elapsed: 0.082 s
% 0.20/0.50  % (17821)------------------------------
% 0.20/0.50  % (17821)------------------------------
% 0.20/0.50  % (17810)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.50  % (17815)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.51  % (17819)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.51  % (17804)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (17816)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.51  % (17811)Refutation not found, incomplete strategy% (17811)------------------------------
% 0.20/0.51  % (17811)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (17811)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (17811)Memory used [KB]: 6140
% 0.20/0.51  % (17811)Time elapsed: 0.080 s
% 0.20/0.51  % (17811)------------------------------
% 0.20/0.51  % (17811)------------------------------
% 0.20/0.51  % (17804)Refutation not found, incomplete strategy% (17804)------------------------------
% 0.20/0.51  % (17804)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (17804)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (17804)Memory used [KB]: 10618
% 0.20/0.51  % (17804)Time elapsed: 0.096 s
% 0.20/0.51  % (17804)------------------------------
% 0.20/0.51  % (17804)------------------------------
% 0.20/0.51  % (17803)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f347,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f88,f109,f138,f161,f346])).
% 0.20/0.51  fof(f346,plain,(
% 0.20/0.51    ~spl3_4 | ~spl3_8),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f345])).
% 0.20/0.51  fof(f345,plain,(
% 0.20/0.51    $false | (~spl3_4 | ~spl3_8)),
% 0.20/0.51    inference(subsumption_resolution,[],[f338,f87])).
% 0.20/0.51  fof(f87,plain,(
% 0.20/0.51    v1_xboole_0(sK2) | ~spl3_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f86])).
% 0.20/0.51  fof(f86,plain,(
% 0.20/0.51    spl3_4 <=> v1_xboole_0(sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.51  fof(f338,plain,(
% 0.20/0.51    ~v1_xboole_0(sK2) | ~spl3_8),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f337])).
% 0.20/0.51  fof(f337,plain,(
% 0.20/0.51    ~v1_xboole_0(sK2) | ~v1_xboole_0(sK2) | ~spl3_8),
% 0.20/0.51    inference(resolution,[],[f213,f163])).
% 0.20/0.51  fof(f163,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v1_funct_2(X0,X0,X1) | ~v1_xboole_0(X0)) ) | ~spl3_8),
% 0.20/0.51    inference(superposition,[],[f108,f39])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.51  fof(f108,plain,(
% 0.20/0.51    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) ) | ~spl3_8),
% 0.20/0.51    inference(avatar_component_clause,[],[f107])).
% 0.20/0.51  fof(f107,plain,(
% 0.20/0.51    spl3_8 <=> ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.51  fof(f213,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_funct_2(sK2,X0,sK1) | ~v1_xboole_0(X0)) )),
% 0.20/0.51    inference(superposition,[],[f210,f39])).
% 0.20/0.51  fof(f210,plain,(
% 0.20/0.51    ~v1_funct_2(sK2,k1_xboole_0,sK1)),
% 0.20/0.51    inference(subsumption_resolution,[],[f209,f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    v1_funct_1(sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) & v1_funct_2(sK2,k1_xboole_0,sK0) & v1_funct_1(sK2)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => (k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) & v1_funct_2(sK2,k1_xboole_0,sK0) & v1_funct_1(sK2))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2))),
% 0.20/0.51    inference(flattening,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)))),
% 0.20/0.51    inference(ennf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.20/0.51    inference(negated_conjecture,[],[f13])).
% 0.20/0.51  fof(f13,conjecture,(
% 0.20/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_funct_2)).
% 0.20/0.51  fof(f209,plain,(
% 0.20/0.51    ~v1_funct_2(sK2,k1_xboole_0,sK1) | ~v1_funct_1(sK2)),
% 0.20/0.51    inference(subsumption_resolution,[],[f198,f54])).
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.51    inference(backward_demodulation,[],[f32,f52])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.51    inference(equality_resolution,[],[f45])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.51    inference(flattening,[],[f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.51    inference(nnf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.20/0.51    inference(cnf_transformation,[],[f27])).
% 0.20/0.51  fof(f198,plain,(
% 0.20/0.51    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(sK2,k1_xboole_0,sK1) | ~v1_funct_1(sK2)),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f197])).
% 0.20/0.51  fof(f197,plain,(
% 0.20/0.51    k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(sK2,k1_xboole_0,sK1) | ~v1_funct_1(sK2)),
% 0.20/0.51    inference(superposition,[],[f117,f122])).
% 0.20/0.51  fof(f122,plain,(
% 0.20/0.51    ( ! [X2,X3] : (k1_xboole_0 = k10_relat_1(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(X3,k1_xboole_0,X2) | ~v1_funct_1(X3)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f121])).
% 0.20/0.51  fof(f121,plain,(
% 0.20/0.51    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k10_relat_1(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(X3,k1_xboole_0,X2) | ~v1_funct_1(X3)) )),
% 0.20/0.51    inference(forward_demodulation,[],[f119,f52])).
% 0.20/0.51  fof(f119,plain,(
% 0.20/0.51    ( ! [X2,X3] : (k1_xboole_0 = k10_relat_1(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(X3,k1_xboole_0,X2) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))) )),
% 0.20/0.51    inference(superposition,[],[f55,f50])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(ennf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    ( ! [X2,X1] : (k1_xboole_0 = k8_relset_1(k1_xboole_0,X1,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.51    inference(forward_demodulation,[],[f53,f52])).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    ( ! [X2,X1] : (k1_xboole_0 = k8_relset_1(k1_xboole_0,X1,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.51    inference(equality_resolution,[],[f49])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,X1) = X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.51    inference(flattening,[],[f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.51    inference(ennf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,X1) = X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_2)).
% 0.20/0.51  fof(f117,plain,(
% 0.20/0.51    k1_xboole_0 != k10_relat_1(sK2,sK1)),
% 0.20/0.51    inference(subsumption_resolution,[],[f116,f54])).
% 0.20/0.51  fof(f116,plain,(
% 0.20/0.51    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k10_relat_1(sK2,sK1)),
% 0.20/0.51    inference(forward_demodulation,[],[f115,f52])).
% 0.20/0.51  fof(f115,plain,(
% 0.20/0.51    k1_xboole_0 != k10_relat_1(sK2,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.20/0.51    inference(superposition,[],[f33,f50])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f27])).
% 0.20/0.51  fof(f161,plain,(
% 0.20/0.51    ~spl3_4 | spl3_7),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f160])).
% 0.20/0.51  fof(f160,plain,(
% 0.20/0.51    $false | (~spl3_4 | spl3_7)),
% 0.20/0.51    inference(subsumption_resolution,[],[f159,f87])).
% 0.20/0.51  fof(f159,plain,(
% 0.20/0.51    ~v1_xboole_0(sK2) | spl3_7),
% 0.20/0.51    inference(resolution,[],[f129,f30])).
% 0.20/0.51  fof(f129,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_funct_1(X0) | ~v1_xboole_0(X0)) ) | spl3_7),
% 0.20/0.51    inference(superposition,[],[f105,f39])).
% 0.20/0.51  fof(f105,plain,(
% 0.20/0.51    ~v1_funct_1(k1_xboole_0) | spl3_7),
% 0.20/0.51    inference(avatar_component_clause,[],[f104])).
% 0.20/0.51  fof(f104,plain,(
% 0.20/0.51    spl3_7 <=> v1_funct_1(k1_xboole_0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.51  fof(f138,plain,(
% 0.20/0.51    ~spl3_3),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f137])).
% 0.20/0.51  fof(f137,plain,(
% 0.20/0.51    $false | ~spl3_3),
% 0.20/0.51    inference(resolution,[],[f134,f34])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    v1_xboole_0(k1_xboole_0)),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    v1_xboole_0(k1_xboole_0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.51  fof(f134,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_xboole_0(X0)) ) | ~spl3_3),
% 0.20/0.51    inference(subsumption_resolution,[],[f131,f34])).
% 0.20/0.51  fof(f131,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(X0)) ) | ~spl3_3),
% 0.20/0.51    inference(superposition,[],[f84,f51])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.51    inference(equality_resolution,[],[f46])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f29])).
% 0.20/0.51  fof(f84,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0)) ) | ~spl3_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f83])).
% 0.20/0.51  fof(f83,plain,(
% 0.20/0.51    spl3_3 <=> ! [X1,X0] : (~v1_xboole_0(X0) | ~v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.51  fof(f109,plain,(
% 0.20/0.51    ~spl3_7 | spl3_8),
% 0.20/0.51    inference(avatar_split_clause,[],[f102,f107,f104])).
% 0.20/0.51  fof(f102,plain,(
% 0.20/0.51    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | ~v1_funct_1(k1_xboole_0)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f101,f37])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.51  fof(f101,plain,(
% 0.20/0.51    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | ~v1_funct_1(k1_xboole_0)) )),
% 0.20/0.51    inference(forward_demodulation,[],[f100,f36])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.51    inference(cnf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.51  fof(f100,plain,(
% 0.20/0.51    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | ~r1_tarski(k2_relat_1(k1_xboole_0),X0) | ~v1_funct_1(k1_xboole_0)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f99,f68])).
% 0.20/0.51  fof(f68,plain,(
% 0.20/0.51    v1_relat_1(k1_xboole_0)),
% 0.20/0.51    inference(resolution,[],[f47,f38])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.51  fof(f99,plain,(
% 0.20/0.51    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | ~r1_tarski(k2_relat_1(k1_xboole_0),X0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.20/0.51    inference(superposition,[],[f42,f35])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.51    inference(cnf_transformation,[],[f7])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(flattening,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.51    inference(ennf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,axiom,(
% 0.20/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 0.20/0.51  fof(f88,plain,(
% 0.20/0.51    spl3_3 | spl3_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f78,f86,f83])).
% 0.20/0.51  fof(f78,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v1_xboole_0(sK2) | ~v1_xboole_0(X0) | ~v1_xboole_0(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.51    inference(resolution,[],[f40,f64])).
% 0.20/0.51  fof(f64,plain,(
% 0.20/0.51    ( ! [X0] : (m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.20/0.51    inference(superposition,[],[f54,f39])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X2) | ~v1_xboole_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,axiom,(
% 0.20/0.51    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (17803)------------------------------
% 0.20/0.51  % (17803)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (17803)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (17803)Memory used [KB]: 10746
% 0.20/0.51  % (17803)Time elapsed: 0.101 s
% 0.20/0.51  % (17803)------------------------------
% 0.20/0.51  % (17803)------------------------------
% 0.20/0.51  % (17800)Success in time 0.153 s
% 0.20/0.51  % (17817)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
%------------------------------------------------------------------------------
