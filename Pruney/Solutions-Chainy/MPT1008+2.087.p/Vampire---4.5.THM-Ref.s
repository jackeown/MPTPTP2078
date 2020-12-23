%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:04:21 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 182 expanded)
%              Number of leaves         :   11 (  45 expanded)
%              Depth                    :   17
%              Number of atoms          :  201 ( 756 expanded)
%              Number of equality atoms :   85 ( 303 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f140,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f139])).

fof(f139,plain,(
    ~ spl3_1 ),
    inference(avatar_contradiction_clause,[],[f138])).

fof(f138,plain,
    ( $false
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f137,f101])).

fof(f101,plain,
    ( k1_tarski(sK0) != k1_relat_1(sK2)
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f100,f50])).

fof(f50,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl3_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f100,plain,
    ( k1_tarski(sK0) != k1_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f99,f26])).

fof(f26,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_2(sK2,k1_tarski(sK0),sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2] :
        ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0))
      & k1_xboole_0 != sK1
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      & v1_funct_2(sK2,k1_tarski(sK0),sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0))
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

fof(f99,plain,
    ( k1_tarski(sK0) != k1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(trivial_inequality_removal,[],[f98])).

fof(f98,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | k1_tarski(sK0) != k1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f97,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_relat_1(X1) != k1_tarski(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_relat_1(X1) != k1_tarski(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))
      | k1_relat_1(X1) != k1_tarski(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_relat_1(X1) = k1_tarski(X0)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

fof(f97,plain,(
    k1_tarski(k1_funct_1(sK2,sK0)) != k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f96,f28])).

fof(f28,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f25])).

fof(f96,plain,
    ( k1_tarski(k1_funct_1(sK2,sK0)) != k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(superposition,[],[f30,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f30,plain,(
    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f137,plain,
    ( k1_tarski(sK0) = k1_relat_1(sK2)
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f136,f79])).

fof(f79,plain,
    ( k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2))
    | ~ spl3_1 ),
    inference(resolution,[],[f50,f38])).

fof(f38,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f136,plain,(
    k1_tarski(sK0) = k10_relat_1(sK2,k2_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f135,f110])).

fof(f110,plain,(
    k2_relat_1(sK2) = k9_relat_1(sK2,k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f109,f86])).

fof(f86,plain,(
    k2_relset_1(k1_tarski(sK0),sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f28,f34])).

fof(f109,plain,(
    k2_relset_1(k1_tarski(sK0),sK1,sK2) = k9_relat_1(sK2,k1_tarski(sK0)) ),
    inference(subsumption_resolution,[],[f108,f26])).

fof(f108,plain,
    ( k2_relset_1(k1_tarski(sK0),sK1,sK2) = k9_relat_1(sK2,k1_tarski(sK0))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f107,f27])).

fof(f27,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f107,plain,
    ( k2_relset_1(k1_tarski(sK0),sK1,sK2) = k9_relat_1(sK2,k1_tarski(sK0))
    | ~ v1_funct_2(sK2,k1_tarski(sK0),sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f106,f28])).

fof(f106,plain,
    ( k2_relset_1(k1_tarski(sK0),sK1,sK2) = k9_relat_1(sK2,k1_tarski(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    | ~ v1_funct_2(sK2,k1_tarski(sK0),sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f103,f29])).

fof(f29,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f25])).

fof(f103,plain,
    ( k2_relset_1(k1_tarski(sK0),sK1,sK2) = k9_relat_1(sK2,k1_tarski(sK0))
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    | ~ v1_funct_2(sK2,k1_tarski(sK0),sK1)
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f82,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_funct_2)).

fof(f82,plain,(
    ! [X0] : k7_relset_1(k1_tarski(sK0),sK1,sK2,X0) = k9_relat_1(sK2,X0) ),
    inference(resolution,[],[f28,f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f135,plain,(
    k1_tarski(sK0) = k10_relat_1(sK2,k9_relat_1(sK2,k1_tarski(sK0))) ),
    inference(forward_demodulation,[],[f134,f82])).

fof(f134,plain,(
    k1_tarski(sK0) = k10_relat_1(sK2,k7_relset_1(k1_tarski(sK0),sK1,sK2,k1_tarski(sK0))) ),
    inference(subsumption_resolution,[],[f133,f26])).

fof(f133,plain,
    ( k1_tarski(sK0) = k10_relat_1(sK2,k7_relset_1(k1_tarski(sK0),sK1,sK2,k1_tarski(sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f132,f27])).

fof(f132,plain,
    ( k1_tarski(sK0) = k10_relat_1(sK2,k7_relset_1(k1_tarski(sK0),sK1,sK2,k1_tarski(sK0)))
    | ~ v1_funct_2(sK2,k1_tarski(sK0),sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f131,f28])).

fof(f131,plain,
    ( k1_tarski(sK0) = k10_relat_1(sK2,k7_relset_1(k1_tarski(sK0),sK1,sK2,k1_tarski(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    | ~ v1_funct_2(sK2,k1_tarski(sK0),sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f121,f29])).

fof(f121,plain,
    ( k1_tarski(sK0) = k10_relat_1(sK2,k7_relset_1(k1_tarski(sK0),sK1,sK2,k1_tarski(sK0)))
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    | ~ v1_funct_2(sK2,k1_tarski(sK0),sK1)
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f36,f85])).

fof(f85,plain,(
    ! [X1] : k8_relset_1(k1_tarski(sK0),sK1,sK2,X1) = k10_relat_1(sK2,X1) ),
    inference(resolution,[],[f28,f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_funct_2)).

fof(f78,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f77])).

fof(f77,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f28,f56])).

fof(f56,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl3_1 ),
    inference(resolution,[],[f51,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f51,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f49])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:55:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.43  % (3522)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.43  % (3522)Refutation not found, incomplete strategy% (3522)------------------------------
% 0.22/0.43  % (3522)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (3522)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.43  
% 0.22/0.43  % (3522)Memory used [KB]: 10490
% 0.22/0.43  % (3522)Time elapsed: 0.003 s
% 0.22/0.43  % (3522)------------------------------
% 0.22/0.43  % (3522)------------------------------
% 0.22/0.47  % (3521)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.47  % (3521)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f140,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(avatar_sat_refutation,[],[f78,f139])).
% 0.22/0.47  fof(f139,plain,(
% 0.22/0.47    ~spl3_1),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f138])).
% 0.22/0.47  fof(f138,plain,(
% 0.22/0.47    $false | ~spl3_1),
% 0.22/0.47    inference(subsumption_resolution,[],[f137,f101])).
% 0.22/0.47  fof(f101,plain,(
% 0.22/0.47    k1_tarski(sK0) != k1_relat_1(sK2) | ~spl3_1),
% 0.22/0.47    inference(subsumption_resolution,[],[f100,f50])).
% 0.22/0.47  fof(f50,plain,(
% 0.22/0.47    v1_relat_1(sK2) | ~spl3_1),
% 0.22/0.47    inference(avatar_component_clause,[],[f49])).
% 0.22/0.47  fof(f49,plain,(
% 0.22/0.47    spl3_1 <=> v1_relat_1(sK2)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.48  fof(f100,plain,(
% 0.22/0.48    k1_tarski(sK0) != k1_relat_1(sK2) | ~v1_relat_1(sK2)),
% 0.22/0.48    inference(subsumption_resolution,[],[f99,f26])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    v1_funct_1(sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f25])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f24])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ? [X0,X1,X2] : (k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0)) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ? [X0,X1,X2] : (k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 0.22/0.48    inference(flattening,[],[f11])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ? [X0,X1,X2] : ((k2_relset_1(k1_tarski(X0),X1,X2) != k1_tarski(k1_funct_1(X2,X0)) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 0.22/0.48    inference(ennf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 0.22/0.48    inference(negated_conjecture,[],[f9])).
% 0.22/0.48  fof(f9,conjecture,(
% 0.22/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k2_relset_1(k1_tarski(X0),X1,X2) = k1_tarski(k1_funct_1(X2,X0))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).
% 0.22/0.48  fof(f99,plain,(
% 0.22/0.48    k1_tarski(sK0) != k1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.22/0.48    inference(trivial_inequality_removal,[],[f98])).
% 0.22/0.48  fof(f98,plain,(
% 0.22/0.48    k2_relat_1(sK2) != k2_relat_1(sK2) | k1_tarski(sK0) != k1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.22/0.48    inference(superposition,[],[f97,f31])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_relat_1(X1) != k1_tarski(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ! [X0,X1] : (k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_relat_1(X1) != k1_tarski(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(flattening,[],[f13])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ! [X0,X1] : ((k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) | k1_relat_1(X1) != k1_tarski(X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_relat_1(X1) = k1_tarski(X0) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).
% 0.22/0.48  fof(f97,plain,(
% 0.22/0.48    k1_tarski(k1_funct_1(sK2,sK0)) != k2_relat_1(sK2)),
% 0.22/0.48    inference(subsumption_resolution,[],[f96,f28])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.22/0.48    inference(cnf_transformation,[],[f25])).
% 0.22/0.48  fof(f96,plain,(
% 0.22/0.48    k1_tarski(k1_funct_1(sK2,sK0)) != k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.22/0.48    inference(superposition,[],[f30,f34])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    inference(ennf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    k2_relset_1(k1_tarski(sK0),sK1,sK2) != k1_tarski(k1_funct_1(sK2,sK0))),
% 0.22/0.48    inference(cnf_transformation,[],[f25])).
% 0.22/0.48  fof(f137,plain,(
% 0.22/0.48    k1_tarski(sK0) = k1_relat_1(sK2) | ~spl3_1),
% 0.22/0.48    inference(forward_demodulation,[],[f136,f79])).
% 0.22/0.48  fof(f79,plain,(
% 0.22/0.48    k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2)) | ~spl3_1),
% 0.22/0.48    inference(resolution,[],[f50,f38])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 0.22/0.48  fof(f136,plain,(
% 0.22/0.48    k1_tarski(sK0) = k10_relat_1(sK2,k2_relat_1(sK2))),
% 0.22/0.48    inference(forward_demodulation,[],[f135,f110])).
% 0.22/0.48  fof(f110,plain,(
% 0.22/0.48    k2_relat_1(sK2) = k9_relat_1(sK2,k1_tarski(sK0))),
% 0.22/0.48    inference(forward_demodulation,[],[f109,f86])).
% 0.22/0.48  fof(f86,plain,(
% 0.22/0.48    k2_relset_1(k1_tarski(sK0),sK1,sK2) = k2_relat_1(sK2)),
% 0.22/0.48    inference(resolution,[],[f28,f34])).
% 0.22/0.48  fof(f109,plain,(
% 0.22/0.48    k2_relset_1(k1_tarski(sK0),sK1,sK2) = k9_relat_1(sK2,k1_tarski(sK0))),
% 0.22/0.48    inference(subsumption_resolution,[],[f108,f26])).
% 0.22/0.48  fof(f108,plain,(
% 0.22/0.48    k2_relset_1(k1_tarski(sK0),sK1,sK2) = k9_relat_1(sK2,k1_tarski(sK0)) | ~v1_funct_1(sK2)),
% 0.22/0.48    inference(subsumption_resolution,[],[f107,f27])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f25])).
% 0.22/0.48  fof(f107,plain,(
% 0.22/0.48    k2_relset_1(k1_tarski(sK0),sK1,sK2) = k9_relat_1(sK2,k1_tarski(sK0)) | ~v1_funct_2(sK2,k1_tarski(sK0),sK1) | ~v1_funct_1(sK2)),
% 0.22/0.48    inference(subsumption_resolution,[],[f106,f28])).
% 0.22/0.48  fof(f106,plain,(
% 0.22/0.48    k2_relset_1(k1_tarski(sK0),sK1,sK2) = k9_relat_1(sK2,k1_tarski(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) | ~v1_funct_2(sK2,k1_tarski(sK0),sK1) | ~v1_funct_1(sK2)),
% 0.22/0.48    inference(subsumption_resolution,[],[f103,f29])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    k1_xboole_0 != sK1),
% 0.22/0.48    inference(cnf_transformation,[],[f25])).
% 0.22/0.48  fof(f103,plain,(
% 0.22/0.48    k2_relset_1(k1_tarski(sK0),sK1,sK2) = k9_relat_1(sK2,k1_tarski(sK0)) | k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) | ~v1_funct_2(sK2,k1_tarski(sK0),sK1) | ~v1_funct_1(sK2)),
% 0.22/0.48    inference(superposition,[],[f82,f32])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.48    inference(flattening,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.48    inference(ennf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_funct_2)).
% 0.22/0.48  fof(f82,plain,(
% 0.22/0.48    ( ! [X0] : (k7_relset_1(k1_tarski(sK0),sK1,sK2,X0) = k9_relat_1(sK2,X0)) )),
% 0.22/0.48    inference(resolution,[],[f28,f40])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.22/0.48  fof(f135,plain,(
% 0.22/0.48    k1_tarski(sK0) = k10_relat_1(sK2,k9_relat_1(sK2,k1_tarski(sK0)))),
% 0.22/0.48    inference(forward_demodulation,[],[f134,f82])).
% 0.22/0.48  fof(f134,plain,(
% 0.22/0.48    k1_tarski(sK0) = k10_relat_1(sK2,k7_relset_1(k1_tarski(sK0),sK1,sK2,k1_tarski(sK0)))),
% 0.22/0.48    inference(subsumption_resolution,[],[f133,f26])).
% 0.22/0.48  fof(f133,plain,(
% 0.22/0.48    k1_tarski(sK0) = k10_relat_1(sK2,k7_relset_1(k1_tarski(sK0),sK1,sK2,k1_tarski(sK0))) | ~v1_funct_1(sK2)),
% 0.22/0.48    inference(subsumption_resolution,[],[f132,f27])).
% 0.22/0.48  fof(f132,plain,(
% 0.22/0.48    k1_tarski(sK0) = k10_relat_1(sK2,k7_relset_1(k1_tarski(sK0),sK1,sK2,k1_tarski(sK0))) | ~v1_funct_2(sK2,k1_tarski(sK0),sK1) | ~v1_funct_1(sK2)),
% 0.22/0.48    inference(subsumption_resolution,[],[f131,f28])).
% 0.22/0.48  fof(f131,plain,(
% 0.22/0.48    k1_tarski(sK0) = k10_relat_1(sK2,k7_relset_1(k1_tarski(sK0),sK1,sK2,k1_tarski(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) | ~v1_funct_2(sK2,k1_tarski(sK0),sK1) | ~v1_funct_1(sK2)),
% 0.22/0.48    inference(subsumption_resolution,[],[f121,f29])).
% 0.22/0.48  fof(f121,plain,(
% 0.22/0.48    k1_tarski(sK0) = k10_relat_1(sK2,k7_relset_1(k1_tarski(sK0),sK1,sK2,k1_tarski(sK0))) | k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) | ~v1_funct_2(sK2,k1_tarski(sK0),sK1) | ~v1_funct_1(sK2)),
% 0.22/0.48    inference(superposition,[],[f36,f85])).
% 0.22/0.48  fof(f85,plain,(
% 0.22/0.48    ( ! [X1] : (k8_relset_1(k1_tarski(sK0),sK1,sK2,X1) = k10_relat_1(sK2,X1)) )),
% 0.22/0.48    inference(resolution,[],[f28,f35])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.48    inference(flattening,[],[f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.48    inference(ennf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_funct_2)).
% 0.22/0.48  fof(f78,plain,(
% 0.22/0.48    spl3_1),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f77])).
% 0.22/0.48  fof(f77,plain,(
% 0.22/0.48    $false | spl3_1),
% 0.22/0.48    inference(subsumption_resolution,[],[f28,f56])).
% 0.22/0.48  fof(f56,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl3_1),
% 0.22/0.48    inference(resolution,[],[f51,f39])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.48  fof(f51,plain,(
% 0.22/0.48    ~v1_relat_1(sK2) | spl3_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f49])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (3521)------------------------------
% 0.22/0.48  % (3521)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (3521)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (3521)Memory used [KB]: 6140
% 0.22/0.48  % (3521)Time elapsed: 0.049 s
% 0.22/0.48  % (3521)------------------------------
% 0.22/0.48  % (3521)------------------------------
% 0.22/0.48  % (3501)Success in time 0.118 s
%------------------------------------------------------------------------------
