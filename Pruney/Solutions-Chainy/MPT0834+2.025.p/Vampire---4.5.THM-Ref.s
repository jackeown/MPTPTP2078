%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:13 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 172 expanded)
%              Number of leaves         :   27 (  59 expanded)
%              Depth                    :   13
%              Number of atoms          :  265 ( 402 expanded)
%              Number of equality atoms :   76 ( 144 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f206,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f99,f101,f107,f113,f124,f131,f133,f148,f201,f205])).

fof(f205,plain,(
    spl3_10 ),
    inference(avatar_contradiction_clause,[],[f204])).

fof(f204,plain,
    ( $false
    | spl3_10 ),
    inference(resolution,[],[f200,f82])).

fof(f82,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(resolution,[],[f75,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f75,plain,(
    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f74,f38])).

fof(f38,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ( k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)
      | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f36])).

fof(f36,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1)
          | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)
        | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1)
        | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
          & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1)) ) ),
    inference(duplicate_literal_removal,[],[f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f51,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f200,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | spl3_10 ),
    inference(avatar_component_clause,[],[f198])).

fof(f198,plain,
    ( spl3_10
  <=> r1_tarski(k2_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f201,plain,
    ( ~ spl3_10
    | ~ spl3_8
    | spl3_9 ),
    inference(avatar_split_clause,[],[f188,f145,f121,f198])).

fof(f121,plain,
    ( spl3_8
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f145,plain,
    ( spl3_9
  <=> k1_relat_1(sK2) = k10_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f188,plain,
    ( ~ v1_relat_1(sK2)
    | ~ r1_tarski(k2_relat_1(sK2),sK1)
    | spl3_9 ),
    inference(trivial_inequality_removal,[],[f187])).

fof(f187,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ r1_tarski(k2_relat_1(sK2),sK1)
    | spl3_9 ),
    inference(superposition,[],[f147,f172])).

fof(f172,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k10_relat_1(X0,X1)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),X1) ) ),
    inference(duplicate_literal_removal,[],[f171])).

fof(f171,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k10_relat_1(X0,X1)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),X1) ) ),
    inference(superposition,[],[f40,f161])).

fof(f161,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0) ) ),
    inference(duplicate_literal_removal,[],[f160])).

fof(f160,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f128,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

fof(f128,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X0,X1) = k10_relat_1(X0,k2_relat_1(k8_relat_1(X1,X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f127])).

fof(f127,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X0,X1) = k10_relat_1(X0,k2_relat_1(k8_relat_1(X1,X0)))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f56,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f43,f41])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f44,f41])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

fof(f40,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f147,plain,
    ( k1_relat_1(sK2) != k10_relat_1(sK2,sK1)
    | spl3_9 ),
    inference(avatar_component_clause,[],[f145])).

fof(f148,plain,
    ( ~ spl3_3
    | ~ spl3_9
    | spl3_5 ),
    inference(avatar_split_clause,[],[f143,f104,f145,f92])).

fof(f92,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f104,plain,
    ( spl3_5
  <=> k1_relset_1(sK0,sK1,sK2) = k10_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f143,plain,
    ( k1_relat_1(sK2) != k10_relat_1(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl3_5 ),
    inference(superposition,[],[f106,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f106,plain,
    ( k1_relset_1(sK0,sK1,sK2) != k10_relat_1(sK2,sK1)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f104])).

fof(f133,plain,(
    spl3_7 ),
    inference(avatar_contradiction_clause,[],[f132])).

fof(f132,plain,
    ( $false
    | spl3_7 ),
    inference(resolution,[],[f119,f89])).

fof(f89,plain,(
    r1_tarski(k1_relat_1(sK2),sK0) ),
    inference(resolution,[],[f88,f47])).

fof(f88,plain,(
    m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f81,f38])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f52,f49])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f119,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl3_7
  <=> r1_tarski(k1_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f131,plain,(
    spl3_8 ),
    inference(avatar_contradiction_clause,[],[f130])).

fof(f130,plain,
    ( $false
    | spl3_8 ),
    inference(resolution,[],[f123,f67])).

fof(f67,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f48,f38])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f123,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f121])).

fof(f124,plain,
    ( ~ spl3_7
    | ~ spl3_8
    | spl3_6 ),
    inference(avatar_split_clause,[],[f115,f110,f121,f117])).

fof(f110,plain,
    ( spl3_6
  <=> k2_relat_1(sK2) = k9_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f115,plain,
    ( ~ v1_relat_1(sK2)
    | ~ r1_tarski(k1_relat_1(sK2),sK0)
    | spl3_6 ),
    inference(trivial_inequality_removal,[],[f114])).

fof(f114,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ r1_tarski(k1_relat_1(sK2),sK0)
    | spl3_6 ),
    inference(superposition,[],[f112,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k9_relat_1(X0,X1)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k1_relat_1(X0),X1) ) ),
    inference(duplicate_literal_removal,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k9_relat_1(X0,X1)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k1_relat_1(X0),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f42,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f112,plain,
    ( k2_relat_1(sK2) != k9_relat_1(sK2,sK0)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f110])).

fof(f113,plain,
    ( ~ spl3_3
    | ~ spl3_6
    | spl3_4 ),
    inference(avatar_split_clause,[],[f108,f96,f110,f92])).

fof(f96,plain,
    ( spl3_4
  <=> k2_relset_1(sK0,sK1,sK2) = k9_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f108,plain,
    ( k2_relat_1(sK2) != k9_relat_1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl3_4 ),
    inference(superposition,[],[f98,f50])).

fof(f98,plain,
    ( k2_relset_1(sK0,sK1,sK2) != k9_relat_1(sK2,sK0)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f96])).

fof(f107,plain,
    ( ~ spl3_3
    | ~ spl3_5
    | spl3_2 ),
    inference(avatar_split_clause,[],[f102,f62,f104,f92])).

fof(f62,plain,
    ( spl3_2
  <=> k1_relset_1(sK0,sK1,sK2) = k8_relset_1(sK0,sK1,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f102,plain,
    ( k1_relset_1(sK0,sK1,sK2) != k10_relat_1(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl3_2 ),
    inference(superposition,[],[f64,f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f64,plain,
    ( k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f101,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f100])).

fof(f100,plain,
    ( $false
    | spl3_3 ),
    inference(resolution,[],[f94,f38])).

fof(f94,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f92])).

fof(f99,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_1 ),
    inference(avatar_split_clause,[],[f90,f58,f96,f92])).

fof(f58,plain,
    ( spl3_1
  <=> k2_relset_1(sK0,sK1,sK2) = k7_relset_1(sK0,sK1,sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f90,plain,
    ( k2_relset_1(sK0,sK1,sK2) != k9_relat_1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl3_1 ),
    inference(superposition,[],[f60,f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f60,plain,
    ( k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f65,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f39,f62,f58])).

fof(f39,plain,
    ( k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)
    | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:36:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (25696)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.46  % (25697)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.46  % (25692)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.46  % (25702)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.47  % (25694)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.47  % (25696)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f206,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(avatar_sat_refutation,[],[f65,f99,f101,f107,f113,f124,f131,f133,f148,f201,f205])).
% 0.22/0.47  fof(f205,plain,(
% 0.22/0.47    spl3_10),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f204])).
% 0.22/0.47  fof(f204,plain,(
% 0.22/0.47    $false | spl3_10),
% 0.22/0.47    inference(resolution,[],[f200,f82])).
% 0.22/0.47  fof(f82,plain,(
% 0.22/0.47    r1_tarski(k2_relat_1(sK2),sK1)),
% 0.22/0.47    inference(resolution,[],[f75,f47])).
% 0.22/0.47  fof(f47,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f28])).
% 0.22/0.47  fof(f28,plain,(
% 0.22/0.47    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.22/0.47    inference(ennf_transformation,[],[f18])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 0.22/0.47    inference(unused_predicate_definition_removal,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.47  fof(f75,plain,(
% 0.22/0.47    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))),
% 0.22/0.47    inference(resolution,[],[f74,f38])).
% 0.22/0.47  fof(f38,plain,(
% 0.22/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.47    inference(cnf_transformation,[],[f37])).
% 0.22/0.47  fof(f37,plain,(
% 0.22/0.47    (k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f36])).
% 0.22/0.47  fof(f36,plain,(
% 0.22/0.47    ? [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1) | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    ? [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1) | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.47    inference(ennf_transformation,[],[f17])).
% 0.22/0.47  fof(f17,negated_conjecture,(
% 0.22/0.47    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 0.22/0.47    inference(negated_conjecture,[],[f16])).
% 0.22/0.47  fof(f16,conjecture,(
% 0.22/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).
% 0.22/0.47  fof(f74,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1))) )),
% 0.22/0.47    inference(duplicate_literal_removal,[],[f73])).
% 0.22/0.47  fof(f73,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.47    inference(superposition,[],[f51,f50])).
% 0.22/0.47  fof(f50,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f31])).
% 0.22/0.47  fof(f31,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.47    inference(ennf_transformation,[],[f13])).
% 0.22/0.47  fof(f13,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.47  fof(f51,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f32])).
% 0.22/0.47  fof(f32,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.47    inference(ennf_transformation,[],[f11])).
% 0.22/0.47  fof(f11,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.22/0.47  fof(f200,plain,(
% 0.22/0.47    ~r1_tarski(k2_relat_1(sK2),sK1) | spl3_10),
% 0.22/0.47    inference(avatar_component_clause,[],[f198])).
% 0.22/0.47  fof(f198,plain,(
% 0.22/0.47    spl3_10 <=> r1_tarski(k2_relat_1(sK2),sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.47  fof(f201,plain,(
% 0.22/0.47    ~spl3_10 | ~spl3_8 | spl3_9),
% 0.22/0.47    inference(avatar_split_clause,[],[f188,f145,f121,f198])).
% 0.22/0.47  fof(f121,plain,(
% 0.22/0.47    spl3_8 <=> v1_relat_1(sK2)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.47  fof(f145,plain,(
% 0.22/0.47    spl3_9 <=> k1_relat_1(sK2) = k10_relat_1(sK2,sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.47  fof(f188,plain,(
% 0.22/0.47    ~v1_relat_1(sK2) | ~r1_tarski(k2_relat_1(sK2),sK1) | spl3_9),
% 0.22/0.47    inference(trivial_inequality_removal,[],[f187])).
% 0.22/0.47  fof(f187,plain,(
% 0.22/0.47    k1_relat_1(sK2) != k1_relat_1(sK2) | ~v1_relat_1(sK2) | ~r1_tarski(k2_relat_1(sK2),sK1) | spl3_9),
% 0.22/0.47    inference(superposition,[],[f147,f172])).
% 0.22/0.47  fof(f172,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k1_relat_1(X0) = k10_relat_1(X0,X1) | ~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),X1)) )),
% 0.22/0.47    inference(duplicate_literal_removal,[],[f171])).
% 0.22/0.47  fof(f171,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k1_relat_1(X0) = k10_relat_1(X0,X1) | ~v1_relat_1(X0) | ~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),X1)) )),
% 0.22/0.47    inference(superposition,[],[f40,f161])).
% 0.22/0.47  fof(f161,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0)) )),
% 0.22/0.47    inference(duplicate_literal_removal,[],[f160])).
% 0.22/0.47  fof(f160,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.47    inference(superposition,[],[f128,f46])).
% 0.22/0.47  fof(f46,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f27])).
% 0.22/0.47  fof(f27,plain,(
% 0.22/0.47    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.47    inference(flattening,[],[f26])).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).
% 0.22/0.47  fof(f128,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k10_relat_1(X0,X1) = k10_relat_1(X0,k2_relat_1(k8_relat_1(X1,X0))) | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(duplicate_literal_removal,[],[f127])).
% 0.22/0.47  fof(f127,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k10_relat_1(X0,X1) = k10_relat_1(X0,k2_relat_1(k8_relat_1(X1,X0))) | ~v1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(superposition,[],[f56,f55])).
% 0.22/0.47  fof(f55,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 0.22/0.47    inference(definition_unfolding,[],[f43,f41])).
% 0.22/0.47  fof(f41,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.47  fof(f43,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f22])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).
% 0.22/0.47  fof(f56,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 0.22/0.47    inference(definition_unfolding,[],[f44,f41])).
% 0.22/0.47  fof(f44,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f23])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,axiom,(
% 0.22/0.47    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).
% 0.22/0.47  fof(f40,plain,(
% 0.22/0.47    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f20])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f7])).
% 0.22/0.47  fof(f7,axiom,(
% 0.22/0.47    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 0.22/0.47  fof(f147,plain,(
% 0.22/0.47    k1_relat_1(sK2) != k10_relat_1(sK2,sK1) | spl3_9),
% 0.22/0.47    inference(avatar_component_clause,[],[f145])).
% 0.22/0.47  fof(f148,plain,(
% 0.22/0.47    ~spl3_3 | ~spl3_9 | spl3_5),
% 0.22/0.47    inference(avatar_split_clause,[],[f143,f104,f145,f92])).
% 0.22/0.47  fof(f92,plain,(
% 0.22/0.47    spl3_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.47  fof(f104,plain,(
% 0.22/0.47    spl3_5 <=> k1_relset_1(sK0,sK1,sK2) = k10_relat_1(sK2,sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.47  fof(f143,plain,(
% 0.22/0.47    k1_relat_1(sK2) != k10_relat_1(sK2,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl3_5),
% 0.22/0.47    inference(superposition,[],[f106,f49])).
% 0.22/0.47  fof(f49,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f30])).
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.47    inference(ennf_transformation,[],[f12])).
% 0.22/0.47  fof(f12,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.47  fof(f106,plain,(
% 0.22/0.47    k1_relset_1(sK0,sK1,sK2) != k10_relat_1(sK2,sK1) | spl3_5),
% 0.22/0.47    inference(avatar_component_clause,[],[f104])).
% 0.22/0.47  fof(f133,plain,(
% 0.22/0.47    spl3_7),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f132])).
% 0.22/0.47  fof(f132,plain,(
% 0.22/0.47    $false | spl3_7),
% 0.22/0.47    inference(resolution,[],[f119,f89])).
% 0.22/0.47  fof(f89,plain,(
% 0.22/0.47    r1_tarski(k1_relat_1(sK2),sK0)),
% 0.22/0.47    inference(resolution,[],[f88,f47])).
% 0.22/0.47  fof(f88,plain,(
% 0.22/0.47    m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0))),
% 0.22/0.47    inference(resolution,[],[f81,f38])).
% 0.22/0.47  fof(f81,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0))) )),
% 0.22/0.47    inference(duplicate_literal_removal,[],[f80])).
% 0.22/0.47  fof(f80,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.47    inference(superposition,[],[f52,f49])).
% 0.22/0.47  fof(f52,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f33])).
% 0.22/0.47  fof(f33,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.47    inference(ennf_transformation,[],[f10])).
% 0.22/0.47  fof(f10,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 0.22/0.47  fof(f119,plain,(
% 0.22/0.47    ~r1_tarski(k1_relat_1(sK2),sK0) | spl3_7),
% 0.22/0.47    inference(avatar_component_clause,[],[f117])).
% 0.22/0.47  fof(f117,plain,(
% 0.22/0.47    spl3_7 <=> r1_tarski(k1_relat_1(sK2),sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.47  fof(f131,plain,(
% 0.22/0.47    spl3_8),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f130])).
% 0.22/0.47  fof(f130,plain,(
% 0.22/0.47    $false | spl3_8),
% 0.22/0.47    inference(resolution,[],[f123,f67])).
% 0.22/0.47  fof(f67,plain,(
% 0.22/0.47    v1_relat_1(sK2)),
% 0.22/0.47    inference(resolution,[],[f48,f38])).
% 0.22/0.47  fof(f48,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f29])).
% 0.22/0.47  fof(f29,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.47    inference(ennf_transformation,[],[f9])).
% 0.22/0.47  fof(f9,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.47  fof(f123,plain,(
% 0.22/0.47    ~v1_relat_1(sK2) | spl3_8),
% 0.22/0.47    inference(avatar_component_clause,[],[f121])).
% 0.22/0.47  fof(f124,plain,(
% 0.22/0.47    ~spl3_7 | ~spl3_8 | spl3_6),
% 0.22/0.47    inference(avatar_split_clause,[],[f115,f110,f121,f117])).
% 0.22/0.47  fof(f110,plain,(
% 0.22/0.47    spl3_6 <=> k2_relat_1(sK2) = k9_relat_1(sK2,sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.47  fof(f115,plain,(
% 0.22/0.47    ~v1_relat_1(sK2) | ~r1_tarski(k1_relat_1(sK2),sK0) | spl3_6),
% 0.22/0.47    inference(trivial_inequality_removal,[],[f114])).
% 0.22/0.47  fof(f114,plain,(
% 0.22/0.47    k2_relat_1(sK2) != k2_relat_1(sK2) | ~v1_relat_1(sK2) | ~r1_tarski(k1_relat_1(sK2),sK0) | spl3_6),
% 0.22/0.47    inference(superposition,[],[f112,f70])).
% 0.22/0.47  fof(f70,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_relat_1(X0) = k9_relat_1(X0,X1) | ~v1_relat_1(X0) | ~r1_tarski(k1_relat_1(X0),X1)) )),
% 0.22/0.47    inference(duplicate_literal_removal,[],[f69])).
% 0.22/0.47  fof(f69,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_relat_1(X0) = k9_relat_1(X0,X1) | ~v1_relat_1(X0) | ~r1_tarski(k1_relat_1(X0),X1) | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(superposition,[],[f42,f45])).
% 0.22/0.47  fof(f45,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f25])).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.47    inference(flattening,[],[f24])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f8])).
% 0.22/0.47  fof(f8,axiom,(
% 0.22/0.47    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).
% 0.22/0.47  fof(f42,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f21])).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,axiom,(
% 0.22/0.47    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.22/0.47  fof(f112,plain,(
% 0.22/0.47    k2_relat_1(sK2) != k9_relat_1(sK2,sK0) | spl3_6),
% 0.22/0.47    inference(avatar_component_clause,[],[f110])).
% 0.22/0.47  fof(f113,plain,(
% 0.22/0.47    ~spl3_3 | ~spl3_6 | spl3_4),
% 0.22/0.47    inference(avatar_split_clause,[],[f108,f96,f110,f92])).
% 0.22/0.47  fof(f96,plain,(
% 0.22/0.47    spl3_4 <=> k2_relset_1(sK0,sK1,sK2) = k9_relat_1(sK2,sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.47  fof(f108,plain,(
% 0.22/0.47    k2_relat_1(sK2) != k9_relat_1(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl3_4),
% 0.22/0.47    inference(superposition,[],[f98,f50])).
% 0.22/0.47  fof(f98,plain,(
% 0.22/0.47    k2_relset_1(sK0,sK1,sK2) != k9_relat_1(sK2,sK0) | spl3_4),
% 0.22/0.47    inference(avatar_component_clause,[],[f96])).
% 0.22/0.47  fof(f107,plain,(
% 0.22/0.47    ~spl3_3 | ~spl3_5 | spl3_2),
% 0.22/0.47    inference(avatar_split_clause,[],[f102,f62,f104,f92])).
% 0.22/0.47  fof(f62,plain,(
% 0.22/0.47    spl3_2 <=> k1_relset_1(sK0,sK1,sK2) = k8_relset_1(sK0,sK1,sK2,sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.47  fof(f102,plain,(
% 0.22/0.47    k1_relset_1(sK0,sK1,sK2) != k10_relat_1(sK2,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl3_2),
% 0.22/0.47    inference(superposition,[],[f64,f54])).
% 0.22/0.47  fof(f54,plain,(
% 0.22/0.47    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f35])).
% 0.22/0.47  fof(f35,plain,(
% 0.22/0.47    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.47    inference(ennf_transformation,[],[f15])).
% 0.22/0.47  fof(f15,axiom,(
% 0.22/0.47    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.22/0.47  fof(f64,plain,(
% 0.22/0.47    k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) | spl3_2),
% 0.22/0.47    inference(avatar_component_clause,[],[f62])).
% 0.22/0.47  fof(f101,plain,(
% 0.22/0.47    spl3_3),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f100])).
% 0.22/0.47  fof(f100,plain,(
% 0.22/0.47    $false | spl3_3),
% 0.22/0.47    inference(resolution,[],[f94,f38])).
% 0.22/0.47  fof(f94,plain,(
% 0.22/0.47    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl3_3),
% 0.22/0.47    inference(avatar_component_clause,[],[f92])).
% 0.22/0.47  fof(f99,plain,(
% 0.22/0.47    ~spl3_3 | ~spl3_4 | spl3_1),
% 0.22/0.47    inference(avatar_split_clause,[],[f90,f58,f96,f92])).
% 0.22/0.47  fof(f58,plain,(
% 0.22/0.47    spl3_1 <=> k2_relset_1(sK0,sK1,sK2) = k7_relset_1(sK0,sK1,sK2,sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.47  fof(f90,plain,(
% 0.22/0.47    k2_relset_1(sK0,sK1,sK2) != k9_relat_1(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl3_1),
% 0.22/0.47    inference(superposition,[],[f60,f53])).
% 0.22/0.47  fof(f53,plain,(
% 0.22/0.47    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f34])).
% 0.22/0.47  fof(f34,plain,(
% 0.22/0.47    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.47    inference(ennf_transformation,[],[f14])).
% 0.22/0.47  fof(f14,axiom,(
% 0.22/0.47    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.22/0.47  fof(f60,plain,(
% 0.22/0.47    k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0) | spl3_1),
% 0.22/0.47    inference(avatar_component_clause,[],[f58])).
% 0.22/0.47  fof(f65,plain,(
% 0.22/0.47    ~spl3_1 | ~spl3_2),
% 0.22/0.47    inference(avatar_split_clause,[],[f39,f62,f58])).
% 0.22/0.47  fof(f39,plain,(
% 0.22/0.47    k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f37])).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (25696)------------------------------
% 0.22/0.47  % (25696)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (25696)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (25696)Memory used [KB]: 6140
% 0.22/0.47  % (25696)Time elapsed: 0.060 s
% 0.22/0.47  % (25696)------------------------------
% 0.22/0.47  % (25696)------------------------------
% 0.22/0.47  % (25688)Success in time 0.106 s
%------------------------------------------------------------------------------
