%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:11 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 140 expanded)
%              Number of leaves         :   27 (  53 expanded)
%              Depth                    :   12
%              Number of atoms          :  157 ( 223 expanded)
%              Number of equality atoms :   56 (  96 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f391,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f74,f84,f127,f138,f342,f384])).

fof(f384,plain,
    ( spl2_17
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f383,f134,f339])).

fof(f339,plain,
    ( spl2_17
  <=> sK1 = k10_relat_1(k6_partfun1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f134,plain,
    ( spl2_6
  <=> k1_xboole_0 = k4_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f383,plain,
    ( sK1 = k10_relat_1(k6_partfun1(sK0),sK1)
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f371,f37])).

fof(f37,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f371,plain,
    ( k4_xboole_0(sK1,k1_xboole_0) = k10_relat_1(k6_partfun1(sK0),sK1)
    | ~ spl2_6 ),
    inference(superposition,[],[f343,f136])).

fof(f136,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f134])).

fof(f343,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X2,X3)) = k10_relat_1(k6_partfun1(X3),X2) ),
    inference(forward_demodulation,[],[f179,f130])).

fof(f130,plain,(
    ! [X0,X1] : k1_relat_1(k5_relat_1(k6_partfun1(X0),k6_partfun1(X1))) = k10_relat_1(k6_partfun1(X0),X1) ),
    inference(forward_demodulation,[],[f128,f62])).

fof(f62,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f39,f36])).

fof(f36,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f39,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f128,plain,(
    ! [X0,X1] : k1_relat_1(k5_relat_1(k6_partfun1(X0),k6_partfun1(X1))) = k10_relat_1(k6_partfun1(X0),k1_relat_1(k6_partfun1(X1))) ),
    inference(unit_resulting_resolution,[],[f59,f59,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f59,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f35,f36])).

fof(f35,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f179,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X2,X3)) = k1_relat_1(k5_relat_1(k6_partfun1(X3),k6_partfun1(X2))) ),
    inference(superposition,[],[f62,f165])).

fof(f165,plain,(
    ! [X0,X1] : k5_relat_1(k6_partfun1(X1),k6_partfun1(X0)) = k6_partfun1(k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(forward_demodulation,[],[f64,f63])).

fof(f63,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f47,f58])).

fof(f58,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f45,f57])).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f46,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f52,f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f52,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f46,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f64,plain,(
    ! [X0,X1] : k5_relat_1(k6_partfun1(X1),k6_partfun1(X0)) = k6_partfun1(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f48,f36,f36,f36,f58])).

fof(f48,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(f342,plain,
    ( ~ spl2_17
    | spl2_1 ),
    inference(avatar_split_clause,[],[f337,f66,f339])).

fof(f66,plain,
    ( spl2_1
  <=> sK1 = k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f337,plain,
    ( sK1 != k10_relat_1(k6_partfun1(sK0),sK1)
    | spl2_1 ),
    inference(superposition,[],[f68,f190])).

fof(f190,plain,(
    ! [X0,X1] : k8_relset_1(X0,X0,k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1) ),
    inference(unit_resulting_resolution,[],[f60,f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f60,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f38,f36])).

fof(f38,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f68,plain,
    ( sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f66])).

fof(f138,plain,
    ( spl2_6
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f132,f124,f134])).

fof(f124,plain,
    ( spl2_5
  <=> v1_xboole_0(k4_xboole_0(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f132,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl2_5 ),
    inference(resolution,[],[f126,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f126,plain,
    ( v1_xboole_0(k4_xboole_0(sK1,sK0))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f124])).

fof(f127,plain,
    ( spl2_5
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f119,f80,f124])).

fof(f80,plain,
    ( spl2_3
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f119,plain,
    ( v1_xboole_0(k4_xboole_0(sK1,sK0))
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f43,f108,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f108,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(sK1,X0),sK0)
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f82,f44,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f82,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f80])).

fof(f43,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f84,plain,
    ( spl2_3
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f78,f71,f80])).

fof(f71,plain,
    ( spl2_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f78,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_2 ),
    inference(resolution,[],[f50,f73])).

fof(f73,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f74,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f33,f71])).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f30])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_2)).

fof(f69,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f34,f66])).

fof(f34,plain,(
    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n013.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 18:54:09 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.43  % (28608)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.48  % (28600)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (28601)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (28604)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.48  % (28602)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.49  % (28603)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.49  % (28609)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.49  % (28607)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.49  % (28611)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.49  % (28612)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.49  % (28610)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.50  % (28603)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f391,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f69,f74,f84,f127,f138,f342,f384])).
% 0.22/0.50  fof(f384,plain,(
% 0.22/0.50    spl2_17 | ~spl2_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f383,f134,f339])).
% 0.22/0.50  fof(f339,plain,(
% 0.22/0.50    spl2_17 <=> sK1 = k10_relat_1(k6_partfun1(sK0),sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.22/0.50  fof(f134,plain,(
% 0.22/0.50    spl2_6 <=> k1_xboole_0 = k4_xboole_0(sK1,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.50  fof(f383,plain,(
% 0.22/0.50    sK1 = k10_relat_1(k6_partfun1(sK0),sK1) | ~spl2_6),
% 0.22/0.50    inference(forward_demodulation,[],[f371,f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.50  fof(f371,plain,(
% 0.22/0.50    k4_xboole_0(sK1,k1_xboole_0) = k10_relat_1(k6_partfun1(sK0),sK1) | ~spl2_6),
% 0.22/0.50    inference(superposition,[],[f343,f136])).
% 0.22/0.50  fof(f136,plain,(
% 0.22/0.50    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl2_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f134])).
% 0.22/0.50  fof(f343,plain,(
% 0.22/0.50    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X2,X3)) = k10_relat_1(k6_partfun1(X3),X2)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f179,f130])).
% 0.22/0.50  fof(f130,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(k6_partfun1(X0),k6_partfun1(X1))) = k10_relat_1(k6_partfun1(X0),X1)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f128,f62])).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 0.22/0.50    inference(definition_unfolding,[],[f39,f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,axiom,(
% 0.22/0.50    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,axiom,(
% 0.22/0.50    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.22/0.50  fof(f128,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(k6_partfun1(X0),k6_partfun1(X1))) = k10_relat_1(k6_partfun1(X0),k1_relat_1(k6_partfun1(X1)))) )),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f59,f59,f42])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,axiom,(
% 0.22/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 0.22/0.50    inference(definition_unfolding,[],[f35,f36])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,axiom,(
% 0.22/0.50    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.22/0.50  fof(f179,plain,(
% 0.22/0.50    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X2,X3)) = k1_relat_1(k5_relat_1(k6_partfun1(X3),k6_partfun1(X2)))) )),
% 0.22/0.50    inference(superposition,[],[f62,f165])).
% 0.22/0.50  fof(f165,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k5_relat_1(k6_partfun1(X1),k6_partfun1(X0)) = k6_partfun1(k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.22/0.50    inference(forward_demodulation,[],[f64,f63])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 0.22/0.50    inference(definition_unfolding,[],[f47,f58])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 0.22/0.50    inference(definition_unfolding,[],[f45,f57])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.22/0.50    inference(definition_unfolding,[],[f46,f56])).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.22/0.50    inference(definition_unfolding,[],[f52,f54])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,axiom,(
% 0.22/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k5_relat_1(k6_partfun1(X1),k6_partfun1(X0)) = k6_partfun1(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 0.22/0.50    inference(definition_unfolding,[],[f48,f36,f36,f36,f58])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,axiom,(
% 0.22/0.50    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 0.22/0.50  fof(f342,plain,(
% 0.22/0.50    ~spl2_17 | spl2_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f337,f66,f339])).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    spl2_1 <=> sK1 = k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.50  fof(f337,plain,(
% 0.22/0.50    sK1 != k10_relat_1(k6_partfun1(sK0),sK1) | spl2_1),
% 0.22/0.50    inference(superposition,[],[f68,f190])).
% 0.22/0.50  fof(f190,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) = k10_relat_1(k6_partfun1(X0),X1)) )),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f60,f55])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.22/0.50    inference(definition_unfolding,[],[f38,f36])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f18,axiom,(
% 0.22/0.50    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) | spl2_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f66])).
% 0.22/0.50  fof(f138,plain,(
% 0.22/0.50    spl2_6 | ~spl2_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f132,f124,f134])).
% 0.22/0.50  fof(f124,plain,(
% 0.22/0.50    spl2_5 <=> v1_xboole_0(k4_xboole_0(sK1,sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.50  fof(f132,plain,(
% 0.22/0.50    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl2_5),
% 0.22/0.50    inference(resolution,[],[f126,f41])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.50  fof(f126,plain,(
% 0.22/0.50    v1_xboole_0(k4_xboole_0(sK1,sK0)) | ~spl2_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f124])).
% 0.22/0.50  fof(f127,plain,(
% 0.22/0.50    spl2_5 | ~spl2_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f119,f80,f124])).
% 0.22/0.50  fof(f80,plain,(
% 0.22/0.50    spl2_3 <=> r1_tarski(sK1,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.50  fof(f119,plain,(
% 0.22/0.50    v1_xboole_0(k4_xboole_0(sK1,sK0)) | ~spl2_3),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f43,f108,f49])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.22/0.50    inference(flattening,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.22/0.50  fof(f108,plain,(
% 0.22/0.50    ( ! [X0] : (r1_tarski(k4_xboole_0(sK1,X0),sK0)) ) | ~spl2_3),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f82,f44,f53])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.50    inference(flattening,[],[f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.22/0.50  fof(f82,plain,(
% 0.22/0.50    r1_tarski(sK1,sK0) | ~spl2_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f80])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.22/0.50  fof(f84,plain,(
% 0.22/0.50    spl2_3 | ~spl2_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f78,f71,f80])).
% 0.22/0.50  fof(f71,plain,(
% 0.22/0.50    spl2_2 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.50  fof(f78,plain,(
% 0.22/0.50    r1_tarski(sK1,sK0) | ~spl2_2),
% 0.22/0.50    inference(resolution,[],[f50,f73])).
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl2_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f71])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.50    inference(nnf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.50  fof(f74,plain,(
% 0.22/0.50    spl2_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f33,f71])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.50    inference(cnf_transformation,[],[f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ? [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0))) => (sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ? [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f21])).
% 0.22/0.50  fof(f21,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 0.22/0.50    inference(negated_conjecture,[],[f20])).
% 0.22/0.50  fof(f20,conjecture,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_2)).
% 0.22/0.50  fof(f69,plain,(
% 0.22/0.50    ~spl2_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f34,f66])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    sK1 != k8_relset_1(sK0,sK0,k6_partfun1(sK0),sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f31])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (28603)------------------------------
% 0.22/0.50  % (28603)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (28603)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (28603)Memory used [KB]: 6268
% 0.22/0.50  % (28603)Time elapsed: 0.062 s
% 0.22/0.50  % (28603)------------------------------
% 0.22/0.50  % (28603)------------------------------
% 0.22/0.50  % (28596)Success in time 0.14 s
%------------------------------------------------------------------------------
