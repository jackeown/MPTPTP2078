%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:45 EST 2020

% Result     : Theorem 3.47s
% Output     : Refutation 3.47s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 490 expanded)
%              Number of leaves         :   31 ( 158 expanded)
%              Depth                    :   17
%              Number of atoms          :  356 ( 898 expanded)
%              Number of equality atoms :   48 ( 285 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2207,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f85,f90,f571,f1002,f1054,f1078,f1470,f1531,f1547,f2086,f2204])).

fof(f2204,plain,
    ( ~ spl3_2
    | spl3_31 ),
    inference(avatar_contradiction_clause,[],[f2203])).

fof(f2203,plain,
    ( $false
    | ~ spl3_2
    | spl3_31 ),
    inference(subsumption_resolution,[],[f2200,f89])).

fof(f89,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl3_2
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f2200,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_31 ),
    inference(resolution,[],[f2085,f696])).

fof(f696,plain,(
    ! [X72,X71,X73] :
      ( r1_tarski(k7_relat_1(k7_relat_1(X71,X73),X72),k7_relat_1(X71,X72))
      | ~ v1_relat_1(X71) ) ),
    inference(subsumption_resolution,[],[f607,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f607,plain,(
    ! [X72,X71,X73] :
      ( r1_tarski(k7_relat_1(k7_relat_1(X71,X73),X72),k7_relat_1(X71,X72))
      | ~ v1_relat_1(k7_relat_1(X71,X72))
      | ~ v1_relat_1(X71) ) ),
    inference(superposition,[],[f55,f458])).

fof(f458,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X0,X1),X2) = k7_relat_1(k7_relat_1(X0,X2),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f403])).

fof(f403,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X0,X1),X2) = k7_relat_1(k7_relat_1(X0,X2),X1)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f78,f144])).

fof(f144,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X0)))
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f78,f76])).

fof(f76,plain,(
    ! [X0,X1] : k4_enumset1(X0,X0,X0,X0,X0,X1) = k4_enumset1(X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f50,f73,f73])).

fof(f73,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f51,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f65,f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f69,f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f69,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f65,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f67,f74])).

fof(f74,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f52,f73])).

fof(f52,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(f2085,plain,
    ( ~ r1_tarski(k7_relat_1(k7_relat_1(sK2,sK0),sK1),k7_relat_1(sK2,sK1))
    | spl3_31 ),
    inference(avatar_component_clause,[],[f2083])).

fof(f2083,plain,
    ( spl3_31
  <=> r1_tarski(k7_relat_1(k7_relat_1(sK2,sK0),sK1),k7_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f2086,plain,
    ( ~ spl3_31
    | ~ spl3_2
    | spl3_22 ),
    inference(avatar_split_clause,[],[f2081,f1522,f87,f2083])).

fof(f1522,plain,
    ( spl3_22
  <=> r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1)),k9_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f2081,plain,
    ( ~ r1_tarski(k7_relat_1(k7_relat_1(sK2,sK0),sK1),k7_relat_1(sK2,sK1))
    | ~ spl3_2
    | spl3_22 ),
    inference(subsumption_resolution,[],[f2077,f89])).

fof(f2077,plain,
    ( ~ r1_tarski(k7_relat_1(k7_relat_1(sK2,sK0),sK1),k7_relat_1(sK2,sK1))
    | ~ v1_relat_1(sK2)
    | spl3_22 ),
    inference(resolution,[],[f1524,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_relat_1(X2),k9_relat_1(X0,X1))
      | ~ r1_tarski(X2,k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f107,f54])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_relat_1(X2),k9_relat_1(X0,X1))
      | ~ r1_tarski(X2,k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f103,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f103,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f48,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f49,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(f1524,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1)),k9_relat_1(sK2,sK1))
    | spl3_22 ),
    inference(avatar_component_clause,[],[f1522])).

fof(f1547,plain,
    ( ~ spl3_2
    | spl3_23 ),
    inference(avatar_contradiction_clause,[],[f1546])).

fof(f1546,plain,
    ( $false
    | ~ spl3_2
    | spl3_23 ),
    inference(subsumption_resolution,[],[f1541,f89])).

fof(f1541,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_23 ),
    inference(resolution,[],[f1530,f774])).

fof(f774,plain,(
    ! [X6,X8,X7] :
      ( r1_tarski(k7_relat_1(k7_relat_1(X6,X8),X7),k7_relat_1(X6,X8))
      | ~ v1_relat_1(X6) ) ),
    inference(duplicate_literal_removal,[],[f763])).

fof(f763,plain,(
    ! [X6,X8,X7] :
      ( r1_tarski(k7_relat_1(k7_relat_1(X6,X8),X7),k7_relat_1(X6,X8))
      | ~ v1_relat_1(X6)
      | ~ v1_relat_1(X6) ) ),
    inference(superposition,[],[f696,f458])).

fof(f1530,plain,
    ( ~ r1_tarski(k7_relat_1(k7_relat_1(sK2,sK0),sK1),k7_relat_1(sK2,sK0))
    | spl3_23 ),
    inference(avatar_component_clause,[],[f1528])).

fof(f1528,plain,
    ( spl3_23
  <=> r1_tarski(k7_relat_1(k7_relat_1(sK2,sK0),sK1),k7_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f1531,plain,
    ( ~ spl3_22
    | ~ spl3_23
    | ~ spl3_9
    | spl3_19 ),
    inference(avatar_split_clause,[],[f1526,f1467,f953,f1528,f1522])).

fof(f953,plain,
    ( spl3_9
  <=> v1_relat_1(k7_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f1467,plain,
    ( spl3_19
  <=> r1_tarski(k7_relat_1(k7_relat_1(sK2,sK0),sK1),k8_relat_1(k9_relat_1(sK2,sK1),k7_relat_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f1526,plain,
    ( ~ r1_tarski(k7_relat_1(k7_relat_1(sK2,sK0),sK1),k7_relat_1(sK2,sK0))
    | ~ r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1)),k9_relat_1(sK2,sK1))
    | ~ spl3_9
    | spl3_19 ),
    inference(subsumption_resolution,[],[f1515,f954])).

fof(f954,plain,
    ( v1_relat_1(k7_relat_1(sK2,sK0))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f953])).

fof(f1515,plain,
    ( ~ r1_tarski(k7_relat_1(k7_relat_1(sK2,sK0),sK1),k7_relat_1(sK2,sK0))
    | ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | ~ r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1)),k9_relat_1(sK2,sK1))
    | spl3_19 ),
    inference(resolution,[],[f1469,f132])).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k8_relat_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X1),X0) ) ),
    inference(subsumption_resolution,[],[f126,f92])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k8_relat_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f119,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f59,f92])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_relat_1)).

fof(f1469,plain,
    ( ~ r1_tarski(k7_relat_1(k7_relat_1(sK2,sK0),sK1),k8_relat_1(k9_relat_1(sK2,sK1),k7_relat_1(sK2,sK0)))
    | spl3_19 ),
    inference(avatar_component_clause,[],[f1467])).

fof(f1470,plain,
    ( ~ spl3_19
    | ~ spl3_5
    | spl3_7 ),
    inference(avatar_split_clause,[],[f1465,f942,f932,f1467])).

fof(f932,plain,
    ( spl3_5
  <=> v1_relat_1(k8_relat_1(k9_relat_1(sK2,sK1),k7_relat_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f942,plain,
    ( spl3_7
  <=> r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1)),k2_relat_1(k8_relat_1(k9_relat_1(sK2,sK1),k7_relat_1(sK2,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f1465,plain,
    ( ~ r1_tarski(k7_relat_1(k7_relat_1(sK2,sK0),sK1),k8_relat_1(k9_relat_1(sK2,sK1),k7_relat_1(sK2,sK0)))
    | ~ spl3_5
    | spl3_7 ),
    inference(subsumption_resolution,[],[f1455,f933])).

fof(f933,plain,
    ( v1_relat_1(k8_relat_1(k9_relat_1(sK2,sK1),k7_relat_1(sK2,sK0)))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f932])).

fof(f1455,plain,
    ( ~ r1_tarski(k7_relat_1(k7_relat_1(sK2,sK0),sK1),k8_relat_1(k9_relat_1(sK2,sK1),k7_relat_1(sK2,sK0)))
    | ~ v1_relat_1(k8_relat_1(k9_relat_1(sK2,sK1),k7_relat_1(sK2,sK0)))
    | spl3_7 ),
    inference(resolution,[],[f944,f103])).

fof(f944,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1)),k2_relat_1(k8_relat_1(k9_relat_1(sK2,sK1),k7_relat_1(sK2,sK0))))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f942])).

fof(f1078,plain,
    ( ~ spl3_7
    | ~ spl3_2
    | spl3_3 ),
    inference(avatar_split_clause,[],[f1077,f568,f87,f942])).

fof(f568,plain,
    ( spl3_3
  <=> r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1)),k1_setfam_1(k4_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f1077,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1)),k2_relat_1(k8_relat_1(k9_relat_1(sK2,sK1),k7_relat_1(sK2,sK0))))
    | ~ spl3_2
    | spl3_3 ),
    inference(subsumption_resolution,[],[f1062,f89])).

fof(f1062,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1)),k2_relat_1(k8_relat_1(k9_relat_1(sK2,sK1),k7_relat_1(sK2,sK0))))
    | ~ v1_relat_1(sK2)
    | spl3_3 ),
    inference(superposition,[],[f570,f174])).

fof(f174,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(k8_relat_1(X2,k7_relat_1(X0,X1))) = k1_setfam_1(k4_enumset1(k9_relat_1(X0,X1),k9_relat_1(X0,X1),k9_relat_1(X0,X1),k9_relat_1(X0,X1),k9_relat_1(X0,X1),X2))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f170,f54])).

fof(f170,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(k8_relat_1(X2,k7_relat_1(X0,X1))) = k1_setfam_1(k4_enumset1(k9_relat_1(X0,X1),k9_relat_1(X0,X1),k9_relat_1(X0,X1),k9_relat_1(X0,X1),k9_relat_1(X0,X1),X2))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f77,f56])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k1_setfam_1(k4_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f57,f74])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).

fof(f570,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1)),k1_setfam_1(k4_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f568])).

fof(f1054,plain,
    ( ~ spl3_2
    | spl3_5 ),
    inference(avatar_contradiction_clause,[],[f1053])).

fof(f1053,plain,
    ( $false
    | ~ spl3_2
    | spl3_5 ),
    inference(subsumption_resolution,[],[f1043,f89])).

fof(f1043,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_5 ),
    inference(resolution,[],[f934,f247])).

fof(f247,plain,(
    ! [X12,X10,X11] :
      ( v1_relat_1(k8_relat_1(X11,k7_relat_1(X10,X12)))
      | ~ v1_relat_1(X10) ) ),
    inference(resolution,[],[f242,f79])).

fof(f79,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f242,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ r1_tarski(X3,k7_relat_1(X4,X5))
      | ~ v1_relat_1(X4)
      | v1_relat_1(k8_relat_1(X6,X3)) ) ),
    inference(subsumption_resolution,[],[f233,f114])).

fof(f114,plain,(
    ! [X4,X5,X3] :
      ( v1_relat_1(k7_relat_1(k8_relat_1(X3,X4),X5))
      | ~ v1_relat_1(X4) ) ),
    inference(subsumption_resolution,[],[f111,f54])).

fof(f111,plain,(
    ! [X4,X5,X3] :
      ( v1_relat_1(k7_relat_1(k8_relat_1(X3,X4),X5))
      | ~ v1_relat_1(k7_relat_1(X4,X5))
      | ~ v1_relat_1(X4) ) ),
    inference(superposition,[],[f53,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_relat_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f233,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ r1_tarski(X3,k7_relat_1(X4,X5))
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(k7_relat_1(k8_relat_1(X6,X4),X5))
      | v1_relat_1(k8_relat_1(X6,X3)) ) ),
    inference(resolution,[],[f133,f92])).

fof(f133,plain,(
    ! [X6,X4,X5,X3] :
      ( r1_tarski(k8_relat_1(X3,X6),k7_relat_1(k8_relat_1(X3,X4),X5))
      | ~ r1_tarski(X6,k7_relat_1(X4,X5))
      | ~ v1_relat_1(X4) ) ),
    inference(subsumption_resolution,[],[f129,f54])).

fof(f129,plain,(
    ! [X6,X4,X5,X3] :
      ( r1_tarski(k8_relat_1(X3,X6),k7_relat_1(k8_relat_1(X3,X4),X5))
      | ~ r1_tarski(X6,k7_relat_1(X4,X5))
      | ~ v1_relat_1(k7_relat_1(X4,X5))
      | ~ v1_relat_1(X4) ) ),
    inference(superposition,[],[f119,f66])).

fof(f934,plain,
    ( ~ v1_relat_1(k8_relat_1(k9_relat_1(sK2,sK1),k7_relat_1(sK2,sK0)))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f932])).

fof(f1002,plain,
    ( ~ spl3_2
    | spl3_9 ),
    inference(avatar_contradiction_clause,[],[f1001])).

fof(f1001,plain,
    ( $false
    | ~ spl3_2
    | spl3_9 ),
    inference(subsumption_resolution,[],[f998,f89])).

fof(f998,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_9 ),
    inference(resolution,[],[f955,f54])).

fof(f955,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f953])).

fof(f571,plain,
    ( ~ spl3_3
    | spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f566,f87,f82,f568])).

fof(f82,plain,
    ( spl3_1
  <=> r1_tarski(k9_relat_1(sK2,k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k1_setfam_1(k4_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f566,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1)),k1_setfam_1(k4_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))))
    | spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f561,f89])).

fof(f561,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1)),k1_setfam_1(k4_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))))
    | ~ v1_relat_1(sK2)
    | spl3_1 ),
    inference(superposition,[],[f84,f160])).

fof(f160,plain,(
    ! [X6,X8,X7] :
      ( k9_relat_1(X6,k1_setfam_1(k4_enumset1(X7,X7,X7,X7,X7,X8))) = k2_relat_1(k7_relat_1(k7_relat_1(X6,X7),X8))
      | ~ v1_relat_1(X6) ) ),
    inference(duplicate_literal_removal,[],[f148])).

fof(f148,plain,(
    ! [X6,X8,X7] :
      ( k9_relat_1(X6,k1_setfam_1(k4_enumset1(X7,X7,X7,X7,X7,X8))) = k2_relat_1(k7_relat_1(k7_relat_1(X6,X7),X8))
      | ~ v1_relat_1(X6)
      | ~ v1_relat_1(X6) ) ),
    inference(superposition,[],[f56,f78])).

fof(f84,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k1_setfam_1(k4_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f82])).

fof(f90,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f45,f87])).

fof(f45,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f40])).

fof(f40,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_relat_1)).

fof(f85,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f75,f82])).

fof(f75,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k1_setfam_1(k4_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))) ),
    inference(definition_unfolding,[],[f46,f74,f74])).

fof(f46,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:47:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (4195)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.50  % (4209)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.51  % (4198)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (4199)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (4201)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.23/0.51  % (4220)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.23/0.51  % (4196)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.23/0.51  % (4208)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.23/0.51  % (4204)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.23/0.52  % (4203)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.23/0.52  % (4214)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.23/0.52  % (4212)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.23/0.52  % (4200)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.23/0.52  % (4219)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.23/0.52  % (4206)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.23/0.52  % (4197)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.23/0.52  % (4221)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.34/0.53  % (4222)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.34/0.53  % (4223)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.34/0.53  % (4222)Refutation not found, incomplete strategy% (4222)------------------------------
% 1.34/0.53  % (4222)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.53  % (4222)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.53  
% 1.34/0.53  % (4222)Memory used [KB]: 10746
% 1.34/0.53  % (4222)Time elapsed: 0.132 s
% 1.34/0.53  % (4222)------------------------------
% 1.34/0.53  % (4222)------------------------------
% 1.34/0.53  % (4194)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.34/0.53  % (4204)Refutation not found, incomplete strategy% (4204)------------------------------
% 1.34/0.53  % (4204)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.53  % (4217)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.34/0.53  % (4205)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.34/0.54  % (4213)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.34/0.54  % (4204)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.54  
% 1.34/0.54  % (4204)Memory used [KB]: 10746
% 1.34/0.54  % (4204)Time elapsed: 0.132 s
% 1.34/0.54  % (4204)------------------------------
% 1.34/0.54  % (4204)------------------------------
% 1.34/0.54  % (4218)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.34/0.54  % (4215)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.34/0.54  % (4216)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.34/0.54  % (4210)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.34/0.55  % (4210)Refutation not found, incomplete strategy% (4210)------------------------------
% 1.34/0.55  % (4210)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.55  % (4210)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.55  
% 1.34/0.55  % (4210)Memory used [KB]: 10618
% 1.34/0.55  % (4210)Time elapsed: 0.129 s
% 1.34/0.55  % (4210)------------------------------
% 1.34/0.55  % (4210)------------------------------
% 1.34/0.55  % (4202)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.34/0.55  % (4207)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.34/0.55  % (4211)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 2.03/0.66  % (4224)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.03/0.66  % (4197)Refutation not found, incomplete strategy% (4197)------------------------------
% 2.03/0.66  % (4197)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.03/0.66  % (4197)Termination reason: Refutation not found, incomplete strategy
% 2.03/0.66  
% 2.03/0.66  % (4197)Memory used [KB]: 6140
% 2.03/0.66  % (4197)Time elapsed: 0.267 s
% 2.03/0.66  % (4197)------------------------------
% 2.03/0.66  % (4197)------------------------------
% 2.03/0.67  % (4226)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.03/0.68  % (4225)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.54/0.70  % (4226)Refutation not found, incomplete strategy% (4226)------------------------------
% 2.54/0.70  % (4226)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.54/0.70  % (4226)Termination reason: Refutation not found, incomplete strategy
% 2.54/0.70  
% 2.54/0.70  % (4226)Memory used [KB]: 6140
% 2.54/0.70  % (4226)Time elapsed: 0.123 s
% 2.54/0.70  % (4226)------------------------------
% 2.54/0.70  % (4226)------------------------------
% 3.30/0.80  % (4218)Time limit reached!
% 3.30/0.80  % (4218)------------------------------
% 3.30/0.80  % (4218)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.30/0.81  % (4218)Termination reason: Time limit
% 3.30/0.81  
% 3.30/0.81  % (4218)Memory used [KB]: 13432
% 3.30/0.81  % (4218)Time elapsed: 0.410 s
% 3.30/0.81  % (4218)------------------------------
% 3.30/0.81  % (4218)------------------------------
% 3.30/0.82  % (4196)Time limit reached!
% 3.30/0.82  % (4196)------------------------------
% 3.30/0.82  % (4196)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.30/0.82  % (4196)Termination reason: Time limit
% 3.30/0.82  
% 3.30/0.82  % (4196)Memory used [KB]: 7547
% 3.30/0.82  % (4196)Time elapsed: 0.429 s
% 3.30/0.82  % (4196)------------------------------
% 3.30/0.82  % (4196)------------------------------
% 3.30/0.82  % (4227)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 3.47/0.84  % (4228)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 3.47/0.86  % (4225)Refutation found. Thanks to Tanya!
% 3.47/0.86  % SZS status Theorem for theBenchmark
% 3.47/0.87  % SZS output start Proof for theBenchmark
% 3.47/0.87  fof(f2207,plain,(
% 3.47/0.87    $false),
% 3.47/0.87    inference(avatar_sat_refutation,[],[f85,f90,f571,f1002,f1054,f1078,f1470,f1531,f1547,f2086,f2204])).
% 3.47/0.87  fof(f2204,plain,(
% 3.47/0.87    ~spl3_2 | spl3_31),
% 3.47/0.87    inference(avatar_contradiction_clause,[],[f2203])).
% 3.47/0.87  fof(f2203,plain,(
% 3.47/0.87    $false | (~spl3_2 | spl3_31)),
% 3.47/0.87    inference(subsumption_resolution,[],[f2200,f89])).
% 3.47/0.87  fof(f89,plain,(
% 3.47/0.87    v1_relat_1(sK2) | ~spl3_2),
% 3.47/0.87    inference(avatar_component_clause,[],[f87])).
% 3.47/0.87  fof(f87,plain,(
% 3.47/0.87    spl3_2 <=> v1_relat_1(sK2)),
% 3.47/0.87    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 3.47/0.87  fof(f2200,plain,(
% 3.47/0.87    ~v1_relat_1(sK2) | spl3_31),
% 3.47/0.87    inference(resolution,[],[f2085,f696])).
% 3.47/0.87  fof(f696,plain,(
% 3.47/0.87    ( ! [X72,X71,X73] : (r1_tarski(k7_relat_1(k7_relat_1(X71,X73),X72),k7_relat_1(X71,X72)) | ~v1_relat_1(X71)) )),
% 3.47/0.87    inference(subsumption_resolution,[],[f607,f54])).
% 3.47/0.87  fof(f54,plain,(
% 3.47/0.87    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 3.47/0.87    inference(cnf_transformation,[],[f28])).
% 3.47/0.87  fof(f28,plain,(
% 3.47/0.87    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 3.47/0.87    inference(ennf_transformation,[],[f10])).
% 3.47/0.87  fof(f10,axiom,(
% 3.47/0.87    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 3.47/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 3.47/0.87  fof(f607,plain,(
% 3.47/0.87    ( ! [X72,X71,X73] : (r1_tarski(k7_relat_1(k7_relat_1(X71,X73),X72),k7_relat_1(X71,X72)) | ~v1_relat_1(k7_relat_1(X71,X72)) | ~v1_relat_1(X71)) )),
% 3.47/0.87    inference(superposition,[],[f55,f458])).
% 3.47/0.87  fof(f458,plain,(
% 3.47/0.87    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X0,X1),X2) = k7_relat_1(k7_relat_1(X0,X2),X1) | ~v1_relat_1(X0)) )),
% 3.47/0.87    inference(duplicate_literal_removal,[],[f403])).
% 3.47/0.87  fof(f403,plain,(
% 3.47/0.87    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X0,X1),X2) = k7_relat_1(k7_relat_1(X0,X2),X1) | ~v1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.47/0.87    inference(superposition,[],[f78,f144])).
% 3.47/0.87  fof(f144,plain,(
% 3.47/0.87    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X0))) | ~v1_relat_1(X2)) )),
% 3.47/0.87    inference(superposition,[],[f78,f76])).
% 3.47/0.87  fof(f76,plain,(
% 3.47/0.87    ( ! [X0,X1] : (k4_enumset1(X0,X0,X0,X0,X0,X1) = k4_enumset1(X1,X1,X1,X1,X1,X0)) )),
% 3.47/0.87    inference(definition_unfolding,[],[f50,f73,f73])).
% 3.47/0.87  fof(f73,plain,(
% 3.47/0.87    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 3.47/0.87    inference(definition_unfolding,[],[f51,f72])).
% 3.47/0.87  fof(f72,plain,(
% 3.47/0.87    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 3.47/0.87    inference(definition_unfolding,[],[f65,f71])).
% 3.47/0.87  fof(f71,plain,(
% 3.47/0.87    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 3.47/0.87    inference(definition_unfolding,[],[f69,f70])).
% 3.47/0.87  fof(f70,plain,(
% 3.47/0.87    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.47/0.87    inference(cnf_transformation,[],[f6])).
% 3.47/0.87  fof(f6,axiom,(
% 3.47/0.87    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 3.47/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 3.47/0.87  fof(f69,plain,(
% 3.47/0.87    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 3.47/0.87    inference(cnf_transformation,[],[f5])).
% 3.47/0.87  fof(f5,axiom,(
% 3.47/0.87    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 3.47/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 3.47/0.87  fof(f65,plain,(
% 3.47/0.87    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.47/0.87    inference(cnf_transformation,[],[f4])).
% 3.47/0.87  fof(f4,axiom,(
% 3.47/0.87    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 3.47/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 3.47/0.87  fof(f51,plain,(
% 3.47/0.87    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.47/0.87    inference(cnf_transformation,[],[f3])).
% 3.47/0.87  fof(f3,axiom,(
% 3.47/0.87    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.47/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 3.47/0.87  fof(f50,plain,(
% 3.47/0.87    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.47/0.87    inference(cnf_transformation,[],[f2])).
% 3.47/0.87  fof(f2,axiom,(
% 3.47/0.87    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.47/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 3.47/0.87  fof(f78,plain,(
% 3.47/0.87    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) | ~v1_relat_1(X2)) )),
% 3.47/0.87    inference(definition_unfolding,[],[f67,f74])).
% 3.47/0.87  fof(f74,plain,(
% 3.47/0.87    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 3.47/0.87    inference(definition_unfolding,[],[f52,f73])).
% 3.47/0.87  fof(f52,plain,(
% 3.47/0.87    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 3.47/0.87    inference(cnf_transformation,[],[f7])).
% 3.47/0.87  fof(f7,axiom,(
% 3.47/0.87    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 3.47/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 3.47/0.87  fof(f67,plain,(
% 3.47/0.87    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 3.47/0.87    inference(cnf_transformation,[],[f37])).
% 3.47/0.87  fof(f37,plain,(
% 3.47/0.87    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 3.47/0.87    inference(ennf_transformation,[],[f12])).
% 3.47/0.87  fof(f12,axiom,(
% 3.47/0.87    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 3.47/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).
% 3.47/0.87  fof(f55,plain,(
% 3.47/0.87    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 3.47/0.87    inference(cnf_transformation,[],[f29])).
% 3.47/0.87  fof(f29,plain,(
% 3.47/0.87    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 3.47/0.87    inference(ennf_transformation,[],[f20])).
% 3.47/0.87  fof(f20,axiom,(
% 3.47/0.87    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 3.47/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).
% 3.47/0.87  fof(f2085,plain,(
% 3.47/0.87    ~r1_tarski(k7_relat_1(k7_relat_1(sK2,sK0),sK1),k7_relat_1(sK2,sK1)) | spl3_31),
% 3.47/0.87    inference(avatar_component_clause,[],[f2083])).
% 3.47/0.87  fof(f2083,plain,(
% 3.47/0.87    spl3_31 <=> r1_tarski(k7_relat_1(k7_relat_1(sK2,sK0),sK1),k7_relat_1(sK2,sK1))),
% 3.47/0.87    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 3.47/0.87  fof(f2086,plain,(
% 3.47/0.87    ~spl3_31 | ~spl3_2 | spl3_22),
% 3.47/0.87    inference(avatar_split_clause,[],[f2081,f1522,f87,f2083])).
% 3.47/0.87  fof(f1522,plain,(
% 3.47/0.87    spl3_22 <=> r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1)),k9_relat_1(sK2,sK1))),
% 3.47/0.87    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 3.47/0.87  fof(f2081,plain,(
% 3.47/0.87    ~r1_tarski(k7_relat_1(k7_relat_1(sK2,sK0),sK1),k7_relat_1(sK2,sK1)) | (~spl3_2 | spl3_22)),
% 3.47/0.87    inference(subsumption_resolution,[],[f2077,f89])).
% 3.47/0.87  fof(f2077,plain,(
% 3.47/0.87    ~r1_tarski(k7_relat_1(k7_relat_1(sK2,sK0),sK1),k7_relat_1(sK2,sK1)) | ~v1_relat_1(sK2) | spl3_22),
% 3.47/0.87    inference(resolution,[],[f1524,f108])).
% 3.47/0.87  fof(f108,plain,(
% 3.47/0.87    ( ! [X2,X0,X1] : (r1_tarski(k2_relat_1(X2),k9_relat_1(X0,X1)) | ~r1_tarski(X2,k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 3.47/0.87    inference(subsumption_resolution,[],[f107,f54])).
% 3.47/0.87  fof(f107,plain,(
% 3.47/0.87    ( ! [X2,X0,X1] : (r1_tarski(k2_relat_1(X2),k9_relat_1(X0,X1)) | ~r1_tarski(X2,k7_relat_1(X0,X1)) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 3.47/0.87    inference(superposition,[],[f103,f56])).
% 3.47/0.87  fof(f56,plain,(
% 3.47/0.87    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.47/0.87    inference(cnf_transformation,[],[f30])).
% 3.47/0.87  fof(f30,plain,(
% 3.47/0.87    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.47/0.87    inference(ennf_transformation,[],[f18])).
% 3.47/0.87  fof(f18,axiom,(
% 3.47/0.87    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 3.47/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 3.47/0.87  fof(f103,plain,(
% 3.47/0.87    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) )),
% 3.47/0.87    inference(subsumption_resolution,[],[f48,f92])).
% 3.47/0.87  fof(f92,plain,(
% 3.47/0.87    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_relat_1(X1) | v1_relat_1(X0)) )),
% 3.47/0.87    inference(resolution,[],[f49,f64])).
% 3.47/0.87  fof(f64,plain,(
% 3.47/0.87    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.47/0.87    inference(cnf_transformation,[],[f44])).
% 3.47/0.87  fof(f44,plain,(
% 3.47/0.87    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.47/0.87    inference(nnf_transformation,[],[f8])).
% 3.47/0.87  fof(f8,axiom,(
% 3.47/0.87    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.47/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 3.47/0.87  fof(f49,plain,(
% 3.47/0.87    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.47/0.87    inference(cnf_transformation,[],[f26])).
% 3.47/0.87  fof(f26,plain,(
% 3.47/0.87    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.47/0.87    inference(ennf_transformation,[],[f9])).
% 3.47/0.87  fof(f9,axiom,(
% 3.47/0.87    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.47/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 3.47/0.87  fof(f48,plain,(
% 3.47/0.87    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.47/0.87    inference(cnf_transformation,[],[f25])).
% 3.47/0.87  fof(f25,plain,(
% 3.47/0.87    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.47/0.87    inference(flattening,[],[f24])).
% 3.47/0.87  fof(f24,plain,(
% 3.47/0.87    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.47/0.87    inference(ennf_transformation,[],[f19])).
% 3.47/0.87  fof(f19,axiom,(
% 3.47/0.87    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 3.47/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).
% 3.47/0.87  fof(f1524,plain,(
% 3.47/0.87    ~r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1)),k9_relat_1(sK2,sK1)) | spl3_22),
% 3.47/0.87    inference(avatar_component_clause,[],[f1522])).
% 3.47/0.87  fof(f1547,plain,(
% 3.47/0.87    ~spl3_2 | spl3_23),
% 3.47/0.87    inference(avatar_contradiction_clause,[],[f1546])).
% 3.47/0.87  fof(f1546,plain,(
% 3.47/0.87    $false | (~spl3_2 | spl3_23)),
% 3.47/0.87    inference(subsumption_resolution,[],[f1541,f89])).
% 3.47/0.87  fof(f1541,plain,(
% 3.47/0.87    ~v1_relat_1(sK2) | spl3_23),
% 3.47/0.87    inference(resolution,[],[f1530,f774])).
% 3.47/0.87  fof(f774,plain,(
% 3.47/0.87    ( ! [X6,X8,X7] : (r1_tarski(k7_relat_1(k7_relat_1(X6,X8),X7),k7_relat_1(X6,X8)) | ~v1_relat_1(X6)) )),
% 3.47/0.87    inference(duplicate_literal_removal,[],[f763])).
% 3.47/0.87  fof(f763,plain,(
% 3.47/0.87    ( ! [X6,X8,X7] : (r1_tarski(k7_relat_1(k7_relat_1(X6,X8),X7),k7_relat_1(X6,X8)) | ~v1_relat_1(X6) | ~v1_relat_1(X6)) )),
% 3.47/0.87    inference(superposition,[],[f696,f458])).
% 3.47/0.87  fof(f1530,plain,(
% 3.47/0.87    ~r1_tarski(k7_relat_1(k7_relat_1(sK2,sK0),sK1),k7_relat_1(sK2,sK0)) | spl3_23),
% 3.47/0.87    inference(avatar_component_clause,[],[f1528])).
% 3.47/0.87  fof(f1528,plain,(
% 3.47/0.87    spl3_23 <=> r1_tarski(k7_relat_1(k7_relat_1(sK2,sK0),sK1),k7_relat_1(sK2,sK0))),
% 3.47/0.87    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 3.47/0.87  fof(f1531,plain,(
% 3.47/0.87    ~spl3_22 | ~spl3_23 | ~spl3_9 | spl3_19),
% 3.47/0.87    inference(avatar_split_clause,[],[f1526,f1467,f953,f1528,f1522])).
% 3.47/0.87  fof(f953,plain,(
% 3.47/0.87    spl3_9 <=> v1_relat_1(k7_relat_1(sK2,sK0))),
% 3.47/0.87    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 3.47/0.87  fof(f1467,plain,(
% 3.47/0.87    spl3_19 <=> r1_tarski(k7_relat_1(k7_relat_1(sK2,sK0),sK1),k8_relat_1(k9_relat_1(sK2,sK1),k7_relat_1(sK2,sK0)))),
% 3.47/0.87    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 3.47/0.87  fof(f1526,plain,(
% 3.47/0.87    ~r1_tarski(k7_relat_1(k7_relat_1(sK2,sK0),sK1),k7_relat_1(sK2,sK0)) | ~r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1)),k9_relat_1(sK2,sK1)) | (~spl3_9 | spl3_19)),
% 3.47/0.87    inference(subsumption_resolution,[],[f1515,f954])).
% 3.47/0.87  fof(f954,plain,(
% 3.47/0.87    v1_relat_1(k7_relat_1(sK2,sK0)) | ~spl3_9),
% 3.47/0.87    inference(avatar_component_clause,[],[f953])).
% 3.47/0.87  fof(f1515,plain,(
% 3.47/0.87    ~r1_tarski(k7_relat_1(k7_relat_1(sK2,sK0),sK1),k7_relat_1(sK2,sK0)) | ~v1_relat_1(k7_relat_1(sK2,sK0)) | ~r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1)),k9_relat_1(sK2,sK1)) | spl3_19),
% 3.47/0.87    inference(resolution,[],[f1469,f132])).
% 3.47/0.87  fof(f132,plain,(
% 3.47/0.87    ( ! [X2,X0,X1] : (r1_tarski(X1,k8_relat_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X1),X0)) )),
% 3.47/0.87    inference(subsumption_resolution,[],[f126,f92])).
% 3.47/0.87  fof(f126,plain,(
% 3.47/0.87    ( ! [X2,X0,X1] : (r1_tarski(X1,k8_relat_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.47/0.87    inference(superposition,[],[f119,f58])).
% 3.47/0.87  fof(f58,plain,(
% 3.47/0.87    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.47/0.87    inference(cnf_transformation,[],[f33])).
% 3.47/0.87  fof(f33,plain,(
% 3.47/0.87    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.47/0.87    inference(flattening,[],[f32])).
% 3.47/0.87  fof(f32,plain,(
% 3.47/0.87    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.47/0.87    inference(ennf_transformation,[],[f15])).
% 3.47/0.87  fof(f15,axiom,(
% 3.47/0.87    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 3.47/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).
% 3.47/0.87  fof(f119,plain,(
% 3.47/0.87    ( ! [X2,X0,X1] : (r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) )),
% 3.47/0.87    inference(subsumption_resolution,[],[f59,f92])).
% 3.47/0.87  fof(f59,plain,(
% 3.47/0.87    ( ! [X2,X0,X1] : (r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 3.47/0.87    inference(cnf_transformation,[],[f35])).
% 3.47/0.87  fof(f35,plain,(
% 3.47/0.87    ! [X0,X1] : (! [X2] : (r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 3.47/0.87    inference(flattening,[],[f34])).
% 3.47/0.87  fof(f34,plain,(
% 3.47/0.87    ! [X0,X1] : (! [X2] : ((r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 3.47/0.87    inference(ennf_transformation,[],[f16])).
% 3.47/0.87  fof(f16,axiom,(
% 3.47/0.87    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)))))),
% 3.47/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_relat_1)).
% 3.47/0.87  fof(f1469,plain,(
% 3.47/0.87    ~r1_tarski(k7_relat_1(k7_relat_1(sK2,sK0),sK1),k8_relat_1(k9_relat_1(sK2,sK1),k7_relat_1(sK2,sK0))) | spl3_19),
% 3.47/0.87    inference(avatar_component_clause,[],[f1467])).
% 3.47/0.87  fof(f1470,plain,(
% 3.47/0.87    ~spl3_19 | ~spl3_5 | spl3_7),
% 3.47/0.87    inference(avatar_split_clause,[],[f1465,f942,f932,f1467])).
% 3.47/0.87  fof(f932,plain,(
% 3.47/0.87    spl3_5 <=> v1_relat_1(k8_relat_1(k9_relat_1(sK2,sK1),k7_relat_1(sK2,sK0)))),
% 3.47/0.87    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 3.47/0.87  fof(f942,plain,(
% 3.47/0.87    spl3_7 <=> r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1)),k2_relat_1(k8_relat_1(k9_relat_1(sK2,sK1),k7_relat_1(sK2,sK0))))),
% 3.47/0.87    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 3.47/0.87  fof(f1465,plain,(
% 3.47/0.87    ~r1_tarski(k7_relat_1(k7_relat_1(sK2,sK0),sK1),k8_relat_1(k9_relat_1(sK2,sK1),k7_relat_1(sK2,sK0))) | (~spl3_5 | spl3_7)),
% 3.47/0.87    inference(subsumption_resolution,[],[f1455,f933])).
% 3.47/0.87  fof(f933,plain,(
% 3.47/0.87    v1_relat_1(k8_relat_1(k9_relat_1(sK2,sK1),k7_relat_1(sK2,sK0))) | ~spl3_5),
% 3.47/0.87    inference(avatar_component_clause,[],[f932])).
% 3.47/0.87  fof(f1455,plain,(
% 3.47/0.87    ~r1_tarski(k7_relat_1(k7_relat_1(sK2,sK0),sK1),k8_relat_1(k9_relat_1(sK2,sK1),k7_relat_1(sK2,sK0))) | ~v1_relat_1(k8_relat_1(k9_relat_1(sK2,sK1),k7_relat_1(sK2,sK0))) | spl3_7),
% 3.47/0.87    inference(resolution,[],[f944,f103])).
% 3.47/0.87  fof(f944,plain,(
% 3.47/0.87    ~r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1)),k2_relat_1(k8_relat_1(k9_relat_1(sK2,sK1),k7_relat_1(sK2,sK0)))) | spl3_7),
% 3.47/0.87    inference(avatar_component_clause,[],[f942])).
% 3.47/0.87  fof(f1078,plain,(
% 3.47/0.87    ~spl3_7 | ~spl3_2 | spl3_3),
% 3.47/0.87    inference(avatar_split_clause,[],[f1077,f568,f87,f942])).
% 3.47/0.87  fof(f568,plain,(
% 3.47/0.87    spl3_3 <=> r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1)),k1_setfam_1(k4_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))))),
% 3.47/0.87    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 3.47/0.87  fof(f1077,plain,(
% 3.47/0.87    ~r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1)),k2_relat_1(k8_relat_1(k9_relat_1(sK2,sK1),k7_relat_1(sK2,sK0)))) | (~spl3_2 | spl3_3)),
% 3.47/0.87    inference(subsumption_resolution,[],[f1062,f89])).
% 3.47/0.87  fof(f1062,plain,(
% 3.47/0.87    ~r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1)),k2_relat_1(k8_relat_1(k9_relat_1(sK2,sK1),k7_relat_1(sK2,sK0)))) | ~v1_relat_1(sK2) | spl3_3),
% 3.47/0.87    inference(superposition,[],[f570,f174])).
% 3.47/0.87  fof(f174,plain,(
% 3.47/0.87    ( ! [X2,X0,X1] : (k2_relat_1(k8_relat_1(X2,k7_relat_1(X0,X1))) = k1_setfam_1(k4_enumset1(k9_relat_1(X0,X1),k9_relat_1(X0,X1),k9_relat_1(X0,X1),k9_relat_1(X0,X1),k9_relat_1(X0,X1),X2)) | ~v1_relat_1(X0)) )),
% 3.47/0.87    inference(subsumption_resolution,[],[f170,f54])).
% 3.47/0.87  fof(f170,plain,(
% 3.47/0.87    ( ! [X2,X0,X1] : (k2_relat_1(k8_relat_1(X2,k7_relat_1(X0,X1))) = k1_setfam_1(k4_enumset1(k9_relat_1(X0,X1),k9_relat_1(X0,X1),k9_relat_1(X0,X1),k9_relat_1(X0,X1),k9_relat_1(X0,X1),X2)) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 3.47/0.87    inference(superposition,[],[f77,f56])).
% 3.47/0.87  fof(f77,plain,(
% 3.47/0.87    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k1_setfam_1(k4_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 3.47/0.87    inference(definition_unfolding,[],[f57,f74])).
% 3.47/0.87  fof(f57,plain,(
% 3.47/0.87    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.47/0.87    inference(cnf_transformation,[],[f31])).
% 3.47/0.87  fof(f31,plain,(
% 3.47/0.87    ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.47/0.87    inference(ennf_transformation,[],[f14])).
% 3.47/0.87  fof(f14,axiom,(
% 3.47/0.87    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0))),
% 3.47/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).
% 3.47/0.87  fof(f570,plain,(
% 3.47/0.87    ~r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1)),k1_setfam_1(k4_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))) | spl3_3),
% 3.47/0.87    inference(avatar_component_clause,[],[f568])).
% 3.47/0.87  fof(f1054,plain,(
% 3.47/0.87    ~spl3_2 | spl3_5),
% 3.47/0.87    inference(avatar_contradiction_clause,[],[f1053])).
% 3.47/0.87  fof(f1053,plain,(
% 3.47/0.87    $false | (~spl3_2 | spl3_5)),
% 3.47/0.87    inference(subsumption_resolution,[],[f1043,f89])).
% 3.47/0.87  fof(f1043,plain,(
% 3.47/0.87    ~v1_relat_1(sK2) | spl3_5),
% 3.47/0.87    inference(resolution,[],[f934,f247])).
% 3.47/0.87  fof(f247,plain,(
% 3.47/0.87    ( ! [X12,X10,X11] : (v1_relat_1(k8_relat_1(X11,k7_relat_1(X10,X12))) | ~v1_relat_1(X10)) )),
% 3.47/0.87    inference(resolution,[],[f242,f79])).
% 3.47/0.87  fof(f79,plain,(
% 3.47/0.87    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.47/0.87    inference(equality_resolution,[],[f61])).
% 3.47/0.87  fof(f61,plain,(
% 3.47/0.87    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.47/0.87    inference(cnf_transformation,[],[f43])).
% 3.47/0.87  fof(f43,plain,(
% 3.47/0.87    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.47/0.87    inference(flattening,[],[f42])).
% 3.47/0.87  fof(f42,plain,(
% 3.47/0.87    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.47/0.87    inference(nnf_transformation,[],[f1])).
% 3.47/0.87  fof(f1,axiom,(
% 3.47/0.87    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.47/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.47/0.87  fof(f242,plain,(
% 3.47/0.87    ( ! [X6,X4,X5,X3] : (~r1_tarski(X3,k7_relat_1(X4,X5)) | ~v1_relat_1(X4) | v1_relat_1(k8_relat_1(X6,X3))) )),
% 3.47/0.87    inference(subsumption_resolution,[],[f233,f114])).
% 3.47/0.87  fof(f114,plain,(
% 3.47/0.87    ( ! [X4,X5,X3] : (v1_relat_1(k7_relat_1(k8_relat_1(X3,X4),X5)) | ~v1_relat_1(X4)) )),
% 3.47/0.87    inference(subsumption_resolution,[],[f111,f54])).
% 3.47/0.87  fof(f111,plain,(
% 3.47/0.87    ( ! [X4,X5,X3] : (v1_relat_1(k7_relat_1(k8_relat_1(X3,X4),X5)) | ~v1_relat_1(k7_relat_1(X4,X5)) | ~v1_relat_1(X4)) )),
% 3.47/0.87    inference(superposition,[],[f53,f66])).
% 3.47/0.87  fof(f66,plain,(
% 3.47/0.87    ( ! [X2,X0,X1] : (k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.47/0.87    inference(cnf_transformation,[],[f36])).
% 3.47/0.87  fof(f36,plain,(
% 3.47/0.87    ! [X0,X1,X2] : (k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 3.47/0.87    inference(ennf_transformation,[],[f17])).
% 3.47/0.87  fof(f17,axiom,(
% 3.47/0.87    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)))),
% 3.47/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_relat_1)).
% 3.47/0.87  fof(f53,plain,(
% 3.47/0.87    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 3.47/0.87    inference(cnf_transformation,[],[f27])).
% 3.47/0.87  fof(f27,plain,(
% 3.47/0.87    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 3.47/0.87    inference(ennf_transformation,[],[f11])).
% 3.47/0.87  fof(f11,axiom,(
% 3.47/0.87    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 3.47/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 3.47/0.87  fof(f233,plain,(
% 3.47/0.87    ( ! [X6,X4,X5,X3] : (~r1_tarski(X3,k7_relat_1(X4,X5)) | ~v1_relat_1(X4) | ~v1_relat_1(k7_relat_1(k8_relat_1(X6,X4),X5)) | v1_relat_1(k8_relat_1(X6,X3))) )),
% 3.47/0.87    inference(resolution,[],[f133,f92])).
% 3.47/0.87  fof(f133,plain,(
% 3.47/0.87    ( ! [X6,X4,X5,X3] : (r1_tarski(k8_relat_1(X3,X6),k7_relat_1(k8_relat_1(X3,X4),X5)) | ~r1_tarski(X6,k7_relat_1(X4,X5)) | ~v1_relat_1(X4)) )),
% 3.47/0.87    inference(subsumption_resolution,[],[f129,f54])).
% 3.47/0.87  fof(f129,plain,(
% 3.47/0.87    ( ! [X6,X4,X5,X3] : (r1_tarski(k8_relat_1(X3,X6),k7_relat_1(k8_relat_1(X3,X4),X5)) | ~r1_tarski(X6,k7_relat_1(X4,X5)) | ~v1_relat_1(k7_relat_1(X4,X5)) | ~v1_relat_1(X4)) )),
% 3.47/0.87    inference(superposition,[],[f119,f66])).
% 3.47/0.87  fof(f934,plain,(
% 3.47/0.87    ~v1_relat_1(k8_relat_1(k9_relat_1(sK2,sK1),k7_relat_1(sK2,sK0))) | spl3_5),
% 3.47/0.87    inference(avatar_component_clause,[],[f932])).
% 3.47/0.87  fof(f1002,plain,(
% 3.47/0.87    ~spl3_2 | spl3_9),
% 3.47/0.87    inference(avatar_contradiction_clause,[],[f1001])).
% 3.47/0.87  fof(f1001,plain,(
% 3.47/0.87    $false | (~spl3_2 | spl3_9)),
% 3.47/0.87    inference(subsumption_resolution,[],[f998,f89])).
% 3.47/0.87  fof(f998,plain,(
% 3.47/0.87    ~v1_relat_1(sK2) | spl3_9),
% 3.47/0.87    inference(resolution,[],[f955,f54])).
% 3.47/0.87  fof(f955,plain,(
% 3.47/0.87    ~v1_relat_1(k7_relat_1(sK2,sK0)) | spl3_9),
% 3.47/0.87    inference(avatar_component_clause,[],[f953])).
% 3.47/0.87  fof(f571,plain,(
% 3.47/0.87    ~spl3_3 | spl3_1 | ~spl3_2),
% 3.47/0.87    inference(avatar_split_clause,[],[f566,f87,f82,f568])).
% 3.47/0.87  fof(f82,plain,(
% 3.47/0.87    spl3_1 <=> r1_tarski(k9_relat_1(sK2,k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k1_setfam_1(k4_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))))),
% 3.47/0.87    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 3.47/0.87  fof(f566,plain,(
% 3.47/0.87    ~r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1)),k1_setfam_1(k4_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))) | (spl3_1 | ~spl3_2)),
% 3.47/0.87    inference(subsumption_resolution,[],[f561,f89])).
% 3.47/0.87  fof(f561,plain,(
% 3.47/0.87    ~r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK2,sK0),sK1)),k1_setfam_1(k4_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))) | ~v1_relat_1(sK2) | spl3_1),
% 3.47/0.87    inference(superposition,[],[f84,f160])).
% 3.47/0.87  fof(f160,plain,(
% 3.47/0.87    ( ! [X6,X8,X7] : (k9_relat_1(X6,k1_setfam_1(k4_enumset1(X7,X7,X7,X7,X7,X8))) = k2_relat_1(k7_relat_1(k7_relat_1(X6,X7),X8)) | ~v1_relat_1(X6)) )),
% 3.47/0.87    inference(duplicate_literal_removal,[],[f148])).
% 3.47/0.87  fof(f148,plain,(
% 3.47/0.87    ( ! [X6,X8,X7] : (k9_relat_1(X6,k1_setfam_1(k4_enumset1(X7,X7,X7,X7,X7,X8))) = k2_relat_1(k7_relat_1(k7_relat_1(X6,X7),X8)) | ~v1_relat_1(X6) | ~v1_relat_1(X6)) )),
% 3.47/0.87    inference(superposition,[],[f56,f78])).
% 3.47/0.87  fof(f84,plain,(
% 3.47/0.87    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k1_setfam_1(k4_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))) | spl3_1),
% 3.47/0.87    inference(avatar_component_clause,[],[f82])).
% 3.47/0.87  fof(f90,plain,(
% 3.47/0.87    spl3_2),
% 3.47/0.87    inference(avatar_split_clause,[],[f45,f87])).
% 3.47/0.87  fof(f45,plain,(
% 3.47/0.87    v1_relat_1(sK2)),
% 3.47/0.87    inference(cnf_transformation,[],[f41])).
% 3.47/0.87  fof(f41,plain,(
% 3.47/0.87    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) & v1_relat_1(sK2)),
% 3.47/0.87    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f40])).
% 3.47/0.87  fof(f40,plain,(
% 3.47/0.87    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) & v1_relat_1(X2)) => (~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) & v1_relat_1(sK2))),
% 3.47/0.87    introduced(choice_axiom,[])).
% 3.47/0.87  fof(f23,plain,(
% 3.47/0.87    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) & v1_relat_1(X2))),
% 3.47/0.87    inference(ennf_transformation,[],[f22])).
% 3.47/0.87  fof(f22,negated_conjecture,(
% 3.47/0.87    ~! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 3.47/0.87    inference(negated_conjecture,[],[f21])).
% 3.47/0.88  fof(f21,conjecture,(
% 3.47/0.88    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 3.47/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_relat_1)).
% 3.47/0.88  fof(f85,plain,(
% 3.47/0.88    ~spl3_1),
% 3.47/0.88    inference(avatar_split_clause,[],[f75,f82])).
% 3.47/0.88  fof(f75,plain,(
% 3.47/0.88    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k1_setfam_1(k4_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))))),
% 3.47/0.88    inference(definition_unfolding,[],[f46,f74,f74])).
% 3.47/0.88  fof(f46,plain,(
% 3.47/0.88    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))),
% 3.47/0.88    inference(cnf_transformation,[],[f41])).
% 3.47/0.88  % SZS output end Proof for theBenchmark
% 3.47/0.88  % (4225)------------------------------
% 3.47/0.88  % (4225)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.47/0.88  % (4225)Termination reason: Refutation
% 3.47/0.88  
% 3.47/0.88  % (4225)Memory used [KB]: 12920
% 3.47/0.88  % (4225)Time elapsed: 0.300 s
% 3.47/0.88  % (4225)------------------------------
% 3.47/0.88  % (4225)------------------------------
% 3.47/0.88  % (4193)Success in time 0.525 s
%------------------------------------------------------------------------------
