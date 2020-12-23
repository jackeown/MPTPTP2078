%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:23 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 185 expanded)
%              Number of leaves         :   28 (  62 expanded)
%              Depth                    :   15
%              Number of atoms          :  255 ( 400 expanded)
%              Number of equality atoms :  101 ( 173 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f856,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f91,f108,f182,f232,f354,f855])).

fof(f855,plain,
    ( spl2_1
    | ~ spl2_2
    | spl2_6
    | ~ spl2_9
    | ~ spl2_10 ),
    inference(avatar_contradiction_clause,[],[f854])).

fof(f854,plain,
    ( $false
    | spl2_1
    | ~ spl2_2
    | spl2_6
    | ~ spl2_9
    | ~ spl2_10 ),
    inference(subsumption_resolution,[],[f853,f181])).

fof(f181,plain,
    ( k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k8_setfam_1(sK0,sK1))
    | spl2_6 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl2_6
  <=> k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = k3_subset_1(sK0,k8_setfam_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f853,plain,
    ( k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = k3_subset_1(sK0,k8_setfam_1(sK0,sK1))
    | spl2_1
    | ~ spl2_2
    | ~ spl2_9
    | ~ spl2_10 ),
    inference(forward_demodulation,[],[f848,f336])).

fof(f336,plain,
    ( k8_setfam_1(sK0,sK1) = k3_subset_1(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)))
    | spl2_1
    | ~ spl2_2
    | ~ spl2_9 ),
    inference(forward_demodulation,[],[f335,f279])).

fof(f279,plain,
    ( k8_setfam_1(sK0,sK1) = k4_subset_1(sK0,k1_xboole_0,k8_setfam_1(sK0,sK1))
    | ~ spl2_9 ),
    inference(forward_demodulation,[],[f268,f109])).

fof(f109,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(unit_resulting_resolution,[],[f48,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f48,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f268,plain,
    ( k4_subset_1(sK0,k1_xboole_0,k8_setfam_1(sK0,sK1)) = k2_xboole_0(k1_xboole_0,k8_setfam_1(sK0,sK1))
    | ~ spl2_9 ),
    inference(unit_resulting_resolution,[],[f50,f231,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f231,plain,
    ( m1_subset_1(k8_setfam_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f229])).

fof(f229,plain,
    ( spl2_9
  <=> m1_subset_1(k8_setfam_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f50,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f335,plain,
    ( k4_subset_1(sK0,k1_xboole_0,k8_setfam_1(sK0,sK1)) = k3_subset_1(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)))
    | spl2_1
    | ~ spl2_2
    | ~ spl2_9 ),
    inference(forward_demodulation,[],[f334,f203])).

fof(f203,plain,
    ( k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = k7_subset_1(sK0,sK0,k8_setfam_1(sK0,sK1))
    | spl2_1
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f196,f169])).

fof(f169,plain,
    ( k6_setfam_1(sK0,sK1) = k8_setfam_1(sK0,sK1)
    | spl2_1
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f85,f90,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 = X1
      | k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

fof(f90,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl2_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f85,plain,
    ( k1_xboole_0 != sK1
    | spl2_1 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl2_1
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f196,plain,
    ( k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = k7_subset_1(sK0,sK0,k6_setfam_1(sK0,sK1))
    | spl2_1
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f85,f90,f166])).

fof(f166,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 = X1
      | k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k7_subset_1(X0,X0,k6_setfam_1(X0,X1)) ) ),
    inference(backward_demodulation,[],[f77,f164])).

fof(f164,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f163,f52])).

fof(f52,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f163,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f156,f75])).

fof(f75,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f51,f54])).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f51,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f156,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) ),
    inference(unit_resulting_resolution,[],[f50,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(definition_unfolding,[],[f57,f73])).

fof(f73,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f55,f54])).

fof(f55,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f57,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f77,plain,(
    ! [X0,X1] :
      ( k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k7_subset_1(X0,k3_subset_1(X0,k1_xboole_0),k6_setfam_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(definition_unfolding,[],[f65,f74])).

fof(f74,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f53,f49])).

fof(f49,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(f53,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

fof(f65,plain,(
    ! [X0,X1] :
      ( k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k7_subset_1(X0,k2_subset_1(X0),k6_setfam_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k7_subset_1(X0,k2_subset_1(X0),k6_setfam_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k7_subset_1(X0,k2_subset_1(X0),k6_setfam_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( k1_xboole_0 != X1
       => k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k7_subset_1(X0,k2_subset_1(X0),k6_setfam_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_setfam_1)).

fof(f334,plain,
    ( k4_subset_1(sK0,k1_xboole_0,k8_setfam_1(sK0,sK1)) = k3_subset_1(sK0,k7_subset_1(sK0,sK0,k8_setfam_1(sK0,sK1)))
    | ~ spl2_9 ),
    inference(forward_demodulation,[],[f285,f165])).

fof(f165,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    inference(backward_demodulation,[],[f129,f164])).

fof(f129,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f50,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f285,plain,
    ( k3_subset_1(sK0,k7_subset_1(sK0,sK0,k8_setfam_1(sK0,sK1))) = k4_subset_1(sK0,k3_subset_1(sK0,sK0),k8_setfam_1(sK0,sK1))
    | ~ spl2_9 ),
    inference(unit_resulting_resolution,[],[f231,f102,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_subset_1)).

fof(f102,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f79,f70])).

fof(f70,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f79,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
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

fof(f848,plain,
    ( k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = k3_subset_1(sK0,k3_subset_1(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1))))
    | ~ spl2_10 ),
    inference(resolution,[],[f135,f353])).

fof(f353,plain,
    ( m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f351])).

fof(f351,plain,
    ( spl2_10
  <=> m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f135,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | k5_setfam_1(X1,X0) = k3_subset_1(X1,k3_subset_1(X1,k5_setfam_1(X1,X0))) ) ),
    inference(resolution,[],[f60,f58])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_setfam_1)).

fof(f354,plain,
    ( spl2_10
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f150,f88,f351])).

fof(f150,plain,
    ( m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f90,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(f232,plain,
    ( spl2_9
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f143,f88,f229])).

fof(f143,plain,
    ( m1_subset_1(k8_setfam_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f90,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).

fof(f182,plain,
    ( ~ spl2_6
    | spl2_1
    | ~ spl2_2
    | spl2_4 ),
    inference(avatar_split_clause,[],[f176,f105,f88,f83,f179])).

fof(f105,plain,
    ( spl2_4
  <=> k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = k3_subset_1(sK0,k6_setfam_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f176,plain,
    ( k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k8_setfam_1(sK0,sK1))
    | spl2_1
    | ~ spl2_2
    | spl2_4 ),
    inference(backward_demodulation,[],[f107,f169])).

fof(f107,plain,
    ( k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k6_setfam_1(sK0,sK1))
    | spl2_4 ),
    inference(avatar_component_clause,[],[f105])).

fof(f108,plain,(
    ~ spl2_4 ),
    inference(avatar_split_clause,[],[f47,f105])).

fof(f47,plain,(
    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k6_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k6_setfam_1(sK0,sK1))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f40])).

fof(f40,plain,
    ( ? [X0,X1] :
        ( k5_setfam_1(X0,k7_setfam_1(X0,X1)) != k3_subset_1(X0,k6_setfam_1(X0,X1))
        & k1_xboole_0 != X1
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k6_setfam_1(sK0,sK1))
      & k1_xboole_0 != sK1
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1] :
      ( k5_setfam_1(X0,k7_setfam_1(X0,X1)) != k3_subset_1(X0,k6_setfam_1(X0,X1))
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1] :
      ( k5_setfam_1(X0,k7_setfam_1(X0,X1)) != k3_subset_1(X0,k6_setfam_1(X0,X1))
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ( k1_xboole_0 != X1
         => k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k6_setfam_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( k1_xboole_0 != X1
       => k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k6_setfam_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_tops_2)).

fof(f91,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f45,f88])).

fof(f45,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f86,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f46,f83])).

fof(f46,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:07:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (26844)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.51  % (26846)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.51  % (26827)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (26834)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.52  % (26828)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (26831)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.52  % (26824)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.52  % (26825)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.53  % (26843)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.53  % (26845)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.53  % (26833)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.53  % (26841)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.53  % (26838)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.53  % (26826)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.53  % (26833)Refutation not found, incomplete strategy% (26833)------------------------------
% 0.22/0.53  % (26833)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (26833)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (26833)Memory used [KB]: 10746
% 0.22/0.53  % (26833)Time elapsed: 0.131 s
% 0.22/0.53  % (26833)------------------------------
% 0.22/0.53  % (26833)------------------------------
% 0.22/0.53  % (26832)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.53  % (26823)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (26830)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.54  % (26837)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.54  % (26850)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (26847)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.54  % (26854)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % (26854)Refutation not found, incomplete strategy% (26854)------------------------------
% 0.22/0.54  % (26854)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (26854)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (26854)Memory used [KB]: 1663
% 0.22/0.54  % (26854)Time elapsed: 0.140 s
% 0.22/0.54  % (26854)------------------------------
% 0.22/0.54  % (26854)------------------------------
% 0.22/0.54  % (26842)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.54  % (26836)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.55  % (26852)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.55  % (26853)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.55  % (26853)Refutation not found, incomplete strategy% (26853)------------------------------
% 0.22/0.55  % (26853)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (26853)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (26853)Memory used [KB]: 10746
% 0.22/0.55  % (26853)Time elapsed: 0.151 s
% 0.22/0.55  % (26853)------------------------------
% 0.22/0.55  % (26853)------------------------------
% 1.51/0.56  % (26839)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.51/0.56  % (26822)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.51/0.56  % (26840)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.51/0.56  % (26849)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.51/0.56  % (26844)Refutation found. Thanks to Tanya!
% 1.51/0.56  % SZS status Theorem for theBenchmark
% 1.51/0.56  % (26840)Refutation not found, incomplete strategy% (26840)------------------------------
% 1.51/0.56  % (26840)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.56  % (26840)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.56  
% 1.51/0.56  % (26840)Memory used [KB]: 10618
% 1.51/0.56  % (26840)Time elapsed: 0.162 s
% 1.51/0.56  % (26840)------------------------------
% 1.51/0.56  % (26840)------------------------------
% 1.51/0.57  % (26848)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.51/0.57  % SZS output start Proof for theBenchmark
% 1.51/0.57  fof(f856,plain,(
% 1.51/0.57    $false),
% 1.51/0.57    inference(avatar_sat_refutation,[],[f86,f91,f108,f182,f232,f354,f855])).
% 1.51/0.57  fof(f855,plain,(
% 1.51/0.57    spl2_1 | ~spl2_2 | spl2_6 | ~spl2_9 | ~spl2_10),
% 1.51/0.57    inference(avatar_contradiction_clause,[],[f854])).
% 1.51/0.57  fof(f854,plain,(
% 1.51/0.57    $false | (spl2_1 | ~spl2_2 | spl2_6 | ~spl2_9 | ~spl2_10)),
% 1.51/0.57    inference(subsumption_resolution,[],[f853,f181])).
% 1.51/0.57  fof(f181,plain,(
% 1.51/0.57    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k8_setfam_1(sK0,sK1)) | spl2_6),
% 1.51/0.57    inference(avatar_component_clause,[],[f179])).
% 1.51/0.57  fof(f179,plain,(
% 1.51/0.57    spl2_6 <=> k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = k3_subset_1(sK0,k8_setfam_1(sK0,sK1))),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 1.51/0.57  fof(f853,plain,(
% 1.51/0.57    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = k3_subset_1(sK0,k8_setfam_1(sK0,sK1)) | (spl2_1 | ~spl2_2 | ~spl2_9 | ~spl2_10)),
% 1.51/0.57    inference(forward_demodulation,[],[f848,f336])).
% 1.51/0.57  fof(f336,plain,(
% 1.51/0.57    k8_setfam_1(sK0,sK1) = k3_subset_1(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1))) | (spl2_1 | ~spl2_2 | ~spl2_9)),
% 1.51/0.57    inference(forward_demodulation,[],[f335,f279])).
% 1.51/0.57  fof(f279,plain,(
% 1.51/0.57    k8_setfam_1(sK0,sK1) = k4_subset_1(sK0,k1_xboole_0,k8_setfam_1(sK0,sK1)) | ~spl2_9),
% 1.51/0.57    inference(forward_demodulation,[],[f268,f109])).
% 1.51/0.57  fof(f109,plain,(
% 1.51/0.57    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.51/0.57    inference(unit_resulting_resolution,[],[f48,f56])).
% 1.51/0.57  fof(f56,plain,(
% 1.51/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.51/0.57    inference(cnf_transformation,[],[f26])).
% 1.51/0.57  fof(f26,plain,(
% 1.51/0.57    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.51/0.57    inference(ennf_transformation,[],[f3])).
% 1.65/0.58  fof(f3,axiom,(
% 1.65/0.58    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.65/0.58  fof(f48,plain,(
% 1.65/0.58    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f5])).
% 1.65/0.58  fof(f5,axiom,(
% 1.65/0.58    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.65/0.58  fof(f268,plain,(
% 1.65/0.58    k4_subset_1(sK0,k1_xboole_0,k8_setfam_1(sK0,sK1)) = k2_xboole_0(k1_xboole_0,k8_setfam_1(sK0,sK1)) | ~spl2_9),
% 1.65/0.58    inference(unit_resulting_resolution,[],[f50,f231,f72])).
% 1.65/0.58  fof(f72,plain,(
% 1.65/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.65/0.58    inference(cnf_transformation,[],[f39])).
% 1.65/0.58  fof(f39,plain,(
% 1.65/0.58    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.65/0.58    inference(flattening,[],[f38])).
% 1.65/0.58  fof(f38,plain,(
% 1.65/0.58    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.65/0.58    inference(ennf_transformation,[],[f10])).
% 1.65/0.58  fof(f10,axiom,(
% 1.65/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.65/0.58  fof(f231,plain,(
% 1.65/0.58    m1_subset_1(k8_setfam_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl2_9),
% 1.65/0.58    inference(avatar_component_clause,[],[f229])).
% 1.65/0.58  fof(f229,plain,(
% 1.65/0.58    spl2_9 <=> m1_subset_1(k8_setfam_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 1.65/0.58  fof(f50,plain,(
% 1.65/0.58    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.65/0.58    inference(cnf_transformation,[],[f13])).
% 1.65/0.58  fof(f13,axiom,(
% 1.65/0.58    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.65/0.58  fof(f335,plain,(
% 1.65/0.58    k4_subset_1(sK0,k1_xboole_0,k8_setfam_1(sK0,sK1)) = k3_subset_1(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1))) | (spl2_1 | ~spl2_2 | ~spl2_9)),
% 1.65/0.58    inference(forward_demodulation,[],[f334,f203])).
% 1.65/0.58  fof(f203,plain,(
% 1.65/0.58    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = k7_subset_1(sK0,sK0,k8_setfam_1(sK0,sK1)) | (spl2_1 | ~spl2_2)),
% 1.65/0.58    inference(forward_demodulation,[],[f196,f169])).
% 1.65/0.58  fof(f169,plain,(
% 1.65/0.58    k6_setfam_1(sK0,sK1) = k8_setfam_1(sK0,sK1) | (spl2_1 | ~spl2_2)),
% 1.65/0.58    inference(unit_resulting_resolution,[],[f85,f90,f63])).
% 1.65/0.58  fof(f63,plain,(
% 1.65/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 = X1 | k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f33])).
% 1.65/0.58  fof(f33,plain,(
% 1.65/0.58    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.65/0.58    inference(ennf_transformation,[],[f14])).
% 1.65/0.58  fof(f14,axiom,(
% 1.65/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).
% 1.65/0.58  fof(f90,plain,(
% 1.65/0.58    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl2_2),
% 1.65/0.58    inference(avatar_component_clause,[],[f88])).
% 1.65/0.58  fof(f88,plain,(
% 1.65/0.58    spl2_2 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.65/0.58  fof(f85,plain,(
% 1.65/0.58    k1_xboole_0 != sK1 | spl2_1),
% 1.65/0.58    inference(avatar_component_clause,[],[f83])).
% 1.65/0.58  fof(f83,plain,(
% 1.65/0.58    spl2_1 <=> k1_xboole_0 = sK1),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.65/0.58  fof(f196,plain,(
% 1.65/0.58    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = k7_subset_1(sK0,sK0,k6_setfam_1(sK0,sK1)) | (spl2_1 | ~spl2_2)),
% 1.65/0.58    inference(unit_resulting_resolution,[],[f85,f90,f166])).
% 1.65/0.58  fof(f166,plain,(
% 1.65/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 = X1 | k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k7_subset_1(X0,X0,k6_setfam_1(X0,X1))) )),
% 1.65/0.58    inference(backward_demodulation,[],[f77,f164])).
% 1.65/0.58  fof(f164,plain,(
% 1.65/0.58    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 1.65/0.58    inference(forward_demodulation,[],[f163,f52])).
% 1.65/0.58  fof(f52,plain,(
% 1.65/0.58    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.65/0.58    inference(cnf_transformation,[],[f6])).
% 1.65/0.58  fof(f6,axiom,(
% 1.65/0.58    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.65/0.58  fof(f163,plain,(
% 1.65/0.58    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0)) )),
% 1.65/0.58    inference(forward_demodulation,[],[f156,f75])).
% 1.65/0.58  fof(f75,plain,(
% 1.65/0.58    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) )),
% 1.65/0.58    inference(definition_unfolding,[],[f51,f54])).
% 1.65/0.58  fof(f54,plain,(
% 1.65/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.65/0.58    inference(cnf_transformation,[],[f18])).
% 1.65/0.58  fof(f18,axiom,(
% 1.65/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.65/0.58  fof(f51,plain,(
% 1.65/0.58    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f4])).
% 1.65/0.58  fof(f4,axiom,(
% 1.65/0.58    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.65/0.58  fof(f156,plain,(
% 1.65/0.58    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0)))) )),
% 1.65/0.58    inference(unit_resulting_resolution,[],[f50,f76])).
% 1.65/0.58  fof(f76,plain,(
% 1.65/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 1.65/0.58    inference(definition_unfolding,[],[f57,f73])).
% 1.65/0.58  fof(f73,plain,(
% 1.65/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 1.65/0.58    inference(definition_unfolding,[],[f55,f54])).
% 1.65/0.58  fof(f55,plain,(
% 1.65/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.65/0.58    inference(cnf_transformation,[],[f2])).
% 1.65/0.58  fof(f2,axiom,(
% 1.65/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.65/0.58  fof(f57,plain,(
% 1.65/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.65/0.58    inference(cnf_transformation,[],[f27])).
% 1.65/0.58  fof(f27,plain,(
% 1.65/0.58    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.65/0.58    inference(ennf_transformation,[],[f8])).
% 1.65/0.58  fof(f8,axiom,(
% 1.65/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.65/0.58  fof(f77,plain,(
% 1.65/0.58    ( ! [X0,X1] : (k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k7_subset_1(X0,k3_subset_1(X0,k1_xboole_0),k6_setfam_1(X0,X1)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.65/0.58    inference(definition_unfolding,[],[f65,f74])).
% 1.65/0.58  fof(f74,plain,(
% 1.65/0.58    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 1.65/0.58    inference(definition_unfolding,[],[f53,f49])).
% 1.65/0.58  fof(f49,plain,(
% 1.65/0.58    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f7])).
% 1.65/0.58  fof(f7,axiom,(
% 1.65/0.58    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).
% 1.65/0.58  fof(f53,plain,(
% 1.65/0.58    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 1.65/0.58    inference(cnf_transformation,[],[f11])).
% 1.65/0.58  fof(f11,axiom,(
% 1.65/0.58    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).
% 1.65/0.58  fof(f65,plain,(
% 1.65/0.58    ( ! [X0,X1] : (k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k7_subset_1(X0,k2_subset_1(X0),k6_setfam_1(X0,X1)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.65/0.58    inference(cnf_transformation,[],[f35])).
% 1.65/0.58  fof(f35,plain,(
% 1.65/0.58    ! [X0,X1] : (k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k7_subset_1(X0,k2_subset_1(X0),k6_setfam_1(X0,X1)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.65/0.58    inference(flattening,[],[f34])).
% 1.65/0.58  fof(f34,plain,(
% 1.65/0.58    ! [X0,X1] : ((k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k7_subset_1(X0,k2_subset_1(X0),k6_setfam_1(X0,X1)) | k1_xboole_0 = X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.65/0.58    inference(ennf_transformation,[],[f20])).
% 1.65/0.58  fof(f20,axiom,(
% 1.65/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k1_xboole_0 != X1 => k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k7_subset_1(X0,k2_subset_1(X0),k6_setfam_1(X0,X1))))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_setfam_1)).
% 1.65/0.58  fof(f334,plain,(
% 1.65/0.58    k4_subset_1(sK0,k1_xboole_0,k8_setfam_1(sK0,sK1)) = k3_subset_1(sK0,k7_subset_1(sK0,sK0,k8_setfam_1(sK0,sK1))) | ~spl2_9),
% 1.65/0.58    inference(forward_demodulation,[],[f285,f165])).
% 1.65/0.58  fof(f165,plain,(
% 1.65/0.58    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0)) )),
% 1.65/0.58    inference(backward_demodulation,[],[f129,f164])).
% 1.65/0.58  fof(f129,plain,(
% 1.65/0.58    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0))) )),
% 1.65/0.58    inference(unit_resulting_resolution,[],[f50,f58])).
% 1.65/0.58  fof(f58,plain,(
% 1.65/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 1.65/0.58    inference(cnf_transformation,[],[f28])).
% 1.65/0.58  fof(f28,plain,(
% 1.65/0.58    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.65/0.58    inference(ennf_transformation,[],[f9])).
% 1.65/0.58  fof(f9,axiom,(
% 1.65/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.65/0.58  fof(f285,plain,(
% 1.65/0.58    k3_subset_1(sK0,k7_subset_1(sK0,sK0,k8_setfam_1(sK0,sK1))) = k4_subset_1(sK0,k3_subset_1(sK0,sK0),k8_setfam_1(sK0,sK1)) | ~spl2_9),
% 1.65/0.58    inference(unit_resulting_resolution,[],[f231,f102,f59])).
% 1.65/0.58  fof(f59,plain,(
% 1.65/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.65/0.58    inference(cnf_transformation,[],[f29])).
% 1.65/0.58  fof(f29,plain,(
% 1.65/0.58    ! [X0,X1] : (! [X2] : (k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.65/0.58    inference(ennf_transformation,[],[f12])).
% 1.65/0.58  fof(f12,axiom,(
% 1.65/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_subset_1)).
% 1.65/0.58  fof(f102,plain,(
% 1.65/0.58    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.65/0.58    inference(unit_resulting_resolution,[],[f79,f70])).
% 1.65/0.58  fof(f70,plain,(
% 1.65/0.58    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f44])).
% 1.65/0.58  fof(f44,plain,(
% 1.65/0.58    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.65/0.58    inference(nnf_transformation,[],[f19])).
% 1.65/0.58  fof(f19,axiom,(
% 1.65/0.58    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.65/0.58  fof(f79,plain,(
% 1.65/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.65/0.58    inference(equality_resolution,[],[f67])).
% 1.65/0.58  fof(f67,plain,(
% 1.65/0.58    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.65/0.58    inference(cnf_transformation,[],[f43])).
% 1.65/0.58  fof(f43,plain,(
% 1.65/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.65/0.58    inference(flattening,[],[f42])).
% 1.65/0.58  fof(f42,plain,(
% 1.65/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.65/0.58    inference(nnf_transformation,[],[f1])).
% 1.65/0.58  fof(f1,axiom,(
% 1.65/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.65/0.58  fof(f848,plain,(
% 1.65/0.58    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = k3_subset_1(sK0,k3_subset_1(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)))) | ~spl2_10),
% 1.65/0.58    inference(resolution,[],[f135,f353])).
% 1.65/0.58  fof(f353,plain,(
% 1.65/0.58    m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl2_10),
% 1.65/0.58    inference(avatar_component_clause,[],[f351])).
% 1.65/0.58  fof(f351,plain,(
% 1.65/0.58    spl2_10 <=> m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 1.65/0.58  fof(f135,plain,(
% 1.65/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) | k5_setfam_1(X1,X0) = k3_subset_1(X1,k3_subset_1(X1,k5_setfam_1(X1,X0)))) )),
% 1.65/0.58    inference(resolution,[],[f60,f58])).
% 1.65/0.58  fof(f60,plain,(
% 1.65/0.58    ( ! [X0,X1] : (m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.65/0.58    inference(cnf_transformation,[],[f30])).
% 1.65/0.58  fof(f30,plain,(
% 1.65/0.58    ! [X0,X1] : (m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.65/0.58    inference(ennf_transformation,[],[f15])).
% 1.65/0.58  fof(f15,axiom,(
% 1.65/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_setfam_1)).
% 1.65/0.58  fof(f354,plain,(
% 1.65/0.58    spl2_10 | ~spl2_2),
% 1.65/0.58    inference(avatar_split_clause,[],[f150,f88,f351])).
% 1.65/0.58  fof(f150,plain,(
% 1.65/0.58    m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl2_2),
% 1.65/0.58    inference(unit_resulting_resolution,[],[f90,f62])).
% 1.65/0.58  fof(f62,plain,(
% 1.65/0.58    ( ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.65/0.58    inference(cnf_transformation,[],[f32])).
% 1.65/0.58  fof(f32,plain,(
% 1.65/0.58    ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.65/0.58    inference(ennf_transformation,[],[f16])).
% 1.65/0.58  fof(f16,axiom,(
% 1.65/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).
% 1.65/0.58  fof(f232,plain,(
% 1.65/0.58    spl2_9 | ~spl2_2),
% 1.65/0.58    inference(avatar_split_clause,[],[f143,f88,f229])).
% 1.65/0.58  fof(f143,plain,(
% 1.65/0.58    m1_subset_1(k8_setfam_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl2_2),
% 1.65/0.58    inference(unit_resulting_resolution,[],[f90,f61])).
% 1.65/0.58  fof(f61,plain,(
% 1.65/0.58    ( ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.65/0.58    inference(cnf_transformation,[],[f31])).
% 1.65/0.58  fof(f31,plain,(
% 1.65/0.58    ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.65/0.58    inference(ennf_transformation,[],[f17])).
% 1.65/0.58  fof(f17,axiom,(
% 1.65/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).
% 1.65/0.58  fof(f182,plain,(
% 1.65/0.58    ~spl2_6 | spl2_1 | ~spl2_2 | spl2_4),
% 1.65/0.58    inference(avatar_split_clause,[],[f176,f105,f88,f83,f179])).
% 1.65/0.58  fof(f105,plain,(
% 1.65/0.58    spl2_4 <=> k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = k3_subset_1(sK0,k6_setfam_1(sK0,sK1))),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 1.65/0.58  fof(f176,plain,(
% 1.65/0.58    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k8_setfam_1(sK0,sK1)) | (spl2_1 | ~spl2_2 | spl2_4)),
% 1.65/0.58    inference(backward_demodulation,[],[f107,f169])).
% 1.65/0.58  fof(f107,plain,(
% 1.65/0.58    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k6_setfam_1(sK0,sK1)) | spl2_4),
% 1.65/0.58    inference(avatar_component_clause,[],[f105])).
% 1.65/0.58  fof(f108,plain,(
% 1.65/0.58    ~spl2_4),
% 1.65/0.58    inference(avatar_split_clause,[],[f47,f105])).
% 1.65/0.58  fof(f47,plain,(
% 1.65/0.58    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k6_setfam_1(sK0,sK1))),
% 1.65/0.58    inference(cnf_transformation,[],[f41])).
% 1.65/0.58  fof(f41,plain,(
% 1.65/0.58    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k6_setfam_1(sK0,sK1)) & k1_xboole_0 != sK1 & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.65/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f40])).
% 1.65/0.58  fof(f40,plain,(
% 1.65/0.58    ? [X0,X1] : (k5_setfam_1(X0,k7_setfam_1(X0,X1)) != k3_subset_1(X0,k6_setfam_1(X0,X1)) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k6_setfam_1(sK0,sK1)) & k1_xboole_0 != sK1 & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 1.65/0.58    introduced(choice_axiom,[])).
% 1.65/0.58  fof(f25,plain,(
% 1.65/0.58    ? [X0,X1] : (k5_setfam_1(X0,k7_setfam_1(X0,X1)) != k3_subset_1(X0,k6_setfam_1(X0,X1)) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.65/0.58    inference(flattening,[],[f24])).
% 1.65/0.58  fof(f24,plain,(
% 1.65/0.58    ? [X0,X1] : ((k5_setfam_1(X0,k7_setfam_1(X0,X1)) != k3_subset_1(X0,k6_setfam_1(X0,X1)) & k1_xboole_0 != X1) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.65/0.58    inference(ennf_transformation,[],[f23])).
% 1.65/0.58  fof(f23,negated_conjecture,(
% 1.65/0.58    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k1_xboole_0 != X1 => k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k6_setfam_1(X0,X1))))),
% 1.65/0.58    inference(negated_conjecture,[],[f22])).
% 1.65/0.58  fof(f22,conjecture,(
% 1.65/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k1_xboole_0 != X1 => k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k6_setfam_1(X0,X1))))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_tops_2)).
% 1.65/0.58  fof(f91,plain,(
% 1.65/0.58    spl2_2),
% 1.65/0.58    inference(avatar_split_clause,[],[f45,f88])).
% 1.65/0.58  fof(f45,plain,(
% 1.65/0.58    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.65/0.58    inference(cnf_transformation,[],[f41])).
% 1.65/0.58  fof(f86,plain,(
% 1.65/0.58    ~spl2_1),
% 1.65/0.58    inference(avatar_split_clause,[],[f46,f83])).
% 1.65/0.58  fof(f46,plain,(
% 1.65/0.58    k1_xboole_0 != sK1),
% 1.65/0.58    inference(cnf_transformation,[],[f41])).
% 1.65/0.58  % SZS output end Proof for theBenchmark
% 1.65/0.58  % (26844)------------------------------
% 1.65/0.58  % (26844)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.58  % (26844)Termination reason: Refutation
% 1.65/0.58  
% 1.65/0.58  % (26844)Memory used [KB]: 11641
% 1.65/0.58  % (26844)Time elapsed: 0.146 s
% 1.65/0.58  % (26844)------------------------------
% 1.65/0.58  % (26844)------------------------------
% 1.65/0.58  % (26816)Success in time 0.216 s
%------------------------------------------------------------------------------
