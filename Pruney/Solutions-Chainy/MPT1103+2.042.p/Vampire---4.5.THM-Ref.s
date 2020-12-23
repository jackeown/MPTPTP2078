%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 691 expanded)
%              Number of leaves         :   24 ( 178 expanded)
%              Depth                    :   22
%              Number of atoms          :  312 (1972 expanded)
%              Number of equality atoms :  100 ( 928 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1575,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f88,f94,f151,f221,f569,f1122,f1124,f1181,f1218,f1428,f1545,f1574])).

fof(f1574,plain,
    ( spl3_2
    | ~ spl3_3
    | ~ spl3_22 ),
    inference(avatar_contradiction_clause,[],[f1572])).

fof(f1572,plain,
    ( $false
    | spl3_2
    | ~ spl3_3
    | ~ spl3_22 ),
    inference(subsumption_resolution,[],[f141,f1429])).

fof(f1429,plain,
    ( sK1 != u1_struct_0(sK0)
    | spl3_2
    | ~ spl3_22 ),
    inference(superposition,[],[f87,f1297])).

fof(f1297,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f1295])).

fof(f1295,plain,
    ( spl3_22
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f87,plain,
    ( sK1 != k2_struct_0(sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl3_2
  <=> sK1 = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f141,plain,
    ( sK1 = u1_struct_0(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl3_3
  <=> sK1 = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f1545,plain,
    ( spl3_3
    | ~ spl3_7
    | ~ spl3_17 ),
    inference(avatar_contradiction_clause,[],[f1500])).

fof(f1500,plain,
    ( $false
    | spl3_3
    | ~ spl3_7
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f140,f1484])).

fof(f1484,plain,
    ( sK1 = u1_struct_0(sK0)
    | ~ spl3_7
    | ~ spl3_17 ),
    inference(backward_demodulation,[],[f1381,f1441])).

fof(f1441,plain,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k1_xboole_0)
    | ~ spl3_7
    | ~ spl3_17 ),
    inference(backward_demodulation,[],[f181,f1408])).

fof(f1408,plain,
    ( k1_xboole_0 = k4_xboole_0(u1_struct_0(sK0),sK1)
    | ~ spl3_7
    | ~ spl3_17 ),
    inference(backward_demodulation,[],[f220,f1382])).

fof(f1382,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_17 ),
    inference(backward_demodulation,[],[f484,f1381])).

fof(f484,plain,(
    k2_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0) ),
    inference(global_subsumption,[],[f480])).

fof(f480,plain,(
    k2_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0) ),
    inference(global_subsumption,[],[f30,f479])).

fof(f479,plain,
    ( k2_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f447,f79])).

fof(f79,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK1) ),
    inference(superposition,[],[f33,f77])).

fof(f77,plain,(
    sK1 = k2_xboole_0(sK1,sK1) ),
    inference(global_subsumption,[],[f30,f76])).

fof(f76,plain,
    ( sK1 = k2_xboole_0(sK1,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(duplicate_literal_removal,[],[f73])).

fof(f73,plain,
    ( sK1 = k2_xboole_0(sK1,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f68,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f68,plain,(
    sK1 = k4_subset_1(u1_struct_0(sK0),sK1,sK1) ),
    inference(global_subsumption,[],[f65,f66])).

fof(f66,plain,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),sK1,sK1)
    | ~ sP2(u1_struct_0(sK0)) ),
    inference(resolution,[],[f30,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X1) = X1
      | ~ sP2(X0) ) ),
    inference(general_splitting,[],[f44,f49_D])).

fof(f49,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | sP2(X0) ) ),
    inference(cnf_transformation,[],[f49_D])).

fof(f49_D,plain,(
    ! [X0] :
      ( ! [X2] : ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    <=> ~ sP2(X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP2])])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X1) = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k4_subset_1)).

fof(f65,plain,(
    sP2(u1_struct_0(sK0)) ),
    inference(resolution,[],[f30,f49])).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f447,plain,
    ( k2_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f441,f192])).

fof(f192,plain,(
    k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),sK1) ),
    inference(global_subsumption,[],[f31,f129,f186])).

fof(f186,plain,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),sK1)
    | ~ l1_struct_0(sK0)
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f32,f181])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) = k2_struct_0(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) = k2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_pre_topc)).

fof(f129,plain,(
    m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(global_subsumption,[],[f30,f126])).

fof(f126,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f54,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f54,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f30,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f31,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( k2_struct_0(X0) = X1
              & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) )
            | ( k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)
              & k2_struct_0(X0) != X1 ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ~ ( k2_struct_0(X0) = X1
                  & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) )
              & ~ ( k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)
                  & k2_struct_0(X0) != X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ~ ( k2_struct_0(X0) = X1
                & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) )
            & ~ ( k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)
                & k2_struct_0(X0) != X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_pre_topc)).

fof(f441,plain,(
    ! [X0] :
      ( k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),X0) = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(sK1,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f440,f60])).

fof(f60,plain,(
    ! [X2] : k7_subset_1(u1_struct_0(sK0),sK1,X2) = k4_xboole_0(sK1,X2) ),
    inference(resolution,[],[f30,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f440,plain,(
    ! [X0] :
      ( k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,X0)) = k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f57,f55])).

fof(f55,plain,(
    k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
    inference(resolution,[],[f30,f35])).

fof(f57,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,X0)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X0) ) ),
    inference(resolution,[],[f30,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_subset_1)).

fof(f30,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f220,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_struct_0(sK0),sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f218])).

fof(f218,plain,
    ( spl3_7
  <=> k1_xboole_0 = k4_xboole_0(k2_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f181,plain,(
    sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(forward_demodulation,[],[f56,f55])).

fof(f56,plain,(
    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f30,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f1381,plain,
    ( u1_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0)
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f1130,f1355])).

fof(f1355,plain,
    ( k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f1129,f1125])).

fof(f1125,plain,
    ( k1_xboole_0 = k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl3_17 ),
    inference(resolution,[],[f1110,f876])).

fof(f876,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_xboole_0 = k4_xboole_0(X0,X0) ) ),
    inference(duplicate_literal_removal,[],[f863])).

fof(f863,plain,(
    ! [X0] :
      ( k1_xboole_0 = k4_xboole_0(X0,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f712,f34])).

fof(f712,plain,(
    ! [X2] :
      ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X2),k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_xboole_0 = k4_xboole_0(X2,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(superposition,[],[f703,f36])).

fof(f703,plain,(
    ! [X0] :
      ( k1_xboole_0 = k4_xboole_0(k3_subset_1(u1_struct_0(sK0),X0),k3_subset_1(u1_struct_0(sK0),X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(superposition,[],[f33,f235])).

fof(f235,plain,(
    ! [X1] :
      ( k3_subset_1(u1_struct_0(sK0),X1) = k2_xboole_0(k3_subset_1(u1_struct_0(sK0),X1),k3_subset_1(u1_struct_0(sK0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f230,f34])).

fof(f230,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_xboole_0(X3,X3) = X3 ) ),
    inference(duplicate_literal_removal,[],[f227])).

fof(f227,plain,(
    ! [X3] :
      ( k2_xboole_0(X3,X3) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(superposition,[],[f45,f69])).

fof(f69,plain,(
    ! [X0] :
      ( k4_subset_1(u1_struct_0(sK0),X0,X0) = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f65,f50])).

fof(f1110,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f1109])).

fof(f1109,plain,
    ( spl3_17
  <=> m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f1129,plain,
    ( k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl3_17 ),
    inference(resolution,[],[f1110,f35])).

fof(f1130,plain,
    ( u1_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | ~ spl3_17 ),
    inference(resolution,[],[f1110,f36])).

fof(f140,plain,
    ( sK1 != u1_struct_0(sK0)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f139])).

fof(f1428,plain,
    ( ~ spl3_17
    | spl3_22 ),
    inference(avatar_contradiction_clause,[],[f1398])).

fof(f1398,plain,
    ( $false
    | ~ spl3_17
    | spl3_22 ),
    inference(subsumption_resolution,[],[f1296,f1382])).

fof(f1296,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | spl3_22 ),
    inference(avatar_component_clause,[],[f1295])).

fof(f1218,plain,
    ( spl3_10
    | ~ spl3_19 ),
    inference(avatar_contradiction_clause,[],[f1214])).

fof(f1214,plain,
    ( $false
    | spl3_10
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f570,f1180])).

fof(f1180,plain,
    ( r1_tarski(k1_xboole_0,u1_struct_0(sK0))
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f1178])).

fof(f1178,plain,
    ( spl3_19
  <=> r1_tarski(k1_xboole_0,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f570,plain,
    ( ~ r1_tarski(k1_xboole_0,u1_struct_0(sK0))
    | spl3_10 ),
    inference(resolution,[],[f568,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f568,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f566])).

fof(f566,plain,
    ( spl3_10
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f1181,plain,
    ( ~ spl3_17
    | spl3_19
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f1176,f1109,f1178,f1109])).

fof(f1176,plain,
    ( r1_tarski(k1_xboole_0,u1_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f1175,f1125])).

fof(f1175,plain,
    ( r1_tarski(k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_17 ),
    inference(superposition,[],[f1162,f35])).

fof(f1162,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl3_17 ),
    inference(resolution,[],[f1128,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f1128,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_17 ),
    inference(resolution,[],[f1110,f34])).

fof(f1124,plain,
    ( ~ spl3_16
    | spl3_17 ),
    inference(avatar_split_clause,[],[f1123,f1109,f1105])).

fof(f1105,plain,
    ( spl3_16
  <=> r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f1123,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0))
    | spl3_17 ),
    inference(resolution,[],[f1111,f41])).

fof(f1111,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_17 ),
    inference(avatar_component_clause,[],[f1109])).

fof(f1122,plain,(
    spl3_16 ),
    inference(avatar_contradiction_clause,[],[f1118])).

fof(f1118,plain,
    ( $false
    | spl3_16 ),
    inference(resolution,[],[f1107,f48])).

fof(f48,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1107,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0))
    | spl3_16 ),
    inference(avatar_component_clause,[],[f1105])).

fof(f569,plain,
    ( ~ spl3_10
    | spl3_6 ),
    inference(avatar_split_clause,[],[f533,f214,f566])).

fof(f214,plain,
    ( spl3_6
  <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f533,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f34,f484])).

fof(f221,plain,
    ( ~ spl3_6
    | spl3_7
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f170,f148,f218,f214])).

fof(f148,plain,
    ( spl3_5
  <=> k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f170,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_struct_0(sK0),sK1)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_5 ),
    inference(superposition,[],[f150,f43])).

fof(f150,plain,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f148])).

fof(f151,plain,
    ( spl3_2
    | spl3_5 ),
    inference(avatar_split_clause,[],[f28,f148,f85])).

fof(f28,plain,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f94,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f92])).

fof(f92,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f30,f91])).

fof(f91,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_1 ),
    inference(trivial_inequality_removal,[],[f90])).

fof(f90,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_1 ),
    inference(forward_demodulation,[],[f89,f79])).

fof(f89,plain,
    ( k1_xboole_0 != k4_xboole_0(sK1,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_1 ),
    inference(superposition,[],[f83,f43])).

fof(f83,plain,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl3_1
  <=> k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f88,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f51,f85,f81])).

fof(f51,plain,
    ( sK1 != k2_struct_0(sK0)
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1) ),
    inference(inner_rewriting,[],[f29])).

fof(f29,plain,
    ( sK1 != k2_struct_0(sK0)
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:51:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.44  % (4402)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.48  % (4402)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f1575,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f88,f94,f151,f221,f569,f1122,f1124,f1181,f1218,f1428,f1545,f1574])).
% 0.21/0.48  fof(f1574,plain,(
% 0.21/0.48    spl3_2 | ~spl3_3 | ~spl3_22),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f1572])).
% 0.21/0.48  fof(f1572,plain,(
% 0.21/0.48    $false | (spl3_2 | ~spl3_3 | ~spl3_22)),
% 0.21/0.48    inference(subsumption_resolution,[],[f141,f1429])).
% 0.21/0.48  fof(f1429,plain,(
% 0.21/0.48    sK1 != u1_struct_0(sK0) | (spl3_2 | ~spl3_22)),
% 0.21/0.48    inference(superposition,[],[f87,f1297])).
% 0.21/0.48  fof(f1297,plain,(
% 0.21/0.48    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_22),
% 0.21/0.48    inference(avatar_component_clause,[],[f1295])).
% 0.21/0.48  fof(f1295,plain,(
% 0.21/0.48    spl3_22 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    sK1 != k2_struct_0(sK0) | spl3_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f85])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    spl3_2 <=> sK1 = k2_struct_0(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.48  fof(f141,plain,(
% 0.21/0.48    sK1 = u1_struct_0(sK0) | ~spl3_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f139])).
% 0.21/0.48  fof(f139,plain,(
% 0.21/0.48    spl3_3 <=> sK1 = u1_struct_0(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.48  fof(f1545,plain,(
% 0.21/0.48    spl3_3 | ~spl3_7 | ~spl3_17),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f1500])).
% 0.21/0.48  fof(f1500,plain,(
% 0.21/0.48    $false | (spl3_3 | ~spl3_7 | ~spl3_17)),
% 0.21/0.48    inference(subsumption_resolution,[],[f140,f1484])).
% 0.21/0.48  fof(f1484,plain,(
% 0.21/0.48    sK1 = u1_struct_0(sK0) | (~spl3_7 | ~spl3_17)),
% 0.21/0.48    inference(backward_demodulation,[],[f1381,f1441])).
% 0.21/0.48  fof(f1441,plain,(
% 0.21/0.48    sK1 = k3_subset_1(u1_struct_0(sK0),k1_xboole_0) | (~spl3_7 | ~spl3_17)),
% 0.21/0.48    inference(backward_demodulation,[],[f181,f1408])).
% 0.21/0.48  fof(f1408,plain,(
% 0.21/0.48    k1_xboole_0 = k4_xboole_0(u1_struct_0(sK0),sK1) | (~spl3_7 | ~spl3_17)),
% 0.21/0.48    inference(backward_demodulation,[],[f220,f1382])).
% 0.21/0.48  fof(f1382,plain,(
% 0.21/0.48    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_17),
% 0.21/0.48    inference(backward_demodulation,[],[f484,f1381])).
% 0.21/0.48  fof(f484,plain,(
% 0.21/0.48    k2_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0)),
% 0.21/0.48    inference(global_subsumption,[],[f480])).
% 0.21/0.48  fof(f480,plain,(
% 0.21/0.48    k2_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0)),
% 0.21/0.48    inference(global_subsumption,[],[f30,f479])).
% 0.21/0.48  fof(f479,plain,(
% 0.21/0.48    k2_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    inference(forward_demodulation,[],[f447,f79])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    k1_xboole_0 = k4_xboole_0(sK1,sK1)),
% 0.21/0.48    inference(superposition,[],[f33,f77])).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    sK1 = k2_xboole_0(sK1,sK1)),
% 0.21/0.48    inference(global_subsumption,[],[f30,f76])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    sK1 = k2_xboole_0(sK1,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f73])).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    sK1 = k2_xboole_0(sK1,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    inference(superposition,[],[f68,f45])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(flattening,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    sK1 = k4_subset_1(u1_struct_0(sK0),sK1,sK1)),
% 0.21/0.48    inference(global_subsumption,[],[f65,f66])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    sK1 = k4_subset_1(u1_struct_0(sK0),sK1,sK1) | ~sP2(u1_struct_0(sK0))),
% 0.21/0.48    inference(resolution,[],[f30,f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X1) = X1 | ~sP2(X0)) )),
% 0.21/0.48    inference(general_splitting,[],[f44,f49_D])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | sP2(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f49_D])).
% 0.21/0.48  fof(f49_D,plain,(
% 0.21/0.48    ( ! [X0] : (( ! [X2] : ~m1_subset_1(X2,k1_zfmisc_1(X0)) ) <=> ~sP2(X0)) )),
% 0.21/0.48    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X1) = X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(flattening,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X1) = X1 | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X1) = X1)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k4_subset_1)).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    sP2(u1_struct_0(sK0))),
% 0.21/0.48    inference(resolution,[],[f30,f49])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.21/0.48  fof(f447,plain,(
% 0.21/0.48    k2_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    inference(superposition,[],[f441,f192])).
% 0.21/0.48  fof(f192,plain,(
% 0.21/0.48    k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),sK1)),
% 0.21/0.48    inference(global_subsumption,[],[f31,f129,f186])).
% 0.21/0.48  fof(f186,plain,(
% 0.21/0.48    k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),sK1) | ~l1_struct_0(sK0) | ~m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    inference(superposition,[],[f32,f181])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~l1_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) = k2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) = k2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,axiom,(
% 0.21/0.48    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) = k2_struct_0(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_pre_topc)).
% 0.21/0.48  fof(f129,plain,(
% 0.21/0.48    m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    inference(global_subsumption,[],[f30,f126])).
% 0.21/0.48  fof(f126,plain,(
% 0.21/0.48    m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    inference(superposition,[],[f54,f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0,X1] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    inference(resolution,[],[f30,f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    l1_struct_0(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (((k2_struct_0(X0) = X1 & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) | (k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) & k2_struct_0(X0) != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_struct_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,negated_conjecture,(
% 0.21/0.48    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (~(k2_struct_0(X0) = X1 & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & ~(k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) & k2_struct_0(X0) != X1))))),
% 0.21/0.48    inference(negated_conjecture,[],[f13])).
% 0.21/0.48  fof(f13,conjecture,(
% 0.21/0.48    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (~(k2_struct_0(X0) = X1 & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & ~(k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) & k2_struct_0(X0) != X1))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_pre_topc)).
% 0.21/0.48  fof(f441,plain,(
% 0.21/0.48    ( ! [X0] : (k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),X0) = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(sK1,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.48    inference(forward_demodulation,[],[f440,f60])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    ( ! [X2] : (k7_subset_1(u1_struct_0(sK0),sK1,X2) = k4_xboole_0(sK1,X2)) )),
% 0.21/0.48    inference(resolution,[],[f30,f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.21/0.48  fof(f440,plain,(
% 0.21/0.48    ( ! [X0] : (k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,X0)) = k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.48    inference(forward_demodulation,[],[f57,f55])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1)),
% 0.21/0.48    inference(resolution,[],[f30,f35])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,X0)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X0)) )),
% 0.21/0.48    inference(resolution,[],[f30,f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_subset_1)).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f220,plain,(
% 0.21/0.48    k1_xboole_0 = k4_xboole_0(k2_struct_0(sK0),sK1) | ~spl3_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f218])).
% 0.21/0.48  fof(f218,plain,(
% 0.21/0.48    spl3_7 <=> k1_xboole_0 = k4_xboole_0(k2_struct_0(sK0),sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.48  fof(f181,plain,(
% 0.21/0.48    sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))),
% 0.21/0.48    inference(forward_demodulation,[],[f56,f55])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.21/0.48    inference(resolution,[],[f30,f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.21/0.48  fof(f1381,plain,(
% 0.21/0.48    u1_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0) | ~spl3_17),
% 0.21/0.48    inference(forward_demodulation,[],[f1130,f1355])).
% 0.21/0.48  fof(f1355,plain,(
% 0.21/0.48    k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) | ~spl3_17),
% 0.21/0.48    inference(forward_demodulation,[],[f1129,f1125])).
% 0.21/0.48  fof(f1125,plain,(
% 0.21/0.48    k1_xboole_0 = k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)) | ~spl3_17),
% 0.21/0.48    inference(resolution,[],[f1110,f876])).
% 0.21/0.48  fof(f876,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f863])).
% 0.21/0.48  fof(f863,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.48    inference(resolution,[],[f712,f34])).
% 0.21/0.48  fof(f712,plain,(
% 0.21/0.48    ( ! [X2] : (~m1_subset_1(k3_subset_1(u1_struct_0(sK0),X2),k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = k4_xboole_0(X2,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.48    inference(superposition,[],[f703,f36])).
% 0.21/0.48  fof(f703,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k3_subset_1(u1_struct_0(sK0),X0),k3_subset_1(u1_struct_0(sK0),X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.48    inference(superposition,[],[f33,f235])).
% 0.21/0.48  fof(f235,plain,(
% 0.21/0.48    ( ! [X1] : (k3_subset_1(u1_struct_0(sK0),X1) = k2_xboole_0(k3_subset_1(u1_struct_0(sK0),X1),k3_subset_1(u1_struct_0(sK0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.48    inference(resolution,[],[f230,f34])).
% 0.21/0.48  fof(f230,plain,(
% 0.21/0.48    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | k2_xboole_0(X3,X3) = X3) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f227])).
% 0.21/0.48  fof(f227,plain,(
% 0.21/0.48    ( ! [X3] : (k2_xboole_0(X3,X3) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.48    inference(superposition,[],[f45,f69])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    ( ! [X0] : (k4_subset_1(u1_struct_0(sK0),X0,X0) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.48    inference(resolution,[],[f65,f50])).
% 0.21/0.48  fof(f1110,plain,(
% 0.21/0.48    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_17),
% 0.21/0.48    inference(avatar_component_clause,[],[f1109])).
% 0.21/0.48  fof(f1109,plain,(
% 0.21/0.48    spl3_17 <=> m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.48  fof(f1129,plain,(
% 0.21/0.48    k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) | ~spl3_17),
% 0.21/0.48    inference(resolution,[],[f1110,f35])).
% 0.21/0.48  fof(f1130,plain,(
% 0.21/0.48    u1_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))) | ~spl3_17),
% 0.21/0.48    inference(resolution,[],[f1110,f36])).
% 0.21/0.48  fof(f140,plain,(
% 0.21/0.48    sK1 != u1_struct_0(sK0) | spl3_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f139])).
% 0.21/0.48  fof(f1428,plain,(
% 0.21/0.48    ~spl3_17 | spl3_22),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f1398])).
% 0.21/0.48  fof(f1398,plain,(
% 0.21/0.48    $false | (~spl3_17 | spl3_22)),
% 0.21/0.48    inference(subsumption_resolution,[],[f1296,f1382])).
% 0.21/0.48  fof(f1296,plain,(
% 0.21/0.48    u1_struct_0(sK0) != k2_struct_0(sK0) | spl3_22),
% 0.21/0.48    inference(avatar_component_clause,[],[f1295])).
% 0.21/0.48  fof(f1218,plain,(
% 0.21/0.48    spl3_10 | ~spl3_19),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f1214])).
% 0.21/0.48  fof(f1214,plain,(
% 0.21/0.48    $false | (spl3_10 | ~spl3_19)),
% 0.21/0.48    inference(subsumption_resolution,[],[f570,f1180])).
% 0.21/0.48  fof(f1180,plain,(
% 0.21/0.48    r1_tarski(k1_xboole_0,u1_struct_0(sK0)) | ~spl3_19),
% 0.21/0.48    inference(avatar_component_clause,[],[f1178])).
% 0.21/0.48  fof(f1178,plain,(
% 0.21/0.48    spl3_19 <=> r1_tarski(k1_xboole_0,u1_struct_0(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.48  fof(f570,plain,(
% 0.21/0.48    ~r1_tarski(k1_xboole_0,u1_struct_0(sK0)) | spl3_10),
% 0.21/0.48    inference(resolution,[],[f568,f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.48  fof(f568,plain,(
% 0.21/0.48    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f566])).
% 0.21/0.48  fof(f566,plain,(
% 0.21/0.48    spl3_10 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.48  fof(f1181,plain,(
% 0.21/0.48    ~spl3_17 | spl3_19 | ~spl3_17),
% 0.21/0.48    inference(avatar_split_clause,[],[f1176,f1109,f1178,f1109])).
% 0.21/0.48  fof(f1176,plain,(
% 0.21/0.48    r1_tarski(k1_xboole_0,u1_struct_0(sK0)) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_17),
% 0.21/0.48    inference(forward_demodulation,[],[f1175,f1125])).
% 0.21/0.48  fof(f1175,plain,(
% 0.21/0.48    r1_tarski(k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_17),
% 0.21/0.48    inference(superposition,[],[f1162,f35])).
% 0.21/0.48  fof(f1162,plain,(
% 0.21/0.48    r1_tarski(k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)) | ~spl3_17),
% 0.21/0.48    inference(resolution,[],[f1128,f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f1128,plain,(
% 0.21/0.48    m1_subset_1(k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_17),
% 0.21/0.48    inference(resolution,[],[f1110,f34])).
% 0.21/0.48  fof(f1124,plain,(
% 0.21/0.48    ~spl3_16 | spl3_17),
% 0.21/0.48    inference(avatar_split_clause,[],[f1123,f1109,f1105])).
% 0.21/0.48  fof(f1105,plain,(
% 0.21/0.48    spl3_16 <=> r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.48  fof(f1123,plain,(
% 0.21/0.48    ~r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) | spl3_17),
% 0.21/0.48    inference(resolution,[],[f1111,f41])).
% 0.21/0.48  fof(f1111,plain,(
% 0.21/0.48    ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_17),
% 0.21/0.48    inference(avatar_component_clause,[],[f1109])).
% 0.21/0.48  fof(f1122,plain,(
% 0.21/0.48    spl3_16),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f1118])).
% 0.21/0.48  fof(f1118,plain,(
% 0.21/0.48    $false | spl3_16),
% 0.21/0.48    inference(resolution,[],[f1107,f48])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.48    inference(equality_resolution,[],[f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.48  fof(f1107,plain,(
% 0.21/0.48    ~r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) | spl3_16),
% 0.21/0.48    inference(avatar_component_clause,[],[f1105])).
% 0.21/0.48  fof(f569,plain,(
% 0.21/0.48    ~spl3_10 | spl3_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f533,f214,f566])).
% 0.21/0.48  fof(f214,plain,(
% 0.21/0.48    spl3_6 <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.48  fof(f533,plain,(
% 0.21/0.48    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    inference(superposition,[],[f34,f484])).
% 0.21/0.48  fof(f221,plain,(
% 0.21/0.48    ~spl3_6 | spl3_7 | ~spl3_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f170,f148,f218,f214])).
% 0.21/0.48  fof(f148,plain,(
% 0.21/0.48    spl3_5 <=> k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.48  fof(f170,plain,(
% 0.21/0.48    k1_xboole_0 = k4_xboole_0(k2_struct_0(sK0),sK1) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_5),
% 0.21/0.48    inference(superposition,[],[f150,f43])).
% 0.21/0.48  fof(f150,plain,(
% 0.21/0.48    k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | ~spl3_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f148])).
% 0.21/0.48  fof(f151,plain,(
% 0.21/0.48    spl3_2 | spl3_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f28,f148,f85])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 = k2_struct_0(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    spl3_1),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f92])).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    $false | spl3_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f30,f91])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_1),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f90])).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_1),
% 0.21/0.48    inference(forward_demodulation,[],[f89,f79])).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    k1_xboole_0 != k4_xboole_0(sK1,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_1),
% 0.21/0.48    inference(superposition,[],[f83,f43])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1) | spl3_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f81])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    spl3_1 <=> k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),sK1,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    ~spl3_1 | ~spl3_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f51,f85,f81])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    sK1 != k2_struct_0(sK0) | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)),
% 0.21/0.48    inference(inner_rewriting,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    sK1 != k2_struct_0(sK0) | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (4402)------------------------------
% 0.21/0.48  % (4402)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (4402)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (4402)Memory used [KB]: 11641
% 0.21/0.48  % (4402)Time elapsed: 0.074 s
% 0.21/0.48  % (4402)------------------------------
% 0.21/0.48  % (4402)------------------------------
% 0.21/0.49  % (4377)Success in time 0.124 s
%------------------------------------------------------------------------------
