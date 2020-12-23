%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1239+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:14 EST 2020

% Result     : Theorem 34.34s
% Output     : Refutation 34.34s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 342 expanded)
%              Number of leaves         :   36 ( 120 expanded)
%              Depth                    :   18
%              Number of atoms          :  407 ( 931 expanded)
%              Number of equality atoms :   70 ( 124 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f51726,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3472,f3477,f3487,f3497,f3517,f3591,f3749,f3769,f4257,f4472,f9360,f51720])).

fof(f51720,plain,
    ( ~ spl92_1
    | ~ spl92_2
    | ~ spl92_4
    | ~ spl92_25
    | ~ spl92_29
    | spl92_30
    | ~ spl92_148 ),
    inference(avatar_contradiction_clause,[],[f51719])).

fof(f51719,plain,
    ( $false
    | ~ spl92_1
    | ~ spl92_2
    | ~ spl92_4
    | ~ spl92_25
    | ~ spl92_29
    | spl92_30
    | ~ spl92_148 ),
    inference(subsumption_resolution,[],[f51231,f47678])).

fof(f47678,plain,
    ( ! [X0] : r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,X0)),k4_xboole_0(k1_tops_1(sK0,sK1),X0))
    | ~ spl92_1
    | ~ spl92_2
    | ~ spl92_4
    | ~ spl92_29
    | ~ spl92_148 ),
    inference(forward_demodulation,[],[f45645,f21678])).

fof(f21678,plain,
    ( ! [X0] : k1_tops_1(sK0,k4_xboole_0(sK1,X0)) = k1_tops_1(sK0,k4_xboole_0(k1_tops_1(sK0,sK1),X0))
    | ~ spl92_1
    | ~ spl92_2
    | ~ spl92_4
    | ~ spl92_29
    | ~ spl92_148 ),
    inference(backward_demodulation,[],[f9024,f21676])).

fof(f21676,plain,
    ( k1_tops_1(sK0,sK1) = k3_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl92_148 ),
    inference(forward_demodulation,[],[f21669,f2987])).

fof(f2987,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f100])).

fof(f100,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f21669,plain,
    ( k4_xboole_0(k1_tops_1(sK0,sK1),k1_xboole_0) = k3_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl92_148 ),
    inference(backward_demodulation,[],[f21645,f21424])).

fof(f21424,plain,
    ( ! [X0] : k4_xboole_0(k1_tops_1(sK0,sK1),X0) = k7_subset_1(sK1,k1_tops_1(sK0,sK1),X0)
    | ~ spl92_148 ),
    inference(unit_resulting_resolution,[],[f9359,f2795])).

fof(f2795,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f2149])).

fof(f2149,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f494])).

fof(f494,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f9359,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl92_148 ),
    inference(avatar_component_clause,[],[f9357])).

fof(f9357,plain,
    ( spl92_148
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl92_148])])).

fof(f21645,plain,
    ( k3_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k7_subset_1(sK1,k1_tops_1(sK0,sK1),k1_xboole_0)
    | ~ spl92_148 ),
    inference(forward_demodulation,[],[f21644,f3176])).

fof(f3176,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f21644,plain,
    ( k3_xboole_0(k1_tops_1(sK0,sK1),sK1) = k7_subset_1(sK1,k1_tops_1(sK0,sK1),k1_xboole_0)
    | ~ spl92_148 ),
    inference(forward_demodulation,[],[f21643,f8788])).

fof(f8788,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k9_subset_1(X1,X0,X1) ),
    inference(unit_resulting_resolution,[],[f3538,f2839])).

fof(f2839,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f2185])).

fof(f2185,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f496])).

fof(f496,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f3538,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f3363,f2770])).

fof(f2770,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2554])).

fof(f2554,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f609])).

fof(f609,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f3363,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f2779])).

fof(f2779,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2564])).

fof(f2564,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f2563])).

fof(f2563,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f21643,plain,
    ( k7_subset_1(sK1,k1_tops_1(sK0,sK1),k1_xboole_0) = k9_subset_1(sK1,k1_tops_1(sK0,sK1),sK1)
    | ~ spl92_148 ),
    inference(forward_demodulation,[],[f21438,f7670])).

fof(f7670,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f7280,f7662])).

fof(f7662,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    inference(forward_demodulation,[],[f7293,f5383])).

fof(f5383,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(unit_resulting_resolution,[],[f2983,f3053])).

fof(f3053,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f2348])).

fof(f2348,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f132])).

fof(f132,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f2983,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f152])).

fof(f152,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_xboole_1)).

fof(f7293,plain,(
    ! [X0] : k3_subset_1(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(unit_resulting_resolution,[],[f3538,f2903])).

fof(f2903,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f2258])).

fof(f2258,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f462])).

fof(f462,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f7280,plain,(
    ! [X0] : k3_subset_1(X0,k3_subset_1(X0,X0)) = X0 ),
    inference(unit_resulting_resolution,[],[f3538,f2902])).

fof(f2902,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f2257])).

fof(f2257,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f487])).

fof(f487,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f21438,plain,
    ( k7_subset_1(sK1,k1_tops_1(sK0,sK1),k1_xboole_0) = k9_subset_1(sK1,k1_tops_1(sK0,sK1),k3_subset_1(sK1,k1_xboole_0))
    | ~ spl92_148 ),
    inference(unit_resulting_resolution,[],[f3081,f9359,f2805])).

fof(f2805,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f2156])).

fof(f2156,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f506])).

fof(f506,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).

fof(f3081,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f522])).

fof(f522,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f9024,plain,
    ( ! [X0] : k1_tops_1(sK0,k4_xboole_0(sK1,X0)) = k1_tops_1(sK0,k4_xboole_0(k3_xboole_0(sK1,k1_tops_1(sK0,sK1)),X0))
    | ~ spl92_1
    | ~ spl92_2
    | ~ spl92_4
    | ~ spl92_29 ),
    inference(forward_demodulation,[],[f9023,f3178])).

fof(f3178,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f2123])).

fof(f2123,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f9023,plain,
    ( ! [X0] : k1_tops_1(sK0,k4_xboole_0(k3_xboole_0(sK1,sK1),X0)) = k1_tops_1(sK0,k4_xboole_0(k3_xboole_0(sK1,k1_tops_1(sK0,sK1)),X0))
    | ~ spl92_1
    | ~ spl92_2
    | ~ spl92_4
    | ~ spl92_29 ),
    inference(forward_demodulation,[],[f9022,f8995])).

fof(f8995,plain,
    ( ! [X0,X1] : k9_subset_1(u1_struct_0(sK0),X0,k4_xboole_0(sK1,X1)) = k4_xboole_0(k3_xboole_0(X0,sK1),X1)
    | ~ spl92_4 ),
    inference(forward_demodulation,[],[f8793,f2943])).

fof(f2943,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f111])).

fof(f111,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f8793,plain,
    ( ! [X0,X1] : k9_subset_1(u1_struct_0(sK0),X0,k4_xboole_0(sK1,X1)) = k3_xboole_0(X0,k4_xboole_0(sK1,X1))
    | ~ spl92_4 ),
    inference(unit_resulting_resolution,[],[f3586,f2839])).

fof(f3586,plain,
    ( ! [X0] : m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl92_4 ),
    inference(backward_demodulation,[],[f3564,f3576])).

fof(f3576,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)
    | ~ spl92_4 ),
    inference(unit_resulting_resolution,[],[f3486,f2795])).

fof(f3486,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl92_4 ),
    inference(avatar_component_clause,[],[f3484])).

fof(f3484,plain,
    ( spl92_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl92_4])])).

fof(f3564,plain,
    ( ! [X0] : m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl92_4 ),
    inference(unit_resulting_resolution,[],[f3486,f2796])).

fof(f2796,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f2150])).

fof(f2150,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f470])).

fof(f470,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).

fof(f9022,plain,
    ( ! [X0] : k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),sK1,k4_xboole_0(sK1,X0))) = k1_tops_1(sK0,k4_xboole_0(k3_xboole_0(sK1,k1_tops_1(sK0,sK1)),X0))
    | ~ spl92_1
    | ~ spl92_2
    | ~ spl92_4
    | ~ spl92_29 ),
    inference(forward_demodulation,[],[f9002,f3176])).

fof(f9002,plain,
    ( ! [X0] : k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),sK1,k4_xboole_0(sK1,X0))) = k1_tops_1(sK0,k4_xboole_0(k3_xboole_0(k1_tops_1(sK0,sK1),sK1),X0))
    | ~ spl92_1
    | ~ spl92_2
    | ~ spl92_4
    | ~ spl92_29 ),
    inference(backward_demodulation,[],[f4463,f8995])).

fof(f4463,plain,
    ( ! [X0] : k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),sK1,k4_xboole_0(sK1,X0))) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k4_xboole_0(sK1,X0)))
    | ~ spl92_1
    | ~ spl92_2
    | ~ spl92_4
    | ~ spl92_29 ),
    inference(forward_demodulation,[],[f4462,f3863])).

fof(f3863,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_xboole_0(sK1,X0))) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),sK1,k4_xboole_0(sK1,X0)))
    | ~ spl92_1
    | ~ spl92_2
    | ~ spl92_4 ),
    inference(unit_resulting_resolution,[],[f3471,f3476,f3486,f3586,f2789])).

fof(f2789,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k9_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)) = k1_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) ) ),
    inference(cnf_transformation,[],[f2141])).

fof(f2141,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k9_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)) = k1_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f2140])).

fof(f2140,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k9_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)) = k1_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2114])).

fof(f2114,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => k9_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)) = k1_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tops_1)).

fof(f3476,plain,
    ( l1_pre_topc(sK0)
    | ~ spl92_2 ),
    inference(avatar_component_clause,[],[f3474])).

fof(f3474,plain,
    ( spl92_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl92_2])])).

fof(f3471,plain,
    ( v2_pre_topc(sK0)
    | ~ spl92_1 ),
    inference(avatar_component_clause,[],[f3469])).

fof(f3469,plain,
    ( spl92_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl92_1])])).

fof(f4462,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_xboole_0(sK1,X0))) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k4_xboole_0(sK1,X0)))
    | ~ spl92_1
    | ~ spl92_2
    | ~ spl92_4
    | ~ spl92_29 ),
    inference(forward_demodulation,[],[f4268,f3614])).

fof(f3614,plain,
    ( k1_tops_1(sK0,sK1) = k1_tops_1(sK0,k1_tops_1(sK0,sK1))
    | ~ spl92_2
    | ~ spl92_4 ),
    inference(unit_resulting_resolution,[],[f3476,f3486,f2787])).

fof(f2787,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f2137])).

fof(f2137,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2136])).

fof(f2136,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2096])).

fof(f2096,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k1_tops_1)).

fof(f4268,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,k4_xboole_0(sK1,X0))) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k4_xboole_0(sK1,X0)))
    | ~ spl92_1
    | ~ spl92_2
    | ~ spl92_4
    | ~ spl92_29 ),
    inference(unit_resulting_resolution,[],[f3471,f3476,f3586,f4256,f2789])).

fof(f4256,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl92_29 ),
    inference(avatar_component_clause,[],[f4254])).

fof(f4254,plain,
    ( spl92_29
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl92_29])])).

fof(f45645,plain,
    ( ! [X0] : r1_tarski(k1_tops_1(sK0,k4_xboole_0(k1_tops_1(sK0,sK1),X0)),k4_xboole_0(k1_tops_1(sK0,sK1),X0))
    | ~ spl92_2
    | ~ spl92_29 ),
    inference(unit_resulting_resolution,[],[f3476,f4371,f2794])).

fof(f2794,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f2148])).

fof(f2148,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2113])).

fof(f2113,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f4371,plain,
    ( ! [X0] : m1_subset_1(k4_xboole_0(k1_tops_1(sK0,sK1),X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl92_29 ),
    inference(backward_demodulation,[],[f4324,f4323])).

fof(f4323,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X0) = k4_xboole_0(k1_tops_1(sK0,sK1),X0)
    | ~ spl92_29 ),
    inference(unit_resulting_resolution,[],[f4256,f2795])).

fof(f4324,plain,
    ( ! [X0] : m1_subset_1(k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl92_29 ),
    inference(unit_resulting_resolution,[],[f4256,f2796])).

fof(f51231,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),sK2))
    | ~ spl92_25
    | spl92_30 ),
    inference(unit_resulting_resolution,[],[f4471,f6924,f2767])).

fof(f2767,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f2128])).

fof(f2128,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f2127])).

fof(f2127,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f77])).

fof(f77,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f6924,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(X0,sK2),k4_xboole_0(X0,k1_tops_1(sK0,sK2)))
    | ~ spl92_25 ),
    inference(unit_resulting_resolution,[],[f3768,f2927])).

fof(f2927,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    inference(cnf_transformation,[],[f2276])).

fof(f2276,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f94])).

fof(f94,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).

fof(f3768,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ spl92_25 ),
    inference(avatar_component_clause,[],[f3766])).

fof(f3766,plain,
    ( spl92_25
  <=> r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl92_25])])).

fof(f4471,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
    | spl92_30 ),
    inference(avatar_component_clause,[],[f4469])).

fof(f4469,plain,
    ( spl92_30
  <=> r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl92_30])])).

fof(f9360,plain,
    ( spl92_148
    | ~ spl92_23 ),
    inference(avatar_split_clause,[],[f3755,f3746,f9357])).

fof(f3746,plain,
    ( spl92_23
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl92_23])])).

fof(f3755,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl92_23 ),
    inference(unit_resulting_resolution,[],[f3748,f2770])).

fof(f3748,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl92_23 ),
    inference(avatar_component_clause,[],[f3746])).

fof(f4472,plain,
    ( ~ spl92_30
    | spl92_18
    | ~ spl92_29 ),
    inference(avatar_split_clause,[],[f4380,f4254,f3588,f4469])).

fof(f3588,plain,
    ( spl92_18
  <=> r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl92_18])])).

fof(f4380,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
    | spl92_18
    | ~ spl92_29 ),
    inference(backward_demodulation,[],[f3590,f4323])).

fof(f3590,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
    | spl92_18 ),
    inference(avatar_component_clause,[],[f3588])).

fof(f4257,plain,
    ( spl92_29
    | ~ spl92_2
    | ~ spl92_4 ),
    inference(avatar_split_clause,[],[f3604,f3484,f3474,f4254])).

fof(f3604,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl92_2
    | ~ spl92_4 ),
    inference(unit_resulting_resolution,[],[f3476,f3486,f2788])).

fof(f2788,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2139])).

fof(f2139,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2138])).

fof(f2138,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2087])).

fof(f2087,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(f3769,plain,
    ( spl92_25
    | ~ spl92_2
    | ~ spl92_6 ),
    inference(avatar_split_clause,[],[f3573,f3494,f3474,f3766])).

fof(f3494,plain,
    ( spl92_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl92_6])])).

fof(f3573,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ spl92_2
    | ~ spl92_6 ),
    inference(unit_resulting_resolution,[],[f3476,f3496,f2794])).

fof(f3496,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl92_6 ),
    inference(avatar_component_clause,[],[f3494])).

fof(f3749,plain,
    ( spl92_23
    | ~ spl92_2
    | ~ spl92_4 ),
    inference(avatar_split_clause,[],[f3572,f3484,f3474,f3746])).

fof(f3572,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl92_2
    | ~ spl92_4 ),
    inference(unit_resulting_resolution,[],[f3476,f3486,f2794])).

fof(f3591,plain,
    ( ~ spl92_18
    | ~ spl92_4
    | spl92_10 ),
    inference(avatar_split_clause,[],[f3585,f3514,f3484,f3588])).

fof(f3514,plain,
    ( spl92_10
  <=> r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl92_10])])).

fof(f3585,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
    | ~ spl92_4
    | spl92_10 ),
    inference(backward_demodulation,[],[f3516,f3576])).

fof(f3516,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
    | spl92_10 ),
    inference(avatar_component_clause,[],[f3514])).

fof(f3517,plain,(
    ~ spl92_10 ),
    inference(avatar_split_clause,[],[f2766,f3514])).

fof(f2766,plain,(
    ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f2553])).

fof(f2553,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f2126,f2552,f2551,f2550])).

fof(f2550,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),X1,X2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f2551,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),X1,X2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,X2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f2552,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,X2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2)))
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f2126,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f2125])).

fof(f2125,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2119])).

fof(f2119,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f2118])).

fof(f2118,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_tops_1)).

fof(f3497,plain,(
    spl92_6 ),
    inference(avatar_split_clause,[],[f2765,f3494])).

fof(f2765,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f2553])).

fof(f3487,plain,(
    spl92_4 ),
    inference(avatar_split_clause,[],[f2764,f3484])).

fof(f2764,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f2553])).

fof(f3477,plain,(
    spl92_2 ),
    inference(avatar_split_clause,[],[f2763,f3474])).

fof(f2763,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f2553])).

fof(f3472,plain,(
    spl92_1 ),
    inference(avatar_split_clause,[],[f2762,f3469])).

fof(f2762,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f2553])).
%------------------------------------------------------------------------------
