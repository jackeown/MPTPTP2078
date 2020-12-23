%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:55 EST 2020

% Result     : Theorem 2.11s
% Output     : Refutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :  124 (1733 expanded)
%              Number of leaves         :   22 ( 497 expanded)
%              Depth                    :   25
%              Number of atoms          :  247 (3261 expanded)
%              Number of equality atoms :   92 (1382 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1727,plain,(
    $false ),
    inference(global_subsumption,[],[f1681,f1726])).

fof(f1726,plain,(
    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1701,f1720])).

fof(f1720,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1715,f1211])).

fof(f1211,plain,(
    k1_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f1061,f481])).

fof(f481,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) ),
    inference(backward_demodulation,[],[f452,f446])).

fof(f446,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X0,X0,X1) ),
    inference(unit_resulting_resolution,[],[f114,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f74,f83])).

fof(f83,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f65,f63])).

fof(f63,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f65,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f114,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f113,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f113,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f86,f84])).

fof(f84,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f53,f83])).

fof(f53,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f86,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
    inference(definition_unfolding,[],[f61,f83])).

fof(f61,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f452,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) ),
    inference(unit_resulting_resolution,[],[f48,f91])).

fof(f48,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

fof(f1061,plain,(
    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f50,f48,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(f50,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f1715,plain,(
    k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f1694,f472])).

fof(f472,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k7_subset_1(X0,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(backward_demodulation,[],[f90,f446])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f69,f83])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f1694,plain,(
    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f1684,f72])).

fof(f1684,plain,(
    r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f50,f48,f1678,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | r1_tarski(k2_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

fof(f1678,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(global_subsumption,[],[f50,f49,f48,f1677])).

fof(f1677,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v4_pre_topc(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f1676])).

fof(f1676,plain,
    ( sK1 != sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v4_pre_topc(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f1675])).

fof(f1675,plain,
    ( sK1 != sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v4_pre_topc(sK1,sK0)
    | v4_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f57,f1674])).

fof(f1674,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(forward_demodulation,[],[f1673,f1150])).

fof(f1150,plain,(
    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f825,f1141])).

fof(f1141,plain,(
    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f50,f48,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(f825,plain,(
    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f48,f294,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f294,plain,(
    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f50,f48,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f1673,plain,
    ( sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f1597,f1247])).

fof(f1247,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f482,f1243])).

fof(f1243,plain,(
    k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f1231,f472])).

fof(f1231,plain,(
    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f1217,f72])).

fof(f1217,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(superposition,[],[f470,f1211])).

fof(f470,plain,(
    ! [X0,X1] : r1_tarski(k7_subset_1(X0,X0,X1),X0) ),
    inference(backward_demodulation,[],[f86,f446])).

fof(f482,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f46,f481])).

fof(f46,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f1597,plain,(
    sK1 = k2_xboole_0(sK1,k3_subset_1(sK1,k1_tops_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f1253,f281])).

fof(f281,plain,(
    ! [X2,X1] :
      ( k2_xboole_0(X2,X1) = X2
      | ~ r1_tarski(X1,X2) ) ),
    inference(forward_demodulation,[],[f270,f52])).

fof(f52,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f270,plain,(
    ! [X2,X1] :
      ( k2_xboole_0(X2,X1) = k2_xboole_0(X2,k1_xboole_0)
      | ~ r1_tarski(X1,X2) ) ),
    inference(backward_demodulation,[],[f195,f262])).

fof(f262,plain,(
    ! [X3] : k1_xboole_0 = k5_xboole_0(X3,X3) ),
    inference(forward_demodulation,[],[f258,f128])).

fof(f128,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f106,f122])).

fof(f122,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0)) ),
    inference(unit_resulting_resolution,[],[f51,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f67,f63])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f51,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f106,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(k1_xboole_0,X0))) = X0 ),
    inference(superposition,[],[f84,f62])).

fof(f62,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f258,plain,(
    ! [X3] : k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X3,k1_xboole_0)) ),
    inference(superposition,[],[f131,f134])).

fof(f134,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    inference(superposition,[],[f122,f62])).

fof(f131,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) ),
    inference(backward_demodulation,[],[f87,f130])).

fof(f130,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) ),
    inference(forward_demodulation,[],[f120,f62])).

fof(f120,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)) ),
    inference(unit_resulting_resolution,[],[f86,f89])).

fof(f87,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))))) ),
    inference(definition_unfolding,[],[f64,f63,f83,f83])).

fof(f64,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f195,plain,(
    ! [X2,X1] :
      ( k2_xboole_0(X2,X1) = k2_xboole_0(X2,k5_xboole_0(X1,X1))
      | ~ r1_tarski(X1,X2) ) ),
    inference(superposition,[],[f88,f89])).

fof(f88,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) ),
    inference(definition_unfolding,[],[f66,f83])).

fof(f66,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f1253,plain,(
    r1_tarski(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),sK1) ),
    inference(unit_resulting_resolution,[],[f1234,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1234,plain,(
    m1_subset_1(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),k1_zfmisc_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f1231,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f57,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f49,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f1701,plain,(
    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f1694,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f1681,plain,(
    k2_tops_1(sK0,sK1) != k3_subset_1(sK1,k1_tops_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f1678,f1246])).

fof(f1246,plain,
    ( k2_tops_1(sK0,sK1) != k3_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f483,f1243])).

fof(f483,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f47,f481])).

fof(f47,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:31:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (11842)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.48  % (11866)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.48  % (11858)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.50  % (11846)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (11858)Refutation not found, incomplete strategy% (11858)------------------------------
% 0.21/0.51  % (11858)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (11858)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (11858)Memory used [KB]: 10618
% 0.21/0.51  % (11858)Time elapsed: 0.114 s
% 0.21/0.51  % (11858)------------------------------
% 0.21/0.51  % (11858)------------------------------
% 0.21/0.51  % (11850)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (11843)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (11847)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (11856)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (11864)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (11867)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (11841)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (11845)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (11844)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (11854)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (11869)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (11865)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (11868)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (11870)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (11859)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (11863)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (11861)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (11860)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (11863)Refutation not found, incomplete strategy% (11863)------------------------------
% 0.21/0.54  % (11863)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (11863)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (11863)Memory used [KB]: 10746
% 0.21/0.54  % (11863)Time elapsed: 0.106 s
% 0.21/0.54  % (11863)------------------------------
% 0.21/0.54  % (11863)------------------------------
% 0.21/0.54  % (11857)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (11862)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (11851)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (11848)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.55  % (11855)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % (11853)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.56  % (11849)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.56  % (11852)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 2.11/0.64  % (11874)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.11/0.68  % (11865)Refutation found. Thanks to Tanya!
% 2.11/0.68  % SZS status Theorem for theBenchmark
% 2.11/0.69  % SZS output start Proof for theBenchmark
% 2.11/0.69  fof(f1727,plain,(
% 2.11/0.69    $false),
% 2.11/0.69    inference(global_subsumption,[],[f1681,f1726])).
% 2.11/0.70  fof(f1726,plain,(
% 2.11/0.70    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))),
% 2.11/0.70    inference(forward_demodulation,[],[f1701,f1720])).
% 2.11/0.70  fof(f1720,plain,(
% 2.11/0.70    k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))),
% 2.11/0.70    inference(forward_demodulation,[],[f1715,f1211])).
% 2.11/0.70  fof(f1211,plain,(
% 2.11/0.70    k1_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1))),
% 2.11/0.70    inference(superposition,[],[f1061,f481])).
% 2.11/0.70  fof(f481,plain,(
% 2.11/0.70    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)) )),
% 2.11/0.70    inference(backward_demodulation,[],[f452,f446])).
% 2.11/0.70  fof(f446,plain,(
% 2.11/0.70    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X0,X0,X1)) )),
% 2.11/0.70    inference(unit_resulting_resolution,[],[f114,f91])).
% 2.11/0.70  fof(f91,plain,(
% 2.11/0.70    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.11/0.70    inference(definition_unfolding,[],[f74,f83])).
% 2.11/0.70  fof(f83,plain,(
% 2.11/0.70    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 2.11/0.70    inference(definition_unfolding,[],[f65,f63])).
% 2.11/0.70  fof(f63,plain,(
% 2.11/0.70    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.11/0.70    inference(cnf_transformation,[],[f17])).
% 2.11/0.70  fof(f17,axiom,(
% 2.11/0.70    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.11/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.11/0.70  fof(f65,plain,(
% 2.11/0.70    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.11/0.70    inference(cnf_transformation,[],[f3])).
% 2.11/0.70  fof(f3,axiom,(
% 2.11/0.70    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.11/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.11/0.70  fof(f74,plain,(
% 2.11/0.70    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 2.11/0.70    inference(cnf_transformation,[],[f43])).
% 2.11/0.70  fof(f43,plain,(
% 2.11/0.70    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.11/0.70    inference(ennf_transformation,[],[f16])).
% 2.11/0.70  fof(f16,axiom,(
% 2.11/0.70    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 2.11/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.11/0.70  fof(f114,plain,(
% 2.11/0.70    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 2.11/0.70    inference(unit_resulting_resolution,[],[f113,f72])).
% 2.11/0.70  fof(f72,plain,(
% 2.11/0.70    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.11/0.70    inference(cnf_transformation,[],[f18])).
% 2.11/0.70  fof(f18,axiom,(
% 2.11/0.70    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.11/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 2.11/0.70  fof(f113,plain,(
% 2.11/0.70    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 2.11/0.70    inference(superposition,[],[f86,f84])).
% 2.11/0.70  fof(f84,plain,(
% 2.11/0.70    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0) )),
% 2.11/0.70    inference(definition_unfolding,[],[f53,f83])).
% 2.11/0.70  fof(f53,plain,(
% 2.11/0.70    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.11/0.70    inference(cnf_transformation,[],[f9])).
% 2.11/0.70  fof(f9,axiom,(
% 2.11/0.70    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.11/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 2.11/0.70  fof(f86,plain,(
% 2.11/0.70    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)) )),
% 2.11/0.70    inference(definition_unfolding,[],[f61,f83])).
% 2.11/0.70  fof(f61,plain,(
% 2.11/0.70    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.11/0.70    inference(cnf_transformation,[],[f7])).
% 2.11/0.70  fof(f7,axiom,(
% 2.11/0.70    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.11/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.11/0.70  fof(f452,plain,(
% 2.11/0.70    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0)))) )),
% 2.11/0.70    inference(unit_resulting_resolution,[],[f48,f91])).
% 2.11/0.70  fof(f48,plain,(
% 2.11/0.70    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.11/0.70    inference(cnf_transformation,[],[f29])).
% 2.11/0.70  fof(f29,plain,(
% 2.11/0.70    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.11/0.70    inference(flattening,[],[f28])).
% 2.11/0.70  fof(f28,plain,(
% 2.11/0.70    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.11/0.70    inference(ennf_transformation,[],[f26])).
% 2.11/0.70  fof(f26,negated_conjecture,(
% 2.11/0.70    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 2.11/0.70    inference(negated_conjecture,[],[f25])).
% 2.11/0.70  fof(f25,conjecture,(
% 2.11/0.70    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 2.11/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).
% 2.11/0.70  fof(f1061,plain,(
% 2.11/0.70    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 2.11/0.70    inference(unit_resulting_resolution,[],[f50,f48,f55])).
% 2.11/0.70  fof(f55,plain,(
% 2.11/0.70    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.11/0.70    inference(cnf_transformation,[],[f31])).
% 2.11/0.70  fof(f31,plain,(
% 2.11/0.70    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.11/0.70    inference(ennf_transformation,[],[f24])).
% 2.11/0.70  fof(f24,axiom,(
% 2.11/0.70    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.11/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).
% 2.11/0.70  fof(f50,plain,(
% 2.11/0.70    l1_pre_topc(sK0)),
% 2.11/0.70    inference(cnf_transformation,[],[f29])).
% 2.11/0.70  fof(f1715,plain,(
% 2.11/0.70    k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))),
% 2.11/0.70    inference(unit_resulting_resolution,[],[f1694,f472])).
% 2.11/0.70  fof(f472,plain,(
% 2.11/0.70    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k7_subset_1(X0,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.11/0.70    inference(backward_demodulation,[],[f90,f446])).
% 2.11/0.70  fof(f90,plain,(
% 2.11/0.70    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.11/0.70    inference(definition_unfolding,[],[f69,f83])).
% 2.11/0.70  fof(f69,plain,(
% 2.11/0.70    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 2.11/0.70    inference(cnf_transformation,[],[f39])).
% 2.11/0.70  fof(f39,plain,(
% 2.11/0.70    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.11/0.70    inference(ennf_transformation,[],[f12])).
% 2.11/0.70  fof(f12,axiom,(
% 2.11/0.70    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.11/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 2.11/0.70  fof(f1694,plain,(
% 2.11/0.70    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))),
% 2.11/0.70    inference(unit_resulting_resolution,[],[f1684,f72])).
% 2.11/0.70  fof(f1684,plain,(
% 2.11/0.70    r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 2.11/0.70    inference(unit_resulting_resolution,[],[f50,f48,f1678,f59])).
% 2.11/0.70  fof(f59,plain,(
% 2.11/0.70    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | r1_tarski(k2_tops_1(X0,X1),X1)) )),
% 2.11/0.70    inference(cnf_transformation,[],[f36])).
% 2.11/0.70  fof(f36,plain,(
% 2.11/0.70    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.11/0.70    inference(flattening,[],[f35])).
% 2.11/0.70  fof(f35,plain,(
% 2.11/0.70    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.11/0.70    inference(ennf_transformation,[],[f23])).
% 2.11/0.70  fof(f23,axiom,(
% 2.11/0.70    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 2.11/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).
% 2.11/0.70  fof(f1678,plain,(
% 2.11/0.70    v4_pre_topc(sK1,sK0)),
% 2.11/0.70    inference(global_subsumption,[],[f50,f49,f48,f1677])).
% 2.11/0.70  fof(f1677,plain,(
% 2.11/0.70    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v4_pre_topc(sK1,sK0)),
% 2.11/0.70    inference(trivial_inequality_removal,[],[f1676])).
% 2.11/0.70  fof(f1676,plain,(
% 2.11/0.70    sK1 != sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v4_pre_topc(sK1,sK0)),
% 2.11/0.70    inference(duplicate_literal_removal,[],[f1675])).
% 2.11/0.70  fof(f1675,plain,(
% 2.11/0.70    sK1 != sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v4_pre_topc(sK1,sK0) | v4_pre_topc(sK1,sK0)),
% 2.11/0.70    inference(superposition,[],[f57,f1674])).
% 2.11/0.70  fof(f1674,plain,(
% 2.11/0.70    sK1 = k2_pre_topc(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 2.11/0.70    inference(forward_demodulation,[],[f1673,f1150])).
% 2.11/0.70  fof(f1150,plain,(
% 2.11/0.70    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 2.11/0.70    inference(backward_demodulation,[],[f825,f1141])).
% 2.11/0.70  fof(f1141,plain,(
% 2.11/0.70    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 2.11/0.70    inference(unit_resulting_resolution,[],[f50,f48,f56])).
% 2.11/0.70  fof(f56,plain,(
% 2.11/0.70    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.11/0.70    inference(cnf_transformation,[],[f32])).
% 2.11/0.70  fof(f32,plain,(
% 2.11/0.70    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.11/0.70    inference(ennf_transformation,[],[f22])).
% 2.11/0.70  fof(f22,axiom,(
% 2.11/0.70    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.11/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).
% 2.11/0.70  fof(f825,plain,(
% 2.11/0.70    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 2.11/0.70    inference(unit_resulting_resolution,[],[f48,f294,f75])).
% 2.11/0.70  fof(f75,plain,(
% 2.11/0.70    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.11/0.70    inference(cnf_transformation,[],[f45])).
% 2.11/0.70  fof(f45,plain,(
% 2.11/0.70    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.11/0.70    inference(flattening,[],[f44])).
% 2.11/0.70  fof(f44,plain,(
% 2.11/0.70    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.11/0.70    inference(ennf_transformation,[],[f15])).
% 2.11/0.70  fof(f15,axiom,(
% 2.11/0.70    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 2.11/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 2.11/0.70  fof(f294,plain,(
% 2.11/0.70    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.11/0.70    inference(unit_resulting_resolution,[],[f50,f48,f71])).
% 2.11/0.70  fof(f71,plain,(
% 2.11/0.70    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.11/0.70    inference(cnf_transformation,[],[f42])).
% 2.11/0.70  fof(f42,plain,(
% 2.11/0.70    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.11/0.70    inference(flattening,[],[f41])).
% 2.11/0.70  fof(f41,plain,(
% 2.11/0.70    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.11/0.70    inference(ennf_transformation,[],[f20])).
% 2.11/0.70  fof(f20,axiom,(
% 2.11/0.70    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.11/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 2.11/0.70  fof(f1673,plain,(
% 2.11/0.70    sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 2.11/0.70    inference(superposition,[],[f1597,f1247])).
% 2.11/0.70  fof(f1247,plain,(
% 2.11/0.70    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 2.11/0.70    inference(backward_demodulation,[],[f482,f1243])).
% 2.11/0.70  fof(f1243,plain,(
% 2.11/0.70    k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))),
% 2.11/0.70    inference(unit_resulting_resolution,[],[f1231,f472])).
% 2.11/0.70  fof(f1231,plain,(
% 2.11/0.70    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))),
% 2.11/0.70    inference(unit_resulting_resolution,[],[f1217,f72])).
% 2.11/0.70  fof(f1217,plain,(
% 2.11/0.70    r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 2.11/0.70    inference(superposition,[],[f470,f1211])).
% 2.11/0.70  fof(f470,plain,(
% 2.11/0.70    ( ! [X0,X1] : (r1_tarski(k7_subset_1(X0,X0,X1),X0)) )),
% 2.11/0.70    inference(backward_demodulation,[],[f86,f446])).
% 2.11/0.70  fof(f482,plain,(
% 2.11/0.70    k2_tops_1(sK0,sK1) = k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 2.11/0.70    inference(backward_demodulation,[],[f46,f481])).
% 2.11/0.70  fof(f46,plain,(
% 2.11/0.70    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 2.11/0.70    inference(cnf_transformation,[],[f29])).
% 2.11/0.70  fof(f1597,plain,(
% 2.11/0.70    sK1 = k2_xboole_0(sK1,k3_subset_1(sK1,k1_tops_1(sK0,sK1)))),
% 2.11/0.70    inference(unit_resulting_resolution,[],[f1253,f281])).
% 2.11/0.70  fof(f281,plain,(
% 2.11/0.70    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = X2 | ~r1_tarski(X1,X2)) )),
% 2.11/0.70    inference(forward_demodulation,[],[f270,f52])).
% 2.11/0.70  fof(f52,plain,(
% 2.11/0.70    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.11/0.70    inference(cnf_transformation,[],[f4])).
% 2.11/0.70  fof(f4,axiom,(
% 2.11/0.70    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.11/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 2.11/0.70  fof(f270,plain,(
% 2.11/0.70    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = k2_xboole_0(X2,k1_xboole_0) | ~r1_tarski(X1,X2)) )),
% 2.11/0.70    inference(backward_demodulation,[],[f195,f262])).
% 2.11/0.70  fof(f262,plain,(
% 2.11/0.70    ( ! [X3] : (k1_xboole_0 = k5_xboole_0(X3,X3)) )),
% 2.11/0.70    inference(forward_demodulation,[],[f258,f128])).
% 2.11/0.70  fof(f128,plain,(
% 2.11/0.70    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.11/0.70    inference(backward_demodulation,[],[f106,f122])).
% 2.11/0.70  fof(f122,plain,(
% 2.11/0.70    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0))) )),
% 2.11/0.70    inference(unit_resulting_resolution,[],[f51,f89])).
% 2.11/0.70  fof(f89,plain,(
% 2.11/0.70    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 2.11/0.70    inference(definition_unfolding,[],[f67,f63])).
% 2.11/0.70  fof(f67,plain,(
% 2.11/0.70    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 2.11/0.70    inference(cnf_transformation,[],[f37])).
% 2.11/0.70  fof(f37,plain,(
% 2.11/0.70    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.11/0.70    inference(ennf_transformation,[],[f5])).
% 2.11/0.70  fof(f5,axiom,(
% 2.11/0.70    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.11/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.11/0.70  fof(f51,plain,(
% 2.11/0.70    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.11/0.70    inference(cnf_transformation,[],[f6])).
% 2.11/0.70  fof(f6,axiom,(
% 2.11/0.70    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.11/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.11/0.70  fof(f106,plain,(
% 2.11/0.70    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(k1_xboole_0,X0))) = X0) )),
% 2.11/0.70    inference(superposition,[],[f84,f62])).
% 2.11/0.70  fof(f62,plain,(
% 2.11/0.70    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.11/0.70    inference(cnf_transformation,[],[f11])).
% 2.11/0.70  fof(f11,axiom,(
% 2.11/0.70    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.11/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.11/0.70  fof(f258,plain,(
% 2.11/0.70    ( ! [X3] : (k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X3,k1_xboole_0))) )),
% 2.11/0.70    inference(superposition,[],[f131,f134])).
% 2.11/0.70  fof(f134,plain,(
% 2.11/0.70    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) )),
% 2.11/0.70    inference(superposition,[],[f122,f62])).
% 2.11/0.70  fof(f131,plain,(
% 2.11/0.70    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) )),
% 2.11/0.70    inference(backward_demodulation,[],[f87,f130])).
% 2.11/0.70  fof(f130,plain,(
% 2.11/0.70    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))))) )),
% 2.11/0.70    inference(forward_demodulation,[],[f120,f62])).
% 2.11/0.70  fof(f120,plain,(
% 2.11/0.70    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k1_setfam_1(k2_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0))) )),
% 2.11/0.70    inference(unit_resulting_resolution,[],[f86,f89])).
% 2.11/0.70  fof(f87,plain,(
% 2.11/0.70    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))))) )),
% 2.11/0.70    inference(definition_unfolding,[],[f64,f63,f83,f83])).
% 2.11/0.70  fof(f64,plain,(
% 2.11/0.70    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.11/0.70    inference(cnf_transformation,[],[f10])).
% 2.11/0.70  fof(f10,axiom,(
% 2.11/0.70    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.11/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.11/0.70  fof(f195,plain,(
% 2.11/0.70    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = k2_xboole_0(X2,k5_xboole_0(X1,X1)) | ~r1_tarski(X1,X2)) )),
% 2.11/0.70    inference(superposition,[],[f88,f89])).
% 2.11/0.70  fof(f88,plain,(
% 2.11/0.70    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))) )),
% 2.11/0.70    inference(definition_unfolding,[],[f66,f83])).
% 2.11/0.70  fof(f66,plain,(
% 2.11/0.70    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 2.11/0.70    inference(cnf_transformation,[],[f8])).
% 2.11/0.70  fof(f8,axiom,(
% 2.11/0.70    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 2.11/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.11/0.70  fof(f1253,plain,(
% 2.11/0.70    r1_tarski(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),sK1)),
% 2.11/0.70    inference(unit_resulting_resolution,[],[f1234,f73])).
% 2.11/0.70  fof(f73,plain,(
% 2.11/0.70    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.11/0.70    inference(cnf_transformation,[],[f18])).
% 2.11/0.70  fof(f1234,plain,(
% 2.11/0.70    m1_subset_1(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),k1_zfmisc_1(sK1))),
% 2.11/0.70    inference(unit_resulting_resolution,[],[f1231,f68])).
% 2.11/0.70  fof(f68,plain,(
% 2.11/0.70    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.11/0.70    inference(cnf_transformation,[],[f38])).
% 2.11/0.70  fof(f38,plain,(
% 2.11/0.70    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.11/0.70    inference(ennf_transformation,[],[f13])).
% 2.11/0.70  fof(f13,axiom,(
% 2.11/0.70    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.11/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 2.11/0.70  fof(f57,plain,(
% 2.11/0.70    ( ! [X0,X1] : (k2_pre_topc(X0,X1) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v4_pre_topc(X1,X0)) )),
% 2.11/0.70    inference(cnf_transformation,[],[f34])).
% 2.11/0.70  fof(f34,plain,(
% 2.11/0.70    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.11/0.70    inference(flattening,[],[f33])).
% 2.11/0.70  fof(f33,plain,(
% 2.11/0.70    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.11/0.70    inference(ennf_transformation,[],[f19])).
% 2.11/0.70  fof(f19,axiom,(
% 2.11/0.70    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 2.11/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 2.11/0.70  fof(f49,plain,(
% 2.11/0.70    v2_pre_topc(sK0)),
% 2.11/0.70    inference(cnf_transformation,[],[f29])).
% 2.11/0.70  fof(f1701,plain,(
% 2.11/0.70    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1)))),
% 2.11/0.70    inference(unit_resulting_resolution,[],[f1694,f70])).
% 2.11/0.70  fof(f70,plain,(
% 2.11/0.70    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.11/0.70    inference(cnf_transformation,[],[f40])).
% 2.11/0.70  fof(f40,plain,(
% 2.11/0.70    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.11/0.70    inference(ennf_transformation,[],[f14])).
% 2.11/0.70  fof(f14,axiom,(
% 2.11/0.70    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.11/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 2.11/0.70  fof(f1681,plain,(
% 2.11/0.70    k2_tops_1(sK0,sK1) != k3_subset_1(sK1,k1_tops_1(sK0,sK1))),
% 2.11/0.70    inference(unit_resulting_resolution,[],[f1678,f1246])).
% 2.11/0.70  fof(f1246,plain,(
% 2.11/0.70    k2_tops_1(sK0,sK1) != k3_subset_1(sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 2.11/0.70    inference(backward_demodulation,[],[f483,f1243])).
% 2.11/0.70  fof(f483,plain,(
% 2.11/0.70    k2_tops_1(sK0,sK1) != k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 2.11/0.70    inference(backward_demodulation,[],[f47,f481])).
% 2.11/0.70  fof(f47,plain,(
% 2.11/0.70    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 2.11/0.70    inference(cnf_transformation,[],[f29])).
% 2.11/0.70  % SZS output end Proof for theBenchmark
% 2.11/0.70  % (11865)------------------------------
% 2.11/0.70  % (11865)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.11/0.70  % (11865)Termination reason: Refutation
% 2.11/0.70  
% 2.11/0.70  % (11865)Memory used [KB]: 8699
% 2.11/0.70  % (11865)Time elapsed: 0.275 s
% 2.11/0.70  % (11865)------------------------------
% 2.11/0.70  % (11865)------------------------------
% 2.11/0.70  % (11840)Success in time 0.342 s
%------------------------------------------------------------------------------
