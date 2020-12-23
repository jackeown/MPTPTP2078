%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:12 EST 2020

% Result     : Theorem 2.98s
% Output     : Refutation 3.08s
% Verified   : 
% Statistics : Number of formulae       :  188 (1092 expanded)
%              Number of leaves         :   27 ( 321 expanded)
%              Depth                    :   23
%              Number of atoms          :  402 (3020 expanded)
%              Number of equality atoms :  135 (1074 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4203,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f99,f100,f3785,f3791,f4202])).

fof(f4202,plain,
    ( spl2_2
    | ~ spl2_23 ),
    inference(avatar_contradiction_clause,[],[f4201])).

fof(f4201,plain,
    ( $false
    | spl2_2
    | ~ spl2_23 ),
    inference(subsumption_resolution,[],[f4198,f98])).

fof(f98,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl2_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f4198,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_23 ),
    inference(backward_demodulation,[],[f284,f4197])).

fof(f4197,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_23 ),
    inference(backward_demodulation,[],[f262,f4154])).

fof(f4154,plain,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_23 ),
    inference(superposition,[],[f3765,f4039])).

fof(f4039,plain,
    ( k2_tops_1(sK0,sK1) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_23 ),
    inference(forward_demodulation,[],[f4035,f3818])).

fof(f3818,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_23 ),
    inference(resolution,[],[f3790,f162])).

fof(f162,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X3,X2)
      | k3_subset_1(X2,k3_subset_1(X2,X3)) = X3 ) ),
    inference(resolution,[],[f70,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f3790,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f3788])).

fof(f3788,plain,
    ( spl2_23
  <=> r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f4035,plain,
    ( k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_23 ),
    inference(superposition,[],[f3207,f3819])).

fof(f3819,plain,
    ( k3_subset_1(sK1,k2_tops_1(sK0,sK1)) = k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_23 ),
    inference(resolution,[],[f3790,f547])).

fof(f547,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X3,X2)
      | k3_subset_1(X2,X3) = k7_subset_1(X2,X2,X3) ) ),
    inference(resolution,[],[f512,f76])).

fof(f512,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k7_subset_1(X0,X0,X1) ) ),
    inference(backward_demodulation,[],[f86,f235])).

fof(f235,plain,(
    ! [X4,X3] : k7_subset_1(X3,X3,X4) = k5_xboole_0(X3,k3_xboole_0(X3,X4)) ),
    inference(resolution,[],[f87,f101])).

fof(f101,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f60,f56])).

fof(f56,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f60,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f77,f67])).

fof(f67,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f69,f67])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f3207,plain,(
    ! [X2,X1] : k3_xboole_0(X1,X2) = k3_subset_1(X1,k7_subset_1(X1,X1,X2)) ),
    inference(backward_demodulation,[],[f463,f3153])).

fof(f3153,plain,(
    ! [X30,X31] : k7_subset_1(X30,X30,X31) = k3_subset_1(X30,k3_xboole_0(X30,X31)) ),
    inference(forward_demodulation,[],[f3152,f235])).

fof(f3152,plain,(
    ! [X30,X31] : k3_subset_1(X30,k3_xboole_0(X30,X31)) = k5_xboole_0(X30,k3_xboole_0(X30,X31)) ),
    inference(forward_demodulation,[],[f3042,f463])).

fof(f3042,plain,(
    ! [X30,X31] : k3_subset_1(X30,k3_xboole_0(X30,X31)) = k5_xboole_0(X30,k3_subset_1(X30,k3_subset_1(X30,k3_xboole_0(X30,X31)))) ),
    inference(superposition,[],[f2728,f2729])).

fof(f2729,plain,(
    ! [X2,X1] : k3_subset_1(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k7_subset_1(X1,X1,X2)) ),
    inference(backward_demodulation,[],[f1294,f859])).

fof(f859,plain,(
    ! [X2,X1] : k3_subset_1(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X1,X1,k3_xboole_0(X1,X2)) ),
    inference(resolution,[],[f547,f185])).

fof(f185,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(superposition,[],[f85,f82])).

fof(f82,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f66,f67,f67])).

fof(f66,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f85,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f64,f67])).

fof(f64,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f1294,plain,(
    ! [X2,X1] : k7_subset_1(X1,X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k7_subset_1(X1,X1,X2)) ),
    inference(forward_demodulation,[],[f1293,f235])).

fof(f1293,plain,(
    ! [X2,X1] : k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k7_subset_1(X1,X1,k3_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f183,f235])).

fof(f183,plain,(
    ! [X2,X1] : k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(superposition,[],[f82,f82])).

fof(f2728,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_subset_1(X0,k3_xboole_0(X0,X1))) ),
    inference(backward_demodulation,[],[f1298,f859])).

fof(f1298,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k7_subset_1(X0,X0,k3_xboole_0(X0,X1))) ),
    inference(backward_demodulation,[],[f513,f1294])).

fof(f513,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k7_subset_1(X0,X0,X1))) ),
    inference(backward_demodulation,[],[f82,f235])).

fof(f463,plain,(
    ! [X2,X1] : k3_xboole_0(X1,X2) = k3_subset_1(X1,k3_subset_1(X1,k3_xboole_0(X1,X2))) ),
    inference(resolution,[],[f162,f185])).

fof(f3765,plain,(
    ! [X32] : sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k3_xboole_0(sK1,X32)) ),
    inference(forward_demodulation,[],[f3764,f150])).

fof(f150,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f149,f113])).

fof(f113,plain,(
    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f84,f107])).

fof(f107,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(resolution,[],[f68,f89])).

fof(f89,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
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

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f84,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f59,f67])).

fof(f59,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f149,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = X0 ),
    inference(forward_demodulation,[],[f83,f108])).

fof(f108,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1) ),
    inference(resolution,[],[f68,f103])).

fof(f103,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f75,f57])).

fof(f57,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f83,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(definition_unfolding,[],[f58,f81])).

fof(f81,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f65,f67])).

fof(f65,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f58,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f3764,plain,(
    ! [X32] : k5_xboole_0(sK1,k1_xboole_0) = k4_subset_1(u1_struct_0(sK0),sK1,k3_xboole_0(sK1,X32)) ),
    inference(forward_demodulation,[],[f3744,f2659])).

fof(f2659,plain,(
    ! [X8] : k1_xboole_0 = k7_subset_1(k3_xboole_0(sK1,X8),k3_xboole_0(sK1,X8),sK1) ),
    inference(superposition,[],[f792,f1983])).

fof(f1983,plain,(
    ! [X1] : k3_xboole_0(sK1,X1) = k7_subset_1(sK1,sK1,k7_subset_1(sK1,sK1,X1)) ),
    inference(superposition,[],[f1977,f515])).

fof(f515,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) ),
    inference(backward_demodulation,[],[f233,f235])).

fof(f233,plain,(
    ! [X0] : k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
    inference(resolution,[],[f87,f53])).

fof(f53,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f44,f46,f45])).

fof(f45,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
              | ~ v4_pre_topc(X1,X0) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
              | v4_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
            | ~ v4_pre_topc(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
            | v4_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
          | ~ v4_pre_topc(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
          | v4_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
        | ~ v4_pre_topc(sK1,sK0) )
      & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
        | v4_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

fof(f1977,plain,(
    ! [X1] : k3_xboole_0(sK1,X1) = k7_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(sK1,sK1,X1)) ),
    inference(forward_demodulation,[],[f332,f515])).

fof(f332,plain,(
    ! [X1] : k3_xboole_0(sK1,X1) = k7_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(u1_struct_0(sK0),sK1,X1)) ),
    inference(forward_demodulation,[],[f325,f233])).

fof(f325,plain,(
    ! [X1] : k3_xboole_0(sK1,X1) = k7_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,X1))) ),
    inference(superposition,[],[f233,f82])).

fof(f792,plain,(
    ! [X2,X3] : k1_xboole_0 = k7_subset_1(k7_subset_1(X2,X2,X3),k7_subset_1(X2,X2,X3),X2) ),
    inference(forward_demodulation,[],[f788,f307])).

fof(f307,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(X1,X1) ),
    inference(forward_demodulation,[],[f208,f257])).

fof(f257,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    inference(forward_demodulation,[],[f160,f207])).

fof(f207,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f204,f84])).

fof(f204,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = k3_subset_1(X0,k1_xboole_0) ),
    inference(resolution,[],[f86,f57])).

fof(f160,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) ),
    inference(resolution,[],[f70,f57])).

fof(f208,plain,(
    ! [X1] : k5_xboole_0(X1,X1) = k3_subset_1(X1,X1) ),
    inference(forward_demodulation,[],[f205,f107])).

fof(f205,plain,(
    ! [X1] : k3_subset_1(X1,X1) = k5_xboole_0(X1,k3_xboole_0(X1,X1)) ),
    inference(resolution,[],[f86,f101])).

fof(f788,plain,(
    ! [X2,X3] : k7_subset_1(k7_subset_1(X2,X2,X3),k7_subset_1(X2,X2,X3),X2) = k5_xboole_0(k7_subset_1(X2,X2,X3),k7_subset_1(X2,X2,X3)) ),
    inference(superposition,[],[f235,f532])).

fof(f532,plain,(
    ! [X10,X9] : k7_subset_1(X9,X9,X10) = k3_xboole_0(k7_subset_1(X9,X9,X10),X9) ),
    inference(resolution,[],[f514,f68])).

fof(f514,plain,(
    ! [X0,X1] : r1_tarski(k7_subset_1(X0,X0,X1),X0) ),
    inference(backward_demodulation,[],[f85,f235])).

fof(f3744,plain,(
    ! [X32] : k4_subset_1(u1_struct_0(sK0),sK1,k3_xboole_0(sK1,X32)) = k5_xboole_0(sK1,k7_subset_1(k3_xboole_0(sK1,X32),k3_xboole_0(sK1,X32),sK1)) ),
    inference(resolution,[],[f1687,f620])).

fof(f620,plain,(
    ! [X2] : r1_tarski(k3_xboole_0(sK1,X2),u1_struct_0(sK0)) ),
    inference(superposition,[],[f598,f548])).

fof(f548,plain,(
    ! [X0] : k7_subset_1(X0,X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f545,f207])).

fof(f545,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = k7_subset_1(X0,X0,k1_xboole_0) ),
    inference(resolution,[],[f512,f57])).

fof(f598,plain,(
    ! [X4,X5] : r1_tarski(k3_xboole_0(k7_subset_1(sK1,sK1,X4),X5),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f589,f89])).

fof(f589,plain,(
    ! [X4,X5] :
      ( r1_tarski(k3_xboole_0(k7_subset_1(sK1,sK1,X4),X5),u1_struct_0(sK0))
      | ~ r1_tarski(sK1,sK1) ) ),
    inference(resolution,[],[f551,f152])).

fof(f152,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | r1_tarski(X1,u1_struct_0(sK0))
      | ~ r1_tarski(X0,sK1) ) ),
    inference(resolution,[],[f143,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f143,plain,(
    ! [X7] :
      ( r1_tarski(X7,u1_struct_0(sK0))
      | ~ r1_tarski(X7,sK1) ) ),
    inference(resolution,[],[f79,f102])).

fof(f102,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f75,f53])).

fof(f551,plain,(
    ! [X2,X1] : r1_tarski(k3_xboole_0(k7_subset_1(sK1,sK1,X1),X2),sK1) ),
    inference(backward_demodulation,[],[f486,f515])).

fof(f486,plain,(
    ! [X2,X1] : r1_tarski(k3_xboole_0(k7_subset_1(u1_struct_0(sK0),sK1,X1),X2),sK1) ),
    inference(resolution,[],[f439,f185])).

fof(f439,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(X5,k7_subset_1(u1_struct_0(sK0),sK1,X4))
      | r1_tarski(X5,sK1) ) ),
    inference(superposition,[],[f142,f233])).

fof(f142,plain,(
    ! [X6,X4,X5] :
      ( ~ r1_tarski(X4,k5_xboole_0(X5,k3_xboole_0(X5,X6)))
      | r1_tarski(X4,X5) ) ),
    inference(resolution,[],[f79,f85])).

fof(f1687,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_struct_0(sK0))
      | k4_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1)) ) ),
    inference(resolution,[],[f643,f53])).

fof(f643,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(X5))
      | k4_subset_1(X5,X6,X7) = k5_xboole_0(X6,k7_subset_1(X7,X7,X6))
      | ~ r1_tarski(X7,X5) ) ),
    inference(resolution,[],[f510,f76])).

fof(f510,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k5_xboole_0(X1,k7_subset_1(X2,X2,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(backward_demodulation,[],[f88,f235])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f80,f81])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f262,plain,(
    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f258,f52])).

fof(f52,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f258,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f61,f53])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(f284,plain,(
    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f280,f52])).

fof(f280,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f62,f53])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(f3791,plain,
    ( spl2_23
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f3786,f92,f3788])).

fof(f92,plain,
    ( spl2_1
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f3786,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f240,f52])).

fof(f240,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f63,f53])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | r1_tarski(k2_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

fof(f3785,plain,
    ( spl2_1
    | ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f3784])).

fof(f3784,plain,
    ( $false
    | spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f3783,f102])).

fof(f3783,plain,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f3782,f51])).

fof(f51,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f3782,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ r1_tarski(sK1,u1_struct_0(sK0))
    | spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f3781,f52])).

fof(f3781,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ r1_tarski(sK1,u1_struct_0(sK0))
    | spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f3778,f94])).

fof(f94,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f92])).

fof(f3778,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl2_2 ),
    inference(superposition,[],[f222,f3775])).

fof(f3775,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f262,f3769])).

fof(f3769,plain,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f3768,f150])).

fof(f3768,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_xboole_0)
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f3751,f526])).

fof(f526,plain,
    ( k1_xboole_0 = k7_subset_1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f519,f307])).

fof(f519,plain,
    ( k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k7_subset_1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_2 ),
    inference(superposition,[],[f235,f342])).

fof(f342,plain,
    ( k2_tops_1(sK0,sK1) = k3_xboole_0(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_2 ),
    inference(resolution,[],[f338,f68])).

fof(f338,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_2 ),
    inference(superposition,[],[f328,f97])).

fof(f97,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f96])).

fof(f328,plain,(
    ! [X2] : r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X2),sK1) ),
    inference(superposition,[],[f85,f233])).

fof(f3751,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k7_subset_1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1))
    | ~ spl2_2 ),
    inference(resolution,[],[f1687,f383])).

fof(f383,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f380,f89])).

fof(f380,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ r1_tarski(sK1,sK1)
    | ~ spl2_2 ),
    inference(resolution,[],[f152,f338])).

fof(f222,plain,(
    ! [X2,X3] :
      ( v4_pre_topc(k2_pre_topc(X2,X3),X2)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ r1_tarski(X3,u1_struct_0(X2)) ) ),
    inference(resolution,[],[f71,f76])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

fof(f100,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f54,f96,f92])).

fof(f54,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f99,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f55,f96,f92])).

fof(f55,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f47])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:12:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.48  % (8551)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.49  % (8559)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.51  % (8545)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.51  % (8555)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.51  % (8542)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.51  % (8554)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.52  % (8570)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.32/0.52  % (8567)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.32/0.53  % (8564)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.32/0.53  % (8552)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.32/0.53  % (8544)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.32/0.53  % (8556)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.32/0.53  % (8543)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.32/0.53  % (8562)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.32/0.53  % (8553)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.32/0.53  % (8563)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.32/0.53  % (8543)Refutation not found, incomplete strategy% (8543)------------------------------
% 1.32/0.53  % (8543)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.53  % (8543)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.53  
% 1.32/0.53  % (8543)Memory used [KB]: 1791
% 1.32/0.53  % (8543)Time elapsed: 0.119 s
% 1.32/0.53  % (8543)------------------------------
% 1.32/0.53  % (8543)------------------------------
% 1.32/0.53  % (8565)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.32/0.53  % (8546)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.32/0.53  % (8557)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.32/0.53  % (8566)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.32/0.54  % (8568)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.32/0.54  % (8550)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.32/0.54  % (8569)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.32/0.54  % (8547)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.42/0.54  % (8560)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.42/0.55  % (8561)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.42/0.55  % (8571)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.42/0.55  % (8558)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.42/0.55  % (8571)Refutation not found, incomplete strategy% (8571)------------------------------
% 1.42/0.55  % (8571)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (8571)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.55  
% 1.42/0.55  % (8571)Memory used [KB]: 1663
% 1.42/0.55  % (8571)Time elapsed: 0.142 s
% 1.42/0.55  % (8571)------------------------------
% 1.42/0.55  % (8571)------------------------------
% 1.42/0.55  % (8549)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.42/0.55  % (8548)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.42/0.57  % (8568)Refutation not found, incomplete strategy% (8568)------------------------------
% 1.42/0.57  % (8568)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.59  % (8568)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.59  
% 1.42/0.59  % (8568)Memory used [KB]: 6652
% 1.42/0.59  % (8568)Time elapsed: 0.165 s
% 1.42/0.59  % (8568)------------------------------
% 1.42/0.59  % (8568)------------------------------
% 2.03/0.68  % (8545)Refutation not found, incomplete strategy% (8545)------------------------------
% 2.03/0.68  % (8545)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.43/0.69  % (8572)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.43/0.69  % (8545)Termination reason: Refutation not found, incomplete strategy
% 2.43/0.69  
% 2.43/0.69  % (8545)Memory used [KB]: 6140
% 2.43/0.69  % (8545)Time elapsed: 0.253 s
% 2.43/0.69  % (8545)------------------------------
% 2.43/0.69  % (8545)------------------------------
% 2.43/0.70  % (8573)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.43/0.73  % (8574)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.43/0.73  % (8574)Refutation not found, incomplete strategy% (8574)------------------------------
% 2.43/0.73  % (8574)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.43/0.75  % (8574)Termination reason: Refutation not found, incomplete strategy
% 2.43/0.75  
% 2.43/0.75  % (8574)Memory used [KB]: 6140
% 2.43/0.75  % (8574)Time elapsed: 0.094 s
% 2.43/0.75  % (8574)------------------------------
% 2.43/0.75  % (8574)------------------------------
% 2.98/0.77  % (8548)Refutation found. Thanks to Tanya!
% 2.98/0.77  % SZS status Theorem for theBenchmark
% 2.98/0.77  % SZS output start Proof for theBenchmark
% 2.98/0.77  fof(f4203,plain,(
% 2.98/0.77    $false),
% 2.98/0.77    inference(avatar_sat_refutation,[],[f99,f100,f3785,f3791,f4202])).
% 2.98/0.77  fof(f4202,plain,(
% 2.98/0.77    spl2_2 | ~spl2_23),
% 2.98/0.77    inference(avatar_contradiction_clause,[],[f4201])).
% 2.98/0.77  fof(f4201,plain,(
% 2.98/0.77    $false | (spl2_2 | ~spl2_23)),
% 2.98/0.77    inference(subsumption_resolution,[],[f4198,f98])).
% 2.98/0.77  fof(f98,plain,(
% 2.98/0.77    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | spl2_2),
% 2.98/0.77    inference(avatar_component_clause,[],[f96])).
% 2.98/0.77  fof(f96,plain,(
% 2.98/0.77    spl2_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 2.98/0.77    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 2.98/0.77  fof(f4198,plain,(
% 2.98/0.77    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_23),
% 2.98/0.77    inference(backward_demodulation,[],[f284,f4197])).
% 2.98/0.77  fof(f4197,plain,(
% 2.98/0.77    sK1 = k2_pre_topc(sK0,sK1) | ~spl2_23),
% 2.98/0.77    inference(backward_demodulation,[],[f262,f4154])).
% 2.98/0.77  fof(f4154,plain,(
% 2.98/0.77    sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_23),
% 2.98/0.77    inference(superposition,[],[f3765,f4039])).
% 2.98/0.77  fof(f4039,plain,(
% 2.98/0.77    k2_tops_1(sK0,sK1) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_23),
% 2.98/0.77    inference(forward_demodulation,[],[f4035,f3818])).
% 2.98/0.77  fof(f3818,plain,(
% 2.98/0.77    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) | ~spl2_23),
% 2.98/0.77    inference(resolution,[],[f3790,f162])).
% 2.98/0.77  fof(f162,plain,(
% 2.98/0.77    ( ! [X2,X3] : (~r1_tarski(X3,X2) | k3_subset_1(X2,k3_subset_1(X2,X3)) = X3) )),
% 2.98/0.77    inference(resolution,[],[f70,f76])).
% 2.98/0.77  fof(f76,plain,(
% 2.98/0.77    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.98/0.77    inference(cnf_transformation,[],[f50])).
% 2.98/0.77  fof(f50,plain,(
% 2.98/0.77    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.98/0.77    inference(nnf_transformation,[],[f17])).
% 2.98/0.77  fof(f17,axiom,(
% 2.98/0.77    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.98/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 2.98/0.77  fof(f70,plain,(
% 2.98/0.77    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 2.98/0.77    inference(cnf_transformation,[],[f33])).
% 2.98/0.77  fof(f33,plain,(
% 2.98/0.77    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.98/0.77    inference(ennf_transformation,[],[f13])).
% 2.98/0.77  fof(f13,axiom,(
% 2.98/0.77    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.98/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 2.98/0.77  fof(f3790,plain,(
% 2.98/0.77    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl2_23),
% 2.98/0.77    inference(avatar_component_clause,[],[f3788])).
% 2.98/0.77  fof(f3788,plain,(
% 2.98/0.77    spl2_23 <=> r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 2.98/0.77    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 2.98/0.77  fof(f4035,plain,(
% 2.98/0.77    k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_23),
% 2.98/0.77    inference(superposition,[],[f3207,f3819])).
% 2.98/0.77  fof(f3819,plain,(
% 2.98/0.77    k3_subset_1(sK1,k2_tops_1(sK0,sK1)) = k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) | ~spl2_23),
% 2.98/0.77    inference(resolution,[],[f3790,f547])).
% 2.98/0.77  fof(f547,plain,(
% 2.98/0.77    ( ! [X2,X3] : (~r1_tarski(X3,X2) | k3_subset_1(X2,X3) = k7_subset_1(X2,X2,X3)) )),
% 2.98/0.77    inference(resolution,[],[f512,f76])).
% 2.98/0.77  fof(f512,plain,(
% 2.98/0.77    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k7_subset_1(X0,X0,X1)) )),
% 2.98/0.77    inference(backward_demodulation,[],[f86,f235])).
% 2.98/0.77  fof(f235,plain,(
% 2.98/0.77    ( ! [X4,X3] : (k7_subset_1(X3,X3,X4) = k5_xboole_0(X3,k3_xboole_0(X3,X4))) )),
% 2.98/0.77    inference(resolution,[],[f87,f101])).
% 2.98/0.77  fof(f101,plain,(
% 2.98/0.77    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 2.98/0.77    inference(forward_demodulation,[],[f60,f56])).
% 2.98/0.77  fof(f56,plain,(
% 2.98/0.77    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.98/0.77    inference(cnf_transformation,[],[f10])).
% 2.98/0.77  fof(f10,axiom,(
% 2.98/0.77    ! [X0] : k2_subset_1(X0) = X0),
% 2.98/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 2.98/0.77  fof(f60,plain,(
% 2.98/0.77    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.98/0.77    inference(cnf_transformation,[],[f12])).
% 2.98/0.77  fof(f12,axiom,(
% 2.98/0.77    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 2.98/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 2.98/0.77  fof(f87,plain,(
% 2.98/0.77    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2))) )),
% 2.98/0.77    inference(definition_unfolding,[],[f77,f67])).
% 2.98/0.77  fof(f67,plain,(
% 2.98/0.77    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.98/0.77    inference(cnf_transformation,[],[f2])).
% 2.98/0.77  fof(f2,axiom,(
% 2.98/0.77    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.98/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.98/0.77  fof(f77,plain,(
% 2.98/0.77    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.98/0.77    inference(cnf_transformation,[],[f36])).
% 2.98/0.77  fof(f36,plain,(
% 2.98/0.77    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.98/0.77    inference(ennf_transformation,[],[f15])).
% 2.98/0.77  fof(f15,axiom,(
% 2.98/0.77    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 2.98/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.98/0.77  fof(f86,plain,(
% 2.98/0.77    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 2.98/0.77    inference(definition_unfolding,[],[f69,f67])).
% 2.98/0.77  fof(f69,plain,(
% 2.98/0.77    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.98/0.77    inference(cnf_transformation,[],[f32])).
% 2.98/0.77  fof(f32,plain,(
% 2.98/0.77    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.98/0.77    inference(ennf_transformation,[],[f11])).
% 2.98/0.77  fof(f11,axiom,(
% 2.98/0.77    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.98/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 2.98/0.77  fof(f3207,plain,(
% 2.98/0.77    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = k3_subset_1(X1,k7_subset_1(X1,X1,X2))) )),
% 2.98/0.77    inference(backward_demodulation,[],[f463,f3153])).
% 2.98/0.77  fof(f3153,plain,(
% 2.98/0.77    ( ! [X30,X31] : (k7_subset_1(X30,X30,X31) = k3_subset_1(X30,k3_xboole_0(X30,X31))) )),
% 2.98/0.77    inference(forward_demodulation,[],[f3152,f235])).
% 2.98/0.77  fof(f3152,plain,(
% 2.98/0.77    ( ! [X30,X31] : (k3_subset_1(X30,k3_xboole_0(X30,X31)) = k5_xboole_0(X30,k3_xboole_0(X30,X31))) )),
% 2.98/0.77    inference(forward_demodulation,[],[f3042,f463])).
% 2.98/0.77  fof(f3042,plain,(
% 2.98/0.77    ( ! [X30,X31] : (k3_subset_1(X30,k3_xboole_0(X30,X31)) = k5_xboole_0(X30,k3_subset_1(X30,k3_subset_1(X30,k3_xboole_0(X30,X31))))) )),
% 2.98/0.77    inference(superposition,[],[f2728,f2729])).
% 2.98/0.77  fof(f2729,plain,(
% 2.98/0.77    ( ! [X2,X1] : (k3_subset_1(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k7_subset_1(X1,X1,X2))) )),
% 2.98/0.77    inference(backward_demodulation,[],[f1294,f859])).
% 2.98/0.77  fof(f859,plain,(
% 2.98/0.77    ( ! [X2,X1] : (k3_subset_1(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X1,X1,k3_xboole_0(X1,X2))) )),
% 2.98/0.77    inference(resolution,[],[f547,f185])).
% 2.98/0.77  fof(f185,plain,(
% 2.98/0.77    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.98/0.77    inference(superposition,[],[f85,f82])).
% 2.98/0.77  fof(f82,plain,(
% 2.98/0.77    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 2.98/0.77    inference(definition_unfolding,[],[f66,f67,f67])).
% 2.98/0.77  fof(f66,plain,(
% 2.98/0.77    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.98/0.77    inference(cnf_transformation,[],[f8])).
% 2.98/0.77  fof(f8,axiom,(
% 2.98/0.77    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.98/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.98/0.77  fof(f85,plain,(
% 2.98/0.77    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 2.98/0.77    inference(definition_unfolding,[],[f64,f67])).
% 2.98/0.77  fof(f64,plain,(
% 2.98/0.77    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.98/0.77    inference(cnf_transformation,[],[f6])).
% 2.98/0.77  fof(f6,axiom,(
% 2.98/0.77    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.98/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.98/0.77  fof(f1294,plain,(
% 2.98/0.77    ( ! [X2,X1] : (k7_subset_1(X1,X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k7_subset_1(X1,X1,X2))) )),
% 2.98/0.77    inference(forward_demodulation,[],[f1293,f235])).
% 2.98/0.77  fof(f1293,plain,(
% 2.98/0.77    ( ! [X2,X1] : (k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k7_subset_1(X1,X1,k3_xboole_0(X1,X2))) )),
% 2.98/0.77    inference(forward_demodulation,[],[f183,f235])).
% 2.98/0.77  fof(f183,plain,(
% 2.98/0.77    ( ! [X2,X1] : (k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2)))) )),
% 2.98/0.77    inference(superposition,[],[f82,f82])).
% 2.98/0.77  fof(f2728,plain,(
% 2.98/0.77    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_subset_1(X0,k3_xboole_0(X0,X1)))) )),
% 2.98/0.77    inference(backward_demodulation,[],[f1298,f859])).
% 2.98/0.77  fof(f1298,plain,(
% 2.98/0.77    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k7_subset_1(X0,X0,k3_xboole_0(X0,X1)))) )),
% 2.98/0.77    inference(backward_demodulation,[],[f513,f1294])).
% 2.98/0.77  fof(f513,plain,(
% 2.98/0.77    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k7_subset_1(X0,X0,X1)))) )),
% 2.98/0.77    inference(backward_demodulation,[],[f82,f235])).
% 2.98/0.77  fof(f463,plain,(
% 2.98/0.77    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = k3_subset_1(X1,k3_subset_1(X1,k3_xboole_0(X1,X2)))) )),
% 2.98/0.77    inference(resolution,[],[f162,f185])).
% 2.98/0.77  fof(f3765,plain,(
% 2.98/0.77    ( ! [X32] : (sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k3_xboole_0(sK1,X32))) )),
% 2.98/0.77    inference(forward_demodulation,[],[f3764,f150])).
% 2.98/0.77  fof(f150,plain,(
% 2.98/0.77    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.98/0.77    inference(forward_demodulation,[],[f149,f113])).
% 2.98/0.77  fof(f113,plain,(
% 2.98/0.77    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 2.98/0.77    inference(superposition,[],[f84,f107])).
% 2.98/0.77  fof(f107,plain,(
% 2.98/0.77    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.98/0.77    inference(resolution,[],[f68,f89])).
% 2.98/0.77  fof(f89,plain,(
% 2.98/0.77    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.98/0.77    inference(equality_resolution,[],[f73])).
% 2.98/0.77  fof(f73,plain,(
% 2.98/0.77    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.98/0.77    inference(cnf_transformation,[],[f49])).
% 2.98/0.77  fof(f49,plain,(
% 2.98/0.77    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.98/0.77    inference(flattening,[],[f48])).
% 2.98/0.77  fof(f48,plain,(
% 2.98/0.77    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.98/0.77    inference(nnf_transformation,[],[f1])).
% 2.98/0.77  fof(f1,axiom,(
% 2.98/0.77    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.98/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.98/0.77  fof(f68,plain,(
% 2.98/0.77    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 2.98/0.77    inference(cnf_transformation,[],[f31])).
% 2.98/0.77  fof(f31,plain,(
% 2.98/0.77    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.98/0.77    inference(ennf_transformation,[],[f5])).
% 2.98/0.77  fof(f5,axiom,(
% 2.98/0.77    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.98/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.98/0.77  fof(f84,plain,(
% 2.98/0.77    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 2.98/0.77    inference(definition_unfolding,[],[f59,f67])).
% 2.98/0.77  fof(f59,plain,(
% 2.98/0.77    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.98/0.77    inference(cnf_transformation,[],[f7])).
% 2.98/0.77  fof(f7,axiom,(
% 2.98/0.77    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.98/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 2.98/0.77  fof(f149,plain,(
% 2.98/0.77    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = X0) )),
% 2.98/0.77    inference(forward_demodulation,[],[f83,f108])).
% 2.98/0.77  fof(f108,plain,(
% 2.98/0.77    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1)) )),
% 2.98/0.77    inference(resolution,[],[f68,f103])).
% 2.98/0.77  fof(f103,plain,(
% 2.98/0.77    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.98/0.77    inference(resolution,[],[f75,f57])).
% 2.98/0.77  fof(f57,plain,(
% 2.98/0.77    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.98/0.77    inference(cnf_transformation,[],[f16])).
% 2.98/0.77  fof(f16,axiom,(
% 2.98/0.77    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.98/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 2.98/0.77  fof(f75,plain,(
% 2.98/0.77    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.98/0.77    inference(cnf_transformation,[],[f50])).
% 2.98/0.77  fof(f83,plain,(
% 2.98/0.77    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0) )),
% 2.98/0.77    inference(definition_unfolding,[],[f58,f81])).
% 2.98/0.77  fof(f81,plain,(
% 2.98/0.77    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 2.98/0.77    inference(definition_unfolding,[],[f65,f67])).
% 2.98/0.77  fof(f65,plain,(
% 2.98/0.77    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.98/0.77    inference(cnf_transformation,[],[f9])).
% 2.98/0.77  fof(f9,axiom,(
% 2.98/0.77    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.98/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.98/0.77  fof(f58,plain,(
% 2.98/0.77    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.98/0.77    inference(cnf_transformation,[],[f3])).
% 2.98/0.77  fof(f3,axiom,(
% 2.98/0.77    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.98/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 2.98/0.77  fof(f3764,plain,(
% 2.98/0.77    ( ! [X32] : (k5_xboole_0(sK1,k1_xboole_0) = k4_subset_1(u1_struct_0(sK0),sK1,k3_xboole_0(sK1,X32))) )),
% 2.98/0.77    inference(forward_demodulation,[],[f3744,f2659])).
% 2.98/0.77  fof(f2659,plain,(
% 2.98/0.77    ( ! [X8] : (k1_xboole_0 = k7_subset_1(k3_xboole_0(sK1,X8),k3_xboole_0(sK1,X8),sK1)) )),
% 2.98/0.77    inference(superposition,[],[f792,f1983])).
% 2.98/0.77  fof(f1983,plain,(
% 2.98/0.77    ( ! [X1] : (k3_xboole_0(sK1,X1) = k7_subset_1(sK1,sK1,k7_subset_1(sK1,sK1,X1))) )),
% 2.98/0.77    inference(superposition,[],[f1977,f515])).
% 2.98/0.77  fof(f515,plain,(
% 2.98/0.77    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)) )),
% 2.98/0.77    inference(backward_demodulation,[],[f233,f235])).
% 2.98/0.77  fof(f233,plain,(
% 2.98/0.77    ( ! [X0] : (k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) = k7_subset_1(u1_struct_0(sK0),sK1,X0)) )),
% 2.98/0.77    inference(resolution,[],[f87,f53])).
% 2.98/0.77  fof(f53,plain,(
% 2.98/0.77    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.98/0.77    inference(cnf_transformation,[],[f47])).
% 2.98/0.77  fof(f47,plain,(
% 2.98/0.77    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 2.98/0.77    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f44,f46,f45])).
% 2.98/0.77  fof(f45,plain,(
% 2.98/0.77    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 2.98/0.77    introduced(choice_axiom,[])).
% 2.98/0.77  fof(f46,plain,(
% 2.98/0.77    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.98/0.77    introduced(choice_axiom,[])).
% 2.98/0.77  fof(f44,plain,(
% 2.98/0.77    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.98/0.77    inference(flattening,[],[f43])).
% 2.98/0.77  fof(f43,plain,(
% 2.98/0.77    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.98/0.77    inference(nnf_transformation,[],[f26])).
% 2.98/0.77  fof(f26,plain,(
% 2.98/0.77    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.98/0.77    inference(flattening,[],[f25])).
% 2.98/0.77  fof(f25,plain,(
% 2.98/0.77    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.08/0.77    inference(ennf_transformation,[],[f24])).
% 3.08/0.77  fof(f24,negated_conjecture,(
% 3.08/0.77    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 3.08/0.77    inference(negated_conjecture,[],[f23])).
% 3.08/0.77  fof(f23,conjecture,(
% 3.08/0.77    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 3.08/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).
% 3.08/0.77  fof(f1977,plain,(
% 3.08/0.77    ( ! [X1] : (k3_xboole_0(sK1,X1) = k7_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(sK1,sK1,X1))) )),
% 3.08/0.77    inference(forward_demodulation,[],[f332,f515])).
% 3.08/0.77  fof(f332,plain,(
% 3.08/0.77    ( ! [X1] : (k3_xboole_0(sK1,X1) = k7_subset_1(u1_struct_0(sK0),sK1,k7_subset_1(u1_struct_0(sK0),sK1,X1))) )),
% 3.08/0.77    inference(forward_demodulation,[],[f325,f233])).
% 3.08/0.77  fof(f325,plain,(
% 3.08/0.77    ( ! [X1] : (k3_xboole_0(sK1,X1) = k7_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,X1)))) )),
% 3.08/0.77    inference(superposition,[],[f233,f82])).
% 3.08/0.77  fof(f792,plain,(
% 3.08/0.77    ( ! [X2,X3] : (k1_xboole_0 = k7_subset_1(k7_subset_1(X2,X2,X3),k7_subset_1(X2,X2,X3),X2)) )),
% 3.08/0.77    inference(forward_demodulation,[],[f788,f307])).
% 3.08/0.77  fof(f307,plain,(
% 3.08/0.77    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,X1)) )),
% 3.08/0.77    inference(forward_demodulation,[],[f208,f257])).
% 3.08/0.77  fof(f257,plain,(
% 3.08/0.77    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0)) )),
% 3.08/0.77    inference(forward_demodulation,[],[f160,f207])).
% 3.08/0.77  fof(f207,plain,(
% 3.08/0.77    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 3.08/0.77    inference(forward_demodulation,[],[f204,f84])).
% 3.08/0.77  fof(f204,plain,(
% 3.08/0.77    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = k3_subset_1(X0,k1_xboole_0)) )),
% 3.08/0.77    inference(resolution,[],[f86,f57])).
% 3.08/0.77  fof(f160,plain,(
% 3.08/0.77    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0))) )),
% 3.08/0.77    inference(resolution,[],[f70,f57])).
% 3.08/0.77  fof(f208,plain,(
% 3.08/0.77    ( ! [X1] : (k5_xboole_0(X1,X1) = k3_subset_1(X1,X1)) )),
% 3.08/0.77    inference(forward_demodulation,[],[f205,f107])).
% 3.08/0.77  fof(f205,plain,(
% 3.08/0.77    ( ! [X1] : (k3_subset_1(X1,X1) = k5_xboole_0(X1,k3_xboole_0(X1,X1))) )),
% 3.08/0.77    inference(resolution,[],[f86,f101])).
% 3.08/0.77  fof(f788,plain,(
% 3.08/0.77    ( ! [X2,X3] : (k7_subset_1(k7_subset_1(X2,X2,X3),k7_subset_1(X2,X2,X3),X2) = k5_xboole_0(k7_subset_1(X2,X2,X3),k7_subset_1(X2,X2,X3))) )),
% 3.08/0.77    inference(superposition,[],[f235,f532])).
% 3.08/0.77  fof(f532,plain,(
% 3.08/0.77    ( ! [X10,X9] : (k7_subset_1(X9,X9,X10) = k3_xboole_0(k7_subset_1(X9,X9,X10),X9)) )),
% 3.08/0.77    inference(resolution,[],[f514,f68])).
% 3.08/0.77  fof(f514,plain,(
% 3.08/0.77    ( ! [X0,X1] : (r1_tarski(k7_subset_1(X0,X0,X1),X0)) )),
% 3.08/0.77    inference(backward_demodulation,[],[f85,f235])).
% 3.08/0.77  fof(f3744,plain,(
% 3.08/0.77    ( ! [X32] : (k4_subset_1(u1_struct_0(sK0),sK1,k3_xboole_0(sK1,X32)) = k5_xboole_0(sK1,k7_subset_1(k3_xboole_0(sK1,X32),k3_xboole_0(sK1,X32),sK1))) )),
% 3.08/0.77    inference(resolution,[],[f1687,f620])).
% 3.08/0.77  fof(f620,plain,(
% 3.08/0.77    ( ! [X2] : (r1_tarski(k3_xboole_0(sK1,X2),u1_struct_0(sK0))) )),
% 3.08/0.77    inference(superposition,[],[f598,f548])).
% 3.08/0.77  fof(f548,plain,(
% 3.08/0.77    ( ! [X0] : (k7_subset_1(X0,X0,k1_xboole_0) = X0) )),
% 3.08/0.77    inference(forward_demodulation,[],[f545,f207])).
% 3.08/0.77  fof(f545,plain,(
% 3.08/0.77    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = k7_subset_1(X0,X0,k1_xboole_0)) )),
% 3.08/0.77    inference(resolution,[],[f512,f57])).
% 3.08/0.77  fof(f598,plain,(
% 3.08/0.77    ( ! [X4,X5] : (r1_tarski(k3_xboole_0(k7_subset_1(sK1,sK1,X4),X5),u1_struct_0(sK0))) )),
% 3.08/0.77    inference(subsumption_resolution,[],[f589,f89])).
% 3.08/0.77  fof(f589,plain,(
% 3.08/0.77    ( ! [X4,X5] : (r1_tarski(k3_xboole_0(k7_subset_1(sK1,sK1,X4),X5),u1_struct_0(sK0)) | ~r1_tarski(sK1,sK1)) )),
% 3.08/0.77    inference(resolution,[],[f551,f152])).
% 3.08/0.77  fof(f152,plain,(
% 3.08/0.77    ( ! [X0,X1] : (~r1_tarski(X1,X0) | r1_tarski(X1,u1_struct_0(sK0)) | ~r1_tarski(X0,sK1)) )),
% 3.08/0.77    inference(resolution,[],[f143,f79])).
% 3.08/0.77  fof(f79,plain,(
% 3.08/0.77    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.08/0.77    inference(cnf_transformation,[],[f40])).
% 3.08/0.77  fof(f40,plain,(
% 3.08/0.77    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.08/0.77    inference(flattening,[],[f39])).
% 3.08/0.77  fof(f39,plain,(
% 3.08/0.77    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.08/0.77    inference(ennf_transformation,[],[f4])).
% 3.08/0.77  fof(f4,axiom,(
% 3.08/0.77    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.08/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 3.08/0.77  fof(f143,plain,(
% 3.08/0.77    ( ! [X7] : (r1_tarski(X7,u1_struct_0(sK0)) | ~r1_tarski(X7,sK1)) )),
% 3.08/0.77    inference(resolution,[],[f79,f102])).
% 3.08/0.77  fof(f102,plain,(
% 3.08/0.77    r1_tarski(sK1,u1_struct_0(sK0))),
% 3.08/0.77    inference(resolution,[],[f75,f53])).
% 3.08/0.77  fof(f551,plain,(
% 3.08/0.77    ( ! [X2,X1] : (r1_tarski(k3_xboole_0(k7_subset_1(sK1,sK1,X1),X2),sK1)) )),
% 3.08/0.77    inference(backward_demodulation,[],[f486,f515])).
% 3.08/0.77  fof(f486,plain,(
% 3.08/0.77    ( ! [X2,X1] : (r1_tarski(k3_xboole_0(k7_subset_1(u1_struct_0(sK0),sK1,X1),X2),sK1)) )),
% 3.08/0.77    inference(resolution,[],[f439,f185])).
% 3.08/0.77  fof(f439,plain,(
% 3.08/0.77    ( ! [X4,X5] : (~r1_tarski(X5,k7_subset_1(u1_struct_0(sK0),sK1,X4)) | r1_tarski(X5,sK1)) )),
% 3.08/0.77    inference(superposition,[],[f142,f233])).
% 3.08/0.77  fof(f142,plain,(
% 3.08/0.77    ( ! [X6,X4,X5] : (~r1_tarski(X4,k5_xboole_0(X5,k3_xboole_0(X5,X6))) | r1_tarski(X4,X5)) )),
% 3.08/0.77    inference(resolution,[],[f79,f85])).
% 3.08/0.77  fof(f1687,plain,(
% 3.08/0.77    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK0)) | k4_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1))) )),
% 3.08/0.77    inference(resolution,[],[f643,f53])).
% 3.08/0.77  fof(f643,plain,(
% 3.08/0.77    ( ! [X6,X7,X5] : (~m1_subset_1(X6,k1_zfmisc_1(X5)) | k4_subset_1(X5,X6,X7) = k5_xboole_0(X6,k7_subset_1(X7,X7,X6)) | ~r1_tarski(X7,X5)) )),
% 3.08/0.77    inference(resolution,[],[f510,f76])).
% 3.08/0.77  fof(f510,plain,(
% 3.08/0.77    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k5_xboole_0(X1,k7_subset_1(X2,X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.08/0.77    inference(backward_demodulation,[],[f88,f235])).
% 3.08/0.77  fof(f88,plain,(
% 3.08/0.77    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.08/0.77    inference(definition_unfolding,[],[f80,f81])).
% 3.08/0.77  fof(f80,plain,(
% 3.08/0.77    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.08/0.77    inference(cnf_transformation,[],[f42])).
% 3.08/0.77  fof(f42,plain,(
% 3.08/0.77    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.08/0.77    inference(flattening,[],[f41])).
% 3.08/0.77  fof(f41,plain,(
% 3.08/0.77    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.08/0.77    inference(ennf_transformation,[],[f14])).
% 3.08/0.77  fof(f14,axiom,(
% 3.08/0.77    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 3.08/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 3.08/0.77  fof(f262,plain,(
% 3.08/0.77    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 3.08/0.77    inference(subsumption_resolution,[],[f258,f52])).
% 3.08/0.77  fof(f52,plain,(
% 3.08/0.77    l1_pre_topc(sK0)),
% 3.08/0.77    inference(cnf_transformation,[],[f47])).
% 3.08/0.77  fof(f258,plain,(
% 3.08/0.77    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 3.08/0.77    inference(resolution,[],[f61,f53])).
% 3.08/0.77  fof(f61,plain,(
% 3.08/0.77    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 3.08/0.77    inference(cnf_transformation,[],[f27])).
% 3.08/0.77  fof(f27,plain,(
% 3.08/0.77    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.08/0.77    inference(ennf_transformation,[],[f21])).
% 3.08/0.77  fof(f21,axiom,(
% 3.08/0.77    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 3.08/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).
% 3.08/0.77  fof(f284,plain,(
% 3.08/0.77    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 3.08/0.77    inference(subsumption_resolution,[],[f280,f52])).
% 3.08/0.77  fof(f280,plain,(
% 3.08/0.77    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 3.08/0.77    inference(resolution,[],[f62,f53])).
% 3.08/0.77  fof(f62,plain,(
% 3.08/0.77    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 3.08/0.77    inference(cnf_transformation,[],[f28])).
% 3.08/0.77  fof(f28,plain,(
% 3.08/0.77    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.08/0.77    inference(ennf_transformation,[],[f20])).
% 3.08/0.77  fof(f20,axiom,(
% 3.08/0.77    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 3.08/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 3.08/0.77  fof(f3791,plain,(
% 3.08/0.77    spl2_23 | ~spl2_1),
% 3.08/0.77    inference(avatar_split_clause,[],[f3786,f92,f3788])).
% 3.08/0.77  fof(f92,plain,(
% 3.08/0.77    spl2_1 <=> v4_pre_topc(sK1,sK0)),
% 3.08/0.77    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 3.08/0.77  fof(f3786,plain,(
% 3.08/0.77    ~v4_pre_topc(sK1,sK0) | r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 3.08/0.77    inference(subsumption_resolution,[],[f240,f52])).
% 3.08/0.77  fof(f240,plain,(
% 3.08/0.77    ~v4_pre_topc(sK1,sK0) | r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0)),
% 3.08/0.77    inference(resolution,[],[f63,f53])).
% 3.08/0.77  fof(f63,plain,(
% 3.08/0.77    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | r1_tarski(k2_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) )),
% 3.08/0.77    inference(cnf_transformation,[],[f30])).
% 3.08/0.77  fof(f30,plain,(
% 3.08/0.77    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.08/0.77    inference(flattening,[],[f29])).
% 3.08/0.77  fof(f29,plain,(
% 3.08/0.77    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.08/0.77    inference(ennf_transformation,[],[f22])).
% 3.08/0.77  fof(f22,axiom,(
% 3.08/0.77    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 3.08/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).
% 3.08/0.77  fof(f3785,plain,(
% 3.08/0.77    spl2_1 | ~spl2_2),
% 3.08/0.77    inference(avatar_contradiction_clause,[],[f3784])).
% 3.08/0.77  fof(f3784,plain,(
% 3.08/0.77    $false | (spl2_1 | ~spl2_2)),
% 3.08/0.77    inference(subsumption_resolution,[],[f3783,f102])).
% 3.08/0.77  fof(f3783,plain,(
% 3.08/0.77    ~r1_tarski(sK1,u1_struct_0(sK0)) | (spl2_1 | ~spl2_2)),
% 3.08/0.77    inference(subsumption_resolution,[],[f3782,f51])).
% 3.08/0.77  fof(f51,plain,(
% 3.08/0.77    v2_pre_topc(sK0)),
% 3.08/0.77    inference(cnf_transformation,[],[f47])).
% 3.08/0.77  fof(f3782,plain,(
% 3.08/0.77    ~v2_pre_topc(sK0) | ~r1_tarski(sK1,u1_struct_0(sK0)) | (spl2_1 | ~spl2_2)),
% 3.08/0.77    inference(subsumption_resolution,[],[f3781,f52])).
% 3.08/0.77  fof(f3781,plain,(
% 3.08/0.77    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~r1_tarski(sK1,u1_struct_0(sK0)) | (spl2_1 | ~spl2_2)),
% 3.08/0.77    inference(subsumption_resolution,[],[f3778,f94])).
% 3.08/0.77  fof(f94,plain,(
% 3.08/0.77    ~v4_pre_topc(sK1,sK0) | spl2_1),
% 3.08/0.77    inference(avatar_component_clause,[],[f92])).
% 3.08/0.77  fof(f3778,plain,(
% 3.08/0.77    v4_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~r1_tarski(sK1,u1_struct_0(sK0)) | ~spl2_2),
% 3.08/0.77    inference(superposition,[],[f222,f3775])).
% 3.08/0.77  fof(f3775,plain,(
% 3.08/0.77    sK1 = k2_pre_topc(sK0,sK1) | ~spl2_2),
% 3.08/0.77    inference(backward_demodulation,[],[f262,f3769])).
% 3.08/0.77  fof(f3769,plain,(
% 3.08/0.77    sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_2),
% 3.08/0.77    inference(forward_demodulation,[],[f3768,f150])).
% 3.08/0.77  fof(f3768,plain,(
% 3.08/0.77    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_xboole_0) | ~spl2_2),
% 3.08/0.77    inference(forward_demodulation,[],[f3751,f526])).
% 3.08/0.77  fof(f526,plain,(
% 3.08/0.77    k1_xboole_0 = k7_subset_1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1) | ~spl2_2),
% 3.08/0.77    inference(forward_demodulation,[],[f519,f307])).
% 3.08/0.77  fof(f519,plain,(
% 3.08/0.77    k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k7_subset_1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1) | ~spl2_2),
% 3.08/0.77    inference(superposition,[],[f235,f342])).
% 3.08/0.77  fof(f342,plain,(
% 3.08/0.77    k2_tops_1(sK0,sK1) = k3_xboole_0(k2_tops_1(sK0,sK1),sK1) | ~spl2_2),
% 3.08/0.77    inference(resolution,[],[f338,f68])).
% 3.08/0.77  fof(f338,plain,(
% 3.08/0.77    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl2_2),
% 3.08/0.77    inference(superposition,[],[f328,f97])).
% 3.08/0.77  fof(f97,plain,(
% 3.08/0.77    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_2),
% 3.08/0.77    inference(avatar_component_clause,[],[f96])).
% 3.08/0.77  fof(f328,plain,(
% 3.08/0.77    ( ! [X2] : (r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X2),sK1)) )),
% 3.08/0.77    inference(superposition,[],[f85,f233])).
% 3.08/0.77  fof(f3751,plain,(
% 3.08/0.77    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k7_subset_1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1)) | ~spl2_2),
% 3.08/0.77    inference(resolution,[],[f1687,f383])).
% 3.08/0.77  fof(f383,plain,(
% 3.08/0.77    r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) | ~spl2_2),
% 3.08/0.77    inference(subsumption_resolution,[],[f380,f89])).
% 3.08/0.77  fof(f380,plain,(
% 3.08/0.77    r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) | ~r1_tarski(sK1,sK1) | ~spl2_2),
% 3.08/0.77    inference(resolution,[],[f152,f338])).
% 3.08/0.77  fof(f222,plain,(
% 3.08/0.77    ( ! [X2,X3] : (v4_pre_topc(k2_pre_topc(X2,X3),X2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~r1_tarski(X3,u1_struct_0(X2))) )),
% 3.08/0.77    inference(resolution,[],[f71,f76])).
% 3.08/0.77  fof(f71,plain,(
% 3.08/0.77    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.08/0.77    inference(cnf_transformation,[],[f35])).
% 3.08/0.77  fof(f35,plain,(
% 3.08/0.77    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.08/0.77    inference(flattening,[],[f34])).
% 3.08/0.77  fof(f34,plain,(
% 3.08/0.77    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.08/0.77    inference(ennf_transformation,[],[f19])).
% 3.08/0.77  fof(f19,axiom,(
% 3.08/0.77    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 3.08/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).
% 3.08/0.77  fof(f100,plain,(
% 3.08/0.77    spl2_1 | spl2_2),
% 3.08/0.77    inference(avatar_split_clause,[],[f54,f96,f92])).
% 3.08/0.77  fof(f54,plain,(
% 3.08/0.77    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 3.08/0.77    inference(cnf_transformation,[],[f47])).
% 3.08/0.77  fof(f99,plain,(
% 3.08/0.77    ~spl2_1 | ~spl2_2),
% 3.08/0.77    inference(avatar_split_clause,[],[f55,f96,f92])).
% 3.08/0.77  fof(f55,plain,(
% 3.08/0.77    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 3.08/0.77    inference(cnf_transformation,[],[f47])).
% 3.08/0.77  % SZS output end Proof for theBenchmark
% 3.08/0.77  % (8548)------------------------------
% 3.08/0.77  % (8548)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.08/0.77  % (8548)Termination reason: Refutation
% 3.08/0.77  
% 3.08/0.77  % (8548)Memory used [KB]: 13048
% 3.08/0.77  % (8548)Time elapsed: 0.330 s
% 3.08/0.77  % (8548)------------------------------
% 3.08/0.77  % (8548)------------------------------
% 3.08/0.77  % (8541)Success in time 0.409 s
%------------------------------------------------------------------------------
