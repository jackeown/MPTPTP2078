%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:36 EST 2020

% Result     : Theorem 3.36s
% Output     : Refutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 516 expanded)
%              Number of leaves         :   23 ( 141 expanded)
%              Depth                    :   32
%              Number of atoms          :  339 (2152 expanded)
%              Number of equality atoms :   92 ( 655 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5896,plain,(
    $false ),
    inference(subsumption_resolution,[],[f5895,f1275])).

fof(f1275,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f1274,f65])).

fof(f65,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f53,f55,f54])).

fof(f54,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | ~ v3_pre_topc(X1,X0) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | ~ v3_pre_topc(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | v3_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | ~ v3_pre_topc(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | v3_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | ~ v3_pre_topc(sK1,sK0) )
      & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | v3_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f30])).

fof(f30,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

fof(f1274,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f1273,f66])).

fof(f66,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f56])).

fof(f1273,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f1272,f67])).

fof(f67,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f56])).

fof(f1272,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(duplicate_literal_removal,[],[f1271])).

fof(f1271,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v3_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f91,f1245])).

fof(f1245,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f1244,f66])).

fof(f1244,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | v3_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f1222,f67])).

fof(f1222,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f1194,f243])).

fof(f243,plain,(
    ! [X2,X3] :
      ( k4_xboole_0(X3,k2_tops_1(X2,X3)) = k1_tops_1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(duplicate_literal_removal,[],[f240])).

fof(f240,plain,(
    ! [X2,X3] :
      ( k4_xboole_0(X3,k2_tops_1(X2,X3)) = k1_tops_1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(superposition,[],[f75,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f75,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f1194,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | v3_pre_topc(sK1,sK0) ),
    inference(forward_demodulation,[],[f1178,f136])).

fof(f136,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f134,f72])).

fof(f72,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f134,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f85,f71])).

fof(f71,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f85,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f1178,plain,
    ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_xboole_0)
    | v3_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f86,f1091])).

fof(f1091,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | v3_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f1090,f66])).

fof(f1090,plain,
    ( ~ l1_pre_topc(sK0)
    | k1_xboole_0 = k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | v3_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f1073,f67])).

fof(f1073,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k1_xboole_0 = k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | v3_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f238,f1016])).

fof(f1016,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | v3_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f615,f973])).

fof(f973,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X2,X1),X2) ),
    inference(superposition,[],[f898,f164])).

fof(f164,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2) ),
    inference(superposition,[],[f117,f84])).

fof(f84,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f117,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(superposition,[],[f84,f82])).

fof(f82,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f898,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X1,X0),X0) ),
    inference(backward_demodulation,[],[f200,f897])).

fof(f897,plain,(
    ! [X0,X1] : k1_xboole_0 = k3_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(subsumption_resolution,[],[f871,f177])).

fof(f177,plain,(
    ! [X6,X5] : r1_tarski(k3_xboole_0(X6,X5),X5) ),
    inference(superposition,[],[f79,f164])).

fof(f79,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f871,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k3_xboole_0(X1,X0),X0)
      | k1_xboole_0 = k3_xboole_0(k4_xboole_0(X1,X0),X0) ) ),
    inference(superposition,[],[f205,f78])).

fof(f78,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

% (11560)Time limit reached!
% (11560)------------------------------
% (11560)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f205,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(k3_xboole_0(X3,X4),k3_xboole_0(X5,X4))
      | k1_xboole_0 = k3_xboole_0(k4_xboole_0(X3,X5),X4) ) ),
    inference(superposition,[],[f98,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f98,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k4_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k4_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_xboole_1)).

fof(f200,plain,(
    ! [X0,X1] : k3_xboole_0(k4_xboole_0(X1,X0),X0) = k4_xboole_0(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f98,f78])).

fof(f615,plain,
    ( k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k4_xboole_0(k3_xboole_0(sK1,k2_pre_topc(sK0,sK1)),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK1,sK0) ),
    inference(forward_demodulation,[],[f614,f164])).

fof(f614,plain,
    ( k4_xboole_0(k3_xboole_0(k2_pre_topc(sK0,sK1),sK1),sK1) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK1,sK0) ),
    inference(forward_demodulation,[],[f587,f164])).

fof(f587,plain,
    ( k4_xboole_0(k3_xboole_0(k2_pre_topc(sK0,sK1),sK1),sK1) = k3_xboole_0(k2_tops_1(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f200,f183])).

fof(f183,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f99,f68])).

fof(f68,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f56])).

fof(f238,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f235,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f235,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f234])).

fof(f234,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f100,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f86,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f91,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f5895,plain,(
    ~ v3_pre_topc(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f5894])).

fof(f5894,plain,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f69,f5893])).

fof(f5893,plain,(
    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f5892,f66])).

fof(f5892,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f5884,f67])).

fof(f5884,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f76,f5772])).

fof(f5772,plain,(
    sK1 = k1_tops_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f5767,f1275])).

fof(f5767,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f5766,f295])).

fof(f295,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | sK1 = k1_tops_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f288,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f288,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f286,f107])).

fof(f107,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f286,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ r1_tarski(sK1,sK1) ),
    inference(resolution,[],[f280,f67])).

fof(f280,plain,(
    ! [X16] :
      ( ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X16,sK0)
      | r1_tarski(X16,k1_tops_1(sK0,sK1))
      | ~ r1_tarski(X16,sK1) ) ),
    inference(subsumption_resolution,[],[f278,f66])).

fof(f278,plain,(
    ! [X16] :
      ( ~ r1_tarski(X16,sK1)
      | ~ v3_pre_topc(X16,sK0)
      | r1_tarski(X16,k1_tops_1(sK0,sK1))
      | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f77,f67])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

fof(f5766,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f5763,f66])).

fof(f5763,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f1098,f67])).

fof(f1098,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | r1_tarski(k1_tops_1(X1,X0),X0)
      | ~ l1_pre_topc(X1) ) ),
    inference(superposition,[],[f80,f243])).

fof(f80,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f76,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f69,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f56])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:16:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.49  % (11568)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.49  % (11566)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.50  % (11576)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.50  % (11560)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (11574)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.51  % (11582)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.51  % (11569)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.18/0.52  % (11577)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.18/0.52  % (11561)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.18/0.52  % (11556)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.18/0.52  % (11557)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.18/0.52  % (11558)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.18/0.52  % (11582)Refutation not found, incomplete strategy% (11582)------------------------------
% 1.18/0.52  % (11582)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.18/0.52  % (11582)Termination reason: Refutation not found, incomplete strategy
% 1.18/0.52  
% 1.18/0.52  % (11582)Memory used [KB]: 10874
% 1.18/0.52  % (11582)Time elapsed: 0.100 s
% 1.18/0.52  % (11582)------------------------------
% 1.18/0.52  % (11582)------------------------------
% 1.18/0.53  % (11583)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.18/0.53  % (11583)Refutation not found, incomplete strategy% (11583)------------------------------
% 1.18/0.53  % (11583)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.18/0.53  % (11583)Termination reason: Refutation not found, incomplete strategy
% 1.18/0.53  
% 1.18/0.53  % (11583)Memory used [KB]: 1663
% 1.18/0.53  % (11583)Time elapsed: 0.001 s
% 1.18/0.53  % (11583)------------------------------
% 1.18/0.53  % (11583)------------------------------
% 1.18/0.53  % (11573)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.34/0.53  % (11559)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.34/0.54  % (11581)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.34/0.54  % (11579)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.34/0.54  % (11580)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.34/0.54  % (11571)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.34/0.54  % (11565)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.34/0.54  % (11572)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.34/0.54  % (11570)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.34/0.54  % (11575)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.34/0.54  % (11567)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.34/0.55  % (11578)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.34/0.55  % (11562)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.34/0.55  % (11554)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.34/0.55  % (11563)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.34/0.55  % (11555)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.34/0.55  % (11564)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.34/0.55  % (11570)Refutation not found, incomplete strategy% (11570)------------------------------
% 1.34/0.55  % (11570)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.55  % (11570)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.55  
% 1.34/0.55  % (11570)Memory used [KB]: 10746
% 1.34/0.55  % (11570)Time elapsed: 0.150 s
% 1.34/0.55  % (11570)------------------------------
% 1.34/0.55  % (11570)------------------------------
% 1.34/0.56  % (11564)Refutation not found, incomplete strategy% (11564)------------------------------
% 1.34/0.56  % (11564)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.56  % (11564)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.56  
% 1.34/0.56  % (11564)Memory used [KB]: 10874
% 1.34/0.56  % (11564)Time elapsed: 0.151 s
% 1.34/0.56  % (11564)------------------------------
% 1.34/0.56  % (11564)------------------------------
% 1.97/0.63  % (11597)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 1.97/0.67  % (11612)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 1.97/0.68  % (11614)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 1.97/0.69  % (11610)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 3.16/0.82  % (11578)Time limit reached!
% 3.16/0.82  % (11578)------------------------------
% 3.16/0.82  % (11578)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.16/0.82  % (11578)Termination reason: Time limit
% 3.16/0.82  % (11578)Termination phase: Saturation
% 3.16/0.82  
% 3.16/0.82  % (11578)Memory used [KB]: 14072
% 3.16/0.82  % (11578)Time elapsed: 0.400 s
% 3.16/0.82  % (11578)------------------------------
% 3.16/0.82  % (11578)------------------------------
% 3.16/0.83  % (11556)Time limit reached!
% 3.16/0.83  % (11556)------------------------------
% 3.16/0.83  % (11556)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.16/0.83  % (11556)Termination reason: Time limit
% 3.16/0.83  
% 3.16/0.83  % (11556)Memory used [KB]: 6780
% 3.16/0.83  % (11556)Time elapsed: 0.415 s
% 3.16/0.83  % (11556)------------------------------
% 3.16/0.83  % (11556)------------------------------
% 3.36/0.91  % (11563)Refutation found. Thanks to Tanya!
% 3.36/0.91  % SZS status Theorem for theBenchmark
% 3.36/0.92  % SZS output start Proof for theBenchmark
% 3.36/0.92  fof(f5896,plain,(
% 3.36/0.92    $false),
% 3.36/0.92    inference(subsumption_resolution,[],[f5895,f1275])).
% 3.36/0.92  fof(f1275,plain,(
% 3.36/0.92    v3_pre_topc(sK1,sK0)),
% 3.36/0.92    inference(subsumption_resolution,[],[f1274,f65])).
% 3.36/0.92  fof(f65,plain,(
% 3.36/0.92    v2_pre_topc(sK0)),
% 3.36/0.92    inference(cnf_transformation,[],[f56])).
% 3.36/0.92  fof(f56,plain,(
% 3.36/0.92    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 3.36/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f53,f55,f54])).
% 3.36/0.92  fof(f54,plain,(
% 3.36/0.92    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 3.36/0.92    introduced(choice_axiom,[])).
% 3.36/0.92  fof(f55,plain,(
% 3.36/0.92    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 3.36/0.92    introduced(choice_axiom,[])).
% 3.36/0.92  fof(f53,plain,(
% 3.36/0.92    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.36/0.92    inference(flattening,[],[f52])).
% 3.36/0.92  fof(f52,plain,(
% 3.36/0.92    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.36/0.92    inference(nnf_transformation,[],[f34])).
% 3.36/0.92  fof(f34,plain,(
% 3.36/0.92    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.36/0.92    inference(flattening,[],[f33])).
% 3.36/0.92  fof(f33,plain,(
% 3.36/0.92    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.36/0.92    inference(ennf_transformation,[],[f31])).
% 3.36/0.92  fof(f31,negated_conjecture,(
% 3.36/0.92    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 3.36/0.92    inference(negated_conjecture,[],[f30])).
% 3.36/0.92  fof(f30,conjecture,(
% 3.36/0.92    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 3.36/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).
% 3.36/0.92  fof(f1274,plain,(
% 3.36/0.92    v3_pre_topc(sK1,sK0) | ~v2_pre_topc(sK0)),
% 3.36/0.92    inference(subsumption_resolution,[],[f1273,f66])).
% 3.36/0.92  fof(f66,plain,(
% 3.36/0.92    l1_pre_topc(sK0)),
% 3.36/0.92    inference(cnf_transformation,[],[f56])).
% 3.36/0.92  fof(f1273,plain,(
% 3.36/0.92    v3_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 3.36/0.92    inference(subsumption_resolution,[],[f1272,f67])).
% 3.36/0.92  fof(f67,plain,(
% 3.36/0.92    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.36/0.92    inference(cnf_transformation,[],[f56])).
% 3.36/0.92  fof(f1272,plain,(
% 3.36/0.92    v3_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 3.36/0.92    inference(duplicate_literal_removal,[],[f1271])).
% 3.36/0.92  fof(f1271,plain,(
% 3.36/0.92    v3_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v3_pre_topc(sK1,sK0)),
% 3.36/0.92    inference(superposition,[],[f91,f1245])).
% 3.36/0.92  fof(f1245,plain,(
% 3.36/0.92    sK1 = k1_tops_1(sK0,sK1) | v3_pre_topc(sK1,sK0)),
% 3.36/0.92    inference(subsumption_resolution,[],[f1244,f66])).
% 3.36/0.92  fof(f1244,plain,(
% 3.36/0.92    sK1 = k1_tops_1(sK0,sK1) | v3_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0)),
% 3.36/0.92    inference(subsumption_resolution,[],[f1222,f67])).
% 3.36/0.92  fof(f1222,plain,(
% 3.36/0.92    sK1 = k1_tops_1(sK0,sK1) | v3_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 3.36/0.92    inference(superposition,[],[f1194,f243])).
% 3.36/0.92  fof(f243,plain,(
% 3.36/0.92    ( ! [X2,X3] : (k4_xboole_0(X3,k2_tops_1(X2,X3)) = k1_tops_1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 3.36/0.92    inference(duplicate_literal_removal,[],[f240])).
% 3.36/0.92  fof(f240,plain,(
% 3.36/0.92    ( ! [X2,X3] : (k4_xboole_0(X3,k2_tops_1(X2,X3)) = k1_tops_1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) )),
% 3.36/0.92    inference(superposition,[],[f75,f99])).
% 3.36/0.92  fof(f99,plain,(
% 3.36/0.92    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.36/0.92    inference(cnf_transformation,[],[f49])).
% 3.36/0.92  fof(f49,plain,(
% 3.36/0.92    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.36/0.92    inference(ennf_transformation,[],[f21])).
% 3.36/0.92  fof(f21,axiom,(
% 3.36/0.92    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 3.36/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 3.36/0.92  fof(f75,plain,(
% 3.36/0.92    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.36/0.92    inference(cnf_transformation,[],[f37])).
% 3.36/0.92  fof(f37,plain,(
% 3.36/0.92    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.36/0.92    inference(ennf_transformation,[],[f29])).
% 3.36/0.92  fof(f29,axiom,(
% 3.36/0.92    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 3.36/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 3.36/0.92  fof(f1194,plain,(
% 3.36/0.92    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | v3_pre_topc(sK1,sK0)),
% 3.36/0.92    inference(forward_demodulation,[],[f1178,f136])).
% 3.36/0.92  fof(f136,plain,(
% 3.36/0.92    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.36/0.92    inference(forward_demodulation,[],[f134,f72])).
% 3.36/0.92  fof(f72,plain,(
% 3.36/0.92    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.36/0.92    inference(cnf_transformation,[],[f8])).
% 3.36/0.92  fof(f8,axiom,(
% 3.36/0.92    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 3.36/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 3.36/0.92  fof(f134,plain,(
% 3.36/0.92    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0)) )),
% 3.36/0.92    inference(superposition,[],[f85,f71])).
% 3.36/0.92  fof(f71,plain,(
% 3.36/0.92    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 3.36/0.92    inference(cnf_transformation,[],[f12])).
% 3.36/0.92  fof(f12,axiom,(
% 3.36/0.92    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 3.36/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 3.36/0.92  fof(f85,plain,(
% 3.36/0.92    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.36/0.92    inference(cnf_transformation,[],[f13])).
% 3.36/0.92  fof(f13,axiom,(
% 3.36/0.92    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.36/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 3.36/0.92  fof(f1178,plain,(
% 3.36/0.92    k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_xboole_0) | v3_pre_topc(sK1,sK0)),
% 3.36/0.92    inference(superposition,[],[f86,f1091])).
% 3.36/0.92  fof(f1091,plain,(
% 3.36/0.92    k1_xboole_0 = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | v3_pre_topc(sK1,sK0)),
% 3.36/0.92    inference(subsumption_resolution,[],[f1090,f66])).
% 3.36/0.92  fof(f1090,plain,(
% 3.36/0.92    ~l1_pre_topc(sK0) | k1_xboole_0 = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | v3_pre_topc(sK1,sK0)),
% 3.36/0.92    inference(subsumption_resolution,[],[f1073,f67])).
% 3.36/0.92  fof(f1073,plain,(
% 3.36/0.92    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | k1_xboole_0 = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | v3_pre_topc(sK1,sK0)),
% 3.36/0.92    inference(resolution,[],[f238,f1016])).
% 3.36/0.92  fof(f1016,plain,(
% 3.36/0.92    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | v3_pre_topc(sK1,sK0)),
% 3.36/0.92    inference(backward_demodulation,[],[f615,f973])).
% 3.36/0.92  fof(f973,plain,(
% 3.36/0.92    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X2,X1),X2)) )),
% 3.36/0.92    inference(superposition,[],[f898,f164])).
% 3.36/0.92  fof(f164,plain,(
% 3.36/0.92    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) )),
% 3.36/0.92    inference(superposition,[],[f117,f84])).
% 3.36/0.92  fof(f84,plain,(
% 3.36/0.92    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.36/0.92    inference(cnf_transformation,[],[f22])).
% 3.36/0.92  fof(f22,axiom,(
% 3.36/0.92    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.36/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 3.36/0.92  fof(f117,plain,(
% 3.36/0.92    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 3.36/0.92    inference(superposition,[],[f84,f82])).
% 3.36/0.92  fof(f82,plain,(
% 3.36/0.92    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.36/0.92    inference(cnf_transformation,[],[f14])).
% 3.36/0.92  fof(f14,axiom,(
% 3.36/0.92    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.36/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 3.36/0.92  fof(f898,plain,(
% 3.36/0.92    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X1,X0),X0)) )),
% 3.36/0.92    inference(backward_demodulation,[],[f200,f897])).
% 3.36/0.92  fof(f897,plain,(
% 3.36/0.92    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(k4_xboole_0(X1,X0),X0)) )),
% 3.36/0.92    inference(subsumption_resolution,[],[f871,f177])).
% 3.36/0.92  fof(f177,plain,(
% 3.36/0.92    ( ! [X6,X5] : (r1_tarski(k3_xboole_0(X6,X5),X5)) )),
% 3.36/0.92    inference(superposition,[],[f79,f164])).
% 3.36/0.92  fof(f79,plain,(
% 3.36/0.92    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.36/0.92    inference(cnf_transformation,[],[f7])).
% 3.36/0.92  fof(f7,axiom,(
% 3.36/0.92    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.36/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 3.36/0.92  fof(f871,plain,(
% 3.36/0.92    ( ! [X0,X1] : (~r1_tarski(k3_xboole_0(X1,X0),X0) | k1_xboole_0 = k3_xboole_0(k4_xboole_0(X1,X0),X0)) )),
% 3.36/0.92    inference(superposition,[],[f205,f78])).
% 3.36/0.92  fof(f78,plain,(
% 3.36/0.92    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 3.36/0.92    inference(cnf_transformation,[],[f32])).
% 3.36/0.92  fof(f32,plain,(
% 3.36/0.92    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 3.36/0.92    inference(rectify,[],[f2])).
% 3.36/0.92  % (11560)Time limit reached!
% 3.36/0.92  % (11560)------------------------------
% 3.36/0.92  % (11560)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.36/0.92  fof(f2,axiom,(
% 3.36/0.92    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 3.36/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 3.36/0.92  fof(f205,plain,(
% 3.36/0.92    ( ! [X4,X5,X3] : (~r1_tarski(k3_xboole_0(X3,X4),k3_xboole_0(X5,X4)) | k1_xboole_0 = k3_xboole_0(k4_xboole_0(X3,X5),X4)) )),
% 3.36/0.92    inference(superposition,[],[f98,f97])).
% 3.36/0.92  fof(f97,plain,(
% 3.36/0.92    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 3.36/0.92    inference(cnf_transformation,[],[f59])).
% 3.36/0.92  fof(f59,plain,(
% 3.36/0.92    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 3.36/0.92    inference(nnf_transformation,[],[f4])).
% 3.36/0.92  fof(f4,axiom,(
% 3.36/0.92    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 3.36/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 3.36/0.92  fof(f98,plain,(
% 3.36/0.92    ( ! [X2,X0,X1] : (k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k4_xboole_0(X0,X2),X1)) )),
% 3.36/0.92    inference(cnf_transformation,[],[f6])).
% 3.36/0.92  fof(f6,axiom,(
% 3.36/0.92    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k4_xboole_0(X0,X2),X1)),
% 3.36/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_xboole_1)).
% 3.36/0.92  fof(f200,plain,(
% 3.36/0.92    ( ! [X0,X1] : (k3_xboole_0(k4_xboole_0(X1,X0),X0) = k4_xboole_0(k3_xboole_0(X1,X0),X0)) )),
% 3.36/0.92    inference(superposition,[],[f98,f78])).
% 3.36/0.92  fof(f615,plain,(
% 3.36/0.92    k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k4_xboole_0(k3_xboole_0(sK1,k2_pre_topc(sK0,sK1)),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK1,sK0)),
% 3.36/0.92    inference(forward_demodulation,[],[f614,f164])).
% 3.36/0.92  fof(f614,plain,(
% 3.36/0.92    k4_xboole_0(k3_xboole_0(k2_pre_topc(sK0,sK1),sK1),sK1) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK1,sK0)),
% 3.36/0.92    inference(forward_demodulation,[],[f587,f164])).
% 3.36/0.92  fof(f587,plain,(
% 3.36/0.92    k4_xboole_0(k3_xboole_0(k2_pre_topc(sK0,sK1),sK1),sK1) = k3_xboole_0(k2_tops_1(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK1,sK0)),
% 3.36/0.92    inference(superposition,[],[f200,f183])).
% 3.36/0.92  fof(f183,plain,(
% 3.36/0.92    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK1,sK0)),
% 3.36/0.92    inference(superposition,[],[f99,f68])).
% 3.36/0.92  fof(f68,plain,(
% 3.36/0.92    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 3.36/0.92    inference(cnf_transformation,[],[f56])).
% 3.36/0.92  fof(f238,plain,(
% 3.36/0.92    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.36/0.92    inference(subsumption_resolution,[],[f235,f92])).
% 3.36/0.92  fof(f92,plain,(
% 3.36/0.92    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.36/0.92    inference(cnf_transformation,[],[f48])).
% 3.36/0.92  fof(f48,plain,(
% 3.36/0.92    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.36/0.92    inference(flattening,[],[f47])).
% 3.36/0.92  fof(f47,plain,(
% 3.36/0.92    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.36/0.92    inference(ennf_transformation,[],[f23])).
% 3.36/0.92  fof(f23,axiom,(
% 3.36/0.92    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.36/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 3.36/0.92  fof(f235,plain,(
% 3.36/0.92    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.36/0.92    inference(duplicate_literal_removal,[],[f234])).
% 3.36/0.92  fof(f234,plain,(
% 3.36/0.92    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.36/0.92    inference(superposition,[],[f100,f74])).
% 3.36/0.92  fof(f74,plain,(
% 3.36/0.92    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.36/0.92    inference(cnf_transformation,[],[f36])).
% 3.36/0.93  fof(f36,plain,(
% 3.36/0.93    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.36/0.93    inference(ennf_transformation,[],[f28])).
% 3.36/0.93  fof(f28,axiom,(
% 3.36/0.93    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 3.36/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 3.36/0.93  fof(f100,plain,(
% 3.36/0.93    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.36/0.93    inference(cnf_transformation,[],[f51])).
% 3.36/0.93  fof(f51,plain,(
% 3.36/0.93    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.36/0.93    inference(flattening,[],[f50])).
% 3.36/0.93  fof(f50,plain,(
% 3.36/0.93    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.36/0.93    inference(ennf_transformation,[],[f17])).
% 3.36/0.93  fof(f17,axiom,(
% 3.36/0.93    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 3.36/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 3.36/0.93  fof(f86,plain,(
% 3.36/0.93    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.36/0.93    inference(cnf_transformation,[],[f5])).
% 3.36/0.93  fof(f5,axiom,(
% 3.36/0.93    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.36/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 3.36/0.93  fof(f91,plain,(
% 3.36/0.93    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.36/0.93    inference(cnf_transformation,[],[f46])).
% 3.36/0.93  fof(f46,plain,(
% 3.36/0.93    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.36/0.93    inference(flattening,[],[f45])).
% 3.36/0.93  fof(f45,plain,(
% 3.36/0.93    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.36/0.93    inference(ennf_transformation,[],[f24])).
% 3.36/0.93  fof(f24,axiom,(
% 3.36/0.93    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 3.36/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 3.36/0.93  fof(f5895,plain,(
% 3.36/0.93    ~v3_pre_topc(sK1,sK0)),
% 3.36/0.93    inference(trivial_inequality_removal,[],[f5894])).
% 3.36/0.93  fof(f5894,plain,(
% 3.36/0.93    k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)),
% 3.36/0.93    inference(backward_demodulation,[],[f69,f5893])).
% 3.36/0.93  fof(f5893,plain,(
% 3.36/0.93    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 3.36/0.93    inference(subsumption_resolution,[],[f5892,f66])).
% 3.36/0.93  fof(f5892,plain,(
% 3.36/0.93    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~l1_pre_topc(sK0)),
% 3.36/0.93    inference(subsumption_resolution,[],[f5884,f67])).
% 3.36/0.93  fof(f5884,plain,(
% 3.36/0.93    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 3.36/0.93    inference(superposition,[],[f76,f5772])).
% 3.36/0.93  fof(f5772,plain,(
% 3.36/0.93    sK1 = k1_tops_1(sK0,sK1)),
% 3.36/0.93    inference(subsumption_resolution,[],[f5767,f1275])).
% 3.36/0.93  fof(f5767,plain,(
% 3.36/0.93    sK1 = k1_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)),
% 3.36/0.93    inference(resolution,[],[f5766,f295])).
% 3.36/0.93  fof(f295,plain,(
% 3.36/0.93    ~r1_tarski(k1_tops_1(sK0,sK1),sK1) | sK1 = k1_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)),
% 3.36/0.93    inference(resolution,[],[f288,f95])).
% 3.36/0.93  fof(f95,plain,(
% 3.36/0.93    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 3.36/0.93    inference(cnf_transformation,[],[f58])).
% 3.36/0.93  fof(f58,plain,(
% 3.36/0.93    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.36/0.93    inference(flattening,[],[f57])).
% 3.36/0.93  fof(f57,plain,(
% 3.36/0.93    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.36/0.93    inference(nnf_transformation,[],[f3])).
% 3.36/0.93  fof(f3,axiom,(
% 3.36/0.93    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.36/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.36/0.93  fof(f288,plain,(
% 3.36/0.93    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~v3_pre_topc(sK1,sK0)),
% 3.36/0.93    inference(subsumption_resolution,[],[f286,f107])).
% 3.36/0.93  fof(f107,plain,(
% 3.36/0.93    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.36/0.93    inference(equality_resolution,[],[f94])).
% 3.36/0.93  fof(f94,plain,(
% 3.36/0.93    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.36/0.93    inference(cnf_transformation,[],[f58])).
% 3.36/0.93  fof(f286,plain,(
% 3.36/0.93    ~v3_pre_topc(sK1,sK0) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~r1_tarski(sK1,sK1)),
% 3.36/0.93    inference(resolution,[],[f280,f67])).
% 3.36/0.93  fof(f280,plain,(
% 3.36/0.93    ( ! [X16] : (~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X16,sK0) | r1_tarski(X16,k1_tops_1(sK0,sK1)) | ~r1_tarski(X16,sK1)) )),
% 3.36/0.93    inference(subsumption_resolution,[],[f278,f66])).
% 3.36/0.93  fof(f278,plain,(
% 3.36/0.93    ( ! [X16] : (~r1_tarski(X16,sK1) | ~v3_pre_topc(X16,sK0) | r1_tarski(X16,k1_tops_1(sK0,sK1)) | ~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 3.36/0.93    inference(resolution,[],[f77,f67])).
% 3.36/0.93  fof(f77,plain,(
% 3.36/0.93    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.36/0.93    inference(cnf_transformation,[],[f40])).
% 3.36/0.93  fof(f40,plain,(
% 3.36/0.93    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.36/0.93    inference(flattening,[],[f39])).
% 3.36/0.93  fof(f39,plain,(
% 3.36/0.93    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.36/0.93    inference(ennf_transformation,[],[f26])).
% 3.36/0.93  fof(f26,axiom,(
% 3.36/0.93    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 3.36/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).
% 3.36/0.93  fof(f5766,plain,(
% 3.36/0.93    r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 3.36/0.93    inference(subsumption_resolution,[],[f5763,f66])).
% 3.36/0.93  fof(f5763,plain,(
% 3.36/0.93    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0)),
% 3.36/0.93    inference(resolution,[],[f1098,f67])).
% 3.36/0.93  fof(f1098,plain,(
% 3.36/0.93    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | r1_tarski(k1_tops_1(X1,X0),X0) | ~l1_pre_topc(X1)) )),
% 3.36/0.93    inference(superposition,[],[f80,f243])).
% 3.36/0.93  fof(f80,plain,(
% 3.36/0.93    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.36/0.93    inference(cnf_transformation,[],[f11])).
% 3.36/0.93  fof(f11,axiom,(
% 3.36/0.93    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.36/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 3.36/0.93  fof(f76,plain,(
% 3.36/0.93    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.36/0.93    inference(cnf_transformation,[],[f38])).
% 3.36/0.93  fof(f38,plain,(
% 3.36/0.93    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.36/0.93    inference(ennf_transformation,[],[f25])).
% 3.36/0.93  fof(f25,axiom,(
% 3.36/0.93    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 3.36/0.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 3.36/0.93  fof(f69,plain,(
% 3.36/0.93    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 3.36/0.93    inference(cnf_transformation,[],[f56])).
% 3.36/0.93  % SZS output end Proof for theBenchmark
% 3.36/0.93  % (11563)------------------------------
% 3.36/0.93  % (11563)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.36/0.93  % (11563)Termination reason: Refutation
% 3.36/0.93  
% 3.36/0.93  % (11563)Memory used [KB]: 4733
% 3.36/0.93  % (11563)Time elapsed: 0.504 s
% 3.36/0.93  % (11563)------------------------------
% 3.36/0.93  % (11563)------------------------------
% 4.01/0.93  % (11553)Success in time 0.56 s
%------------------------------------------------------------------------------
