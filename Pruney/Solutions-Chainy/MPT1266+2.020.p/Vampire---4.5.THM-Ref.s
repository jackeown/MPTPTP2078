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
% DateTime   : Thu Dec  3 13:12:25 EST 2020

% Result     : Theorem 1.60s
% Output     : Refutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 619 expanded)
%              Number of leaves         :   19 ( 153 expanded)
%              Depth                    :   16
%              Number of atoms          :  288 (1485 expanded)
%              Number of equality atoms :   75 ( 400 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1011,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f55,f834,f860,f932,f934,f938,f940,f1010])).

fof(f1010,plain,
    ( spl2_2
    | ~ spl2_4 ),
    inference(avatar_contradiction_clause,[],[f1009])).

fof(f1009,plain,
    ( $false
    | spl2_2
    | ~ spl2_4 ),
    inference(trivial_inequality_removal,[],[f1008])).

fof(f1008,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl2_2
    | ~ spl2_4 ),
    inference(superposition,[],[f51,f1007])).

fof(f1007,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f1006,f168])).

fof(f168,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    inference(forward_demodulation,[],[f118,f117])).

fof(f117,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f116,f33])).

fof(f33,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f116,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(resolution,[],[f59,f32])).

fof(f32,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f42,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f118,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) ),
    inference(resolution,[],[f65,f32])).

fof(f65,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X3,X2)
      | k3_subset_1(X2,k3_subset_1(X2,X3)) = X3 ) ),
    inference(resolution,[],[f43,f45])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f1006,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f1005,f107])).

fof(f107,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl2_4
  <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f1005,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) ),
    inference(forward_demodulation,[],[f1004,f62])).

fof(f62,plain,(
    k3_subset_1(k2_struct_0(sK0),sK1) = k4_xboole_0(k2_struct_0(sK0),sK1) ),
    inference(resolution,[],[f61,f42])).

fof(f61,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f30,f57])).

fof(f57,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f56,f31])).

fof(f31,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> k1_xboole_0 = k1_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

fof(f56,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(resolution,[],[f34,f35])).

fof(f35,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f34,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f30,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f1004,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) ),
    inference(forward_demodulation,[],[f1003,f81])).

fof(f81,plain,(
    sK1 = k3_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)) ),
    inference(forward_demodulation,[],[f66,f62])).

fof(f66,plain,(
    sK1 = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f43,f61])).

fof(f1003,plain,(
    k1_tops_1(sK0,k3_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1))) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1))))) ),
    inference(forward_demodulation,[],[f990,f62])).

fof(f990,plain,(
    k1_tops_1(sK0,k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1))) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1))))) ),
    inference(resolution,[],[f411,f61])).

fof(f411,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k1_tops_1(sK0,k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),X0))) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),X0))))) ) ),
    inference(global_subsumption,[],[f31,f408])).

fof(f408,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | k1_tops_1(sK0,k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),X0))) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),X0))))) ) ),
    inference(superposition,[],[f200,f57])).

fof(f200,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | k1_tops_1(X2,k3_subset_1(u1_struct_0(X2),k3_subset_1(u1_struct_0(X2),X3))) = k3_subset_1(u1_struct_0(X2),k2_pre_topc(X2,k3_subset_1(u1_struct_0(X2),k3_subset_1(u1_struct_0(X2),k3_subset_1(u1_struct_0(X2),X3))))) ) ),
    inference(resolution,[],[f92,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f92,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | k1_tops_1(X2,k3_subset_1(u1_struct_0(X2),X3)) = k3_subset_1(u1_struct_0(X2),k2_pre_topc(X2,k3_subset_1(u1_struct_0(X2),k3_subset_1(u1_struct_0(X2),X3))))
      | ~ l1_pre_topc(X2) ) ),
    inference(resolution,[],[f36,f41])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

fof(f51,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl2_2
  <=> k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f940,plain,
    ( spl2_1
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f939,f103,f47])).

fof(f47,plain,
    ( spl2_1
  <=> v2_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f103,plain,
    ( spl2_3
  <=> v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f939,plain,
    ( ~ v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | v2_tops_1(sK1,sK0) ),
    inference(global_subsumption,[],[f61,f179])).

fof(f179,plain,
    ( ~ v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | v2_tops_1(sK1,sK0) ),
    inference(superposition,[],[f83,f62])).

fof(f83,plain,(
    ! [X0] :
      ( ~ v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_tops_1(X0,sK0) ) ),
    inference(global_subsumption,[],[f31,f82])).

fof(f82,plain,(
    ! [X0] :
      ( ~ v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | v2_tops_1(X0,sK0) ) ),
    inference(superposition,[],[f39,f57])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_1)).

fof(f938,plain,
    ( spl2_4
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f937,f103,f106])).

fof(f937,plain,
    ( ~ v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) ),
    inference(global_subsumption,[],[f98])).

fof(f98,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))
    | ~ v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) ),
    inference(resolution,[],[f80,f68])).

fof(f68,plain,(
    m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(global_subsumption,[],[f61,f67])).

fof(f67,plain,
    ( m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(superposition,[],[f41,f62])).

fof(f80,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_struct_0(sK0) = k2_pre_topc(sK0,X0)
      | ~ v1_tops_1(X0,sK0) ) ),
    inference(global_subsumption,[],[f31,f78])).

fof(f78,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | k2_struct_0(sK0) = k2_pre_topc(sK0,X0)
      | ~ v1_tops_1(X0,sK0) ) ),
    inference(superposition,[],[f38,f57])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

fof(f934,plain,
    ( ~ spl2_1
    | spl2_4 ),
    inference(avatar_split_clause,[],[f933,f106,f47])).

fof(f933,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))
    | ~ v2_tops_1(sK1,sK0) ),
    inference(forward_demodulation,[],[f492,f62])).

fof(f492,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))
    | ~ v2_tops_1(sK1,sK0) ),
    inference(resolution,[],[f269,f61])).

fof(f269,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))
      | ~ v2_tops_1(X0,sK0) ) ),
    inference(global_subsumption,[],[f31,f267])).

fof(f267,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))
      | ~ v2_tops_1(X0,sK0) ) ),
    inference(superposition,[],[f176,f57])).

fof(f176,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))
      | ~ v2_tops_1(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f172])).

fof(f172,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X0) = k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_tops_1(X1,X0) ) ),
    inference(resolution,[],[f76,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f76,plain,(
    ! [X2,X3] :
      ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X2),X3),X2)
      | k2_struct_0(X2) = k2_pre_topc(X2,k3_subset_1(u1_struct_0(X2),X3))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(resolution,[],[f38,f41])).

fof(f932,plain,(
    spl2_44 ),
    inference(avatar_contradiction_clause,[],[f930])).

fof(f930,plain,
    ( $false
    | spl2_44 ),
    inference(resolution,[],[f826,f68])).

fof(f826,plain,
    ( ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl2_44 ),
    inference(avatar_component_clause,[],[f825])).

fof(f825,plain,
    ( spl2_44
  <=> m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).

fof(f860,plain,(
    spl2_45 ),
    inference(avatar_contradiction_clause,[],[f859])).

fof(f859,plain,
    ( $false
    | spl2_45 ),
    inference(resolution,[],[f833,f31])).

fof(f833,plain,
    ( ~ l1_pre_topc(sK0)
    | spl2_45 ),
    inference(avatar_component_clause,[],[f832])).

fof(f832,plain,
    ( spl2_45
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).

fof(f834,plain,
    ( spl2_3
    | ~ spl2_45
    | ~ spl2_44
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f829,f50,f825,f832,f103])).

fof(f829,plain,
    ( ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f823,f57])).

fof(f823,plain,
    ( ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ spl2_2 ),
    inference(trivial_inequality_removal,[],[f821])).

fof(f821,plain,
    ( k2_struct_0(sK0) != k2_struct_0(sK0)
    | ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ spl2_2 ),
    inference(superposition,[],[f37,f797])).

fof(f797,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f796,f117])).

fof(f796,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k1_xboole_0)
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f795,f516])).

fof(f516,plain,
    ( k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f515,f54])).

fof(f54,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f50])).

fof(f515,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) ),
    inference(forward_demodulation,[],[f507,f62])).

fof(f507,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) ),
    inference(resolution,[],[f96,f61])).

fof(f96,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k1_tops_1(sK0,X0) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) ) ),
    inference(global_subsumption,[],[f31,f94])).

fof(f94,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | k1_tops_1(sK0,X0) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) ) ),
    inference(superposition,[],[f36,f57])).

fof(f795,plain,(
    k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)))) ),
    inference(forward_demodulation,[],[f788,f62])).

fof(f788,plain,(
    k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))) ),
    inference(resolution,[],[f357,f61])).

fof(f357,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0)) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0)))) ) ),
    inference(global_subsumption,[],[f31,f354])).

fof(f354,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0)) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))))
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f157,f57])).

fof(f157,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | k2_pre_topc(X2,k3_subset_1(u1_struct_0(X2),X3)) = k3_subset_1(u1_struct_0(X2),k3_subset_1(u1_struct_0(X2),k2_pre_topc(X2,k3_subset_1(u1_struct_0(X2),X3))))
      | ~ l1_pre_topc(X2) ) ),
    inference(resolution,[],[f69,f41])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | k2_pre_topc(X1,X0) = k3_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0))) ) ),
    inference(resolution,[],[f44,f43])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X0) != k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f55,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f28,f50,f47])).

fof(f28,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f52,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f29,f50,f47])).

fof(f29,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n002.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:41:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.47  % (5315)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.48  % (5319)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (5315)Refutation not found, incomplete strategy% (5315)------------------------------
% 0.21/0.48  % (5315)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (5315)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (5315)Memory used [KB]: 10618
% 0.21/0.48  % (5315)Time elapsed: 0.062 s
% 0.21/0.48  % (5315)------------------------------
% 0.21/0.48  % (5315)------------------------------
% 0.21/0.49  % (5323)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.49  % (5327)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.50  % (5320)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.50  % (5321)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.51  % (5314)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.51  % (5313)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.51  % (5329)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.52  % (5325)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.52  % (5320)Refutation not found, incomplete strategy% (5320)------------------------------
% 0.21/0.52  % (5320)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (5320)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (5320)Memory used [KB]: 10618
% 0.21/0.52  % (5320)Time elapsed: 0.085 s
% 0.21/0.52  % (5320)------------------------------
% 0.21/0.52  % (5320)------------------------------
% 0.21/0.52  % (5322)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.52  % (5334)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.52  % (5328)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.52  % (5322)Refutation not found, incomplete strategy% (5322)------------------------------
% 0.21/0.52  % (5322)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (5322)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (5322)Memory used [KB]: 10618
% 0.21/0.52  % (5322)Time elapsed: 0.100 s
% 0.21/0.52  % (5322)------------------------------
% 0.21/0.52  % (5322)------------------------------
% 0.21/0.53  % (5331)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.53  % (5332)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.53  % (5316)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.54  % (5324)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.54  % (5335)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.54  % (5317)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.55  % (5335)Refutation not found, incomplete strategy% (5335)------------------------------
% 0.21/0.55  % (5335)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (5335)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (5335)Memory used [KB]: 10618
% 0.21/0.55  % (5335)Time elapsed: 0.132 s
% 0.21/0.55  % (5335)------------------------------
% 0.21/0.55  % (5335)------------------------------
% 1.43/0.55  % (5312)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 1.43/0.56  % (5318)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 1.43/0.56  % (5333)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 1.60/0.57  % (5330)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 1.60/0.57  % (5326)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 1.60/0.59  % (5324)Refutation found. Thanks to Tanya!
% 1.60/0.59  % SZS status Theorem for theBenchmark
% 1.60/0.59  % SZS output start Proof for theBenchmark
% 1.60/0.59  fof(f1011,plain,(
% 1.60/0.59    $false),
% 1.60/0.59    inference(avatar_sat_refutation,[],[f52,f55,f834,f860,f932,f934,f938,f940,f1010])).
% 1.60/0.59  fof(f1010,plain,(
% 1.60/0.59    spl2_2 | ~spl2_4),
% 1.60/0.59    inference(avatar_contradiction_clause,[],[f1009])).
% 1.60/0.59  fof(f1009,plain,(
% 1.60/0.59    $false | (spl2_2 | ~spl2_4)),
% 1.60/0.59    inference(trivial_inequality_removal,[],[f1008])).
% 1.60/0.59  fof(f1008,plain,(
% 1.60/0.59    k1_xboole_0 != k1_xboole_0 | (spl2_2 | ~spl2_4)),
% 1.60/0.59    inference(superposition,[],[f51,f1007])).
% 1.60/0.59  fof(f1007,plain,(
% 1.60/0.59    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~spl2_4),
% 1.60/0.59    inference(forward_demodulation,[],[f1006,f168])).
% 1.60/0.59  fof(f168,plain,(
% 1.60/0.59    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0)) )),
% 1.60/0.59    inference(forward_demodulation,[],[f118,f117])).
% 1.60/0.59  fof(f117,plain,(
% 1.60/0.59    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 1.60/0.59    inference(forward_demodulation,[],[f116,f33])).
% 1.60/0.59  fof(f33,plain,(
% 1.60/0.59    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.60/0.59    inference(cnf_transformation,[],[f2])).
% 1.60/0.59  fof(f2,axiom,(
% 1.60/0.59    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.60/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.60/0.59  fof(f116,plain,(
% 1.60/0.59    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0)) )),
% 1.60/0.59    inference(resolution,[],[f59,f32])).
% 1.60/0.59  fof(f32,plain,(
% 1.60/0.59    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.60/0.59    inference(cnf_transformation,[],[f1])).
% 1.60/0.59  fof(f1,axiom,(
% 1.60/0.59    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.60/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.60/0.59  fof(f59,plain,(
% 1.60/0.59    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)) )),
% 1.60/0.59    inference(resolution,[],[f42,f45])).
% 1.60/0.59  fof(f45,plain,(
% 1.60/0.59    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.60/0.59    inference(cnf_transformation,[],[f27])).
% 1.60/0.59  fof(f27,plain,(
% 1.60/0.59    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 1.60/0.59    inference(ennf_transformation,[],[f15])).
% 1.60/0.59  fof(f15,plain,(
% 1.60/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 1.60/0.59    inference(unused_predicate_definition_removal,[],[f6])).
% 1.60/0.59  fof(f6,axiom,(
% 1.60/0.59    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.60/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.60/0.59  fof(f42,plain,(
% 1.60/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)) )),
% 1.60/0.59    inference(cnf_transformation,[],[f23])).
% 1.60/0.59  fof(f23,plain,(
% 1.60/0.59    ! [X0,X1] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.60/0.59    inference(ennf_transformation,[],[f3])).
% 1.60/0.59  fof(f3,axiom,(
% 1.60/0.59    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1))),
% 1.60/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.60/0.59  fof(f118,plain,(
% 1.60/0.59    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0))) )),
% 1.60/0.59    inference(resolution,[],[f65,f32])).
% 1.60/0.59  fof(f65,plain,(
% 1.60/0.59    ( ! [X2,X3] : (~r1_tarski(X3,X2) | k3_subset_1(X2,k3_subset_1(X2,X3)) = X3) )),
% 1.60/0.59    inference(resolution,[],[f43,f45])).
% 1.60/0.59  fof(f43,plain,(
% 1.60/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 1.60/0.59    inference(cnf_transformation,[],[f24])).
% 1.60/0.59  fof(f24,plain,(
% 1.60/0.59    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.60/0.59    inference(ennf_transformation,[],[f5])).
% 1.60/0.59  fof(f5,axiom,(
% 1.60/0.59    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.60/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.60/0.59  fof(f1006,plain,(
% 1.60/0.59    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) | ~spl2_4),
% 1.60/0.59    inference(forward_demodulation,[],[f1005,f107])).
% 1.60/0.59  fof(f107,plain,(
% 1.60/0.59    k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) | ~spl2_4),
% 1.60/0.59    inference(avatar_component_clause,[],[f106])).
% 1.60/0.59  fof(f106,plain,(
% 1.60/0.59    spl2_4 <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))),
% 1.60/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 1.60/0.59  fof(f1005,plain,(
% 1.60/0.59    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)))),
% 1.60/0.59    inference(forward_demodulation,[],[f1004,f62])).
% 1.60/0.59  fof(f62,plain,(
% 1.60/0.59    k3_subset_1(k2_struct_0(sK0),sK1) = k4_xboole_0(k2_struct_0(sK0),sK1)),
% 1.60/0.59    inference(resolution,[],[f61,f42])).
% 1.60/0.59  fof(f61,plain,(
% 1.60/0.59    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.60/0.59    inference(backward_demodulation,[],[f30,f57])).
% 1.60/0.59  fof(f57,plain,(
% 1.60/0.59    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 1.60/0.59    inference(resolution,[],[f56,f31])).
% 1.60/0.59  fof(f31,plain,(
% 1.60/0.59    l1_pre_topc(sK0)),
% 1.60/0.59    inference(cnf_transformation,[],[f16])).
% 1.60/0.59  fof(f16,plain,(
% 1.60/0.59    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> k1_xboole_0 = k1_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.60/0.59    inference(ennf_transformation,[],[f14])).
% 1.60/0.59  fof(f14,negated_conjecture,(
% 1.60/0.59    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 1.60/0.59    inference(negated_conjecture,[],[f13])).
% 1.60/0.59  fof(f13,conjecture,(
% 1.60/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 1.60/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).
% 1.60/0.59  fof(f56,plain,(
% 1.60/0.59    ( ! [X0] : (~l1_pre_topc(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.60/0.59    inference(resolution,[],[f34,f35])).
% 1.60/0.59  fof(f35,plain,(
% 1.60/0.59    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.60/0.59    inference(cnf_transformation,[],[f18])).
% 1.60/0.59  fof(f18,plain,(
% 1.60/0.59    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.60/0.59    inference(ennf_transformation,[],[f9])).
% 1.60/0.59  fof(f9,axiom,(
% 1.60/0.59    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.60/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.60/0.59  fof(f34,plain,(
% 1.60/0.59    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.60/0.59    inference(cnf_transformation,[],[f17])).
% 1.60/0.59  fof(f17,plain,(
% 1.60/0.59    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.60/0.59    inference(ennf_transformation,[],[f7])).
% 1.60/0.59  fof(f7,axiom,(
% 1.60/0.59    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.60/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 1.60/0.59  fof(f30,plain,(
% 1.60/0.59    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.60/0.59    inference(cnf_transformation,[],[f16])).
% 1.60/0.59  fof(f1004,plain,(
% 1.60/0.59    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))),
% 1.60/0.59    inference(forward_demodulation,[],[f1003,f81])).
% 1.60/0.59  fof(f81,plain,(
% 1.60/0.59    sK1 = k3_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1))),
% 1.60/0.59    inference(forward_demodulation,[],[f66,f62])).
% 1.60/0.59  fof(f66,plain,(
% 1.60/0.59    sK1 = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1))),
% 1.60/0.59    inference(resolution,[],[f43,f61])).
% 1.60/0.59  fof(f1003,plain,(
% 1.60/0.59    k1_tops_1(sK0,k3_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1))) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)))))),
% 1.60/0.59    inference(forward_demodulation,[],[f990,f62])).
% 1.60/0.59  fof(f990,plain,(
% 1.60/0.59    k1_tops_1(sK0,k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1))) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1)))))),
% 1.60/0.59    inference(resolution,[],[f411,f61])).
% 1.60/0.60  fof(f411,plain,(
% 1.60/0.60    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k1_tops_1(sK0,k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),X0))) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),X0)))))) )),
% 1.60/0.60    inference(global_subsumption,[],[f31,f408])).
% 1.60/0.60  fof(f408,plain,(
% 1.60/0.60    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | k1_tops_1(sK0,k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),X0))) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),X0)))))) )),
% 1.60/0.60    inference(superposition,[],[f200,f57])).
% 1.60/0.60  fof(f200,plain,(
% 1.60/0.60    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | k1_tops_1(X2,k3_subset_1(u1_struct_0(X2),k3_subset_1(u1_struct_0(X2),X3))) = k3_subset_1(u1_struct_0(X2),k2_pre_topc(X2,k3_subset_1(u1_struct_0(X2),k3_subset_1(u1_struct_0(X2),k3_subset_1(u1_struct_0(X2),X3)))))) )),
% 1.60/0.60    inference(resolution,[],[f92,f41])).
% 1.60/0.60  fof(f41,plain,(
% 1.60/0.60    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.60/0.60    inference(cnf_transformation,[],[f22])).
% 1.60/0.60  fof(f22,plain,(
% 1.60/0.60    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.60/0.60    inference(ennf_transformation,[],[f4])).
% 1.60/0.60  fof(f4,axiom,(
% 1.60/0.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.60/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.60/0.60  fof(f92,plain,(
% 1.60/0.60    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | k1_tops_1(X2,k3_subset_1(u1_struct_0(X2),X3)) = k3_subset_1(u1_struct_0(X2),k2_pre_topc(X2,k3_subset_1(u1_struct_0(X2),k3_subset_1(u1_struct_0(X2),X3)))) | ~l1_pre_topc(X2)) )),
% 1.60/0.60    inference(resolution,[],[f36,f41])).
% 1.60/0.60  fof(f36,plain,(
% 1.60/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))) )),
% 1.60/0.60    inference(cnf_transformation,[],[f19])).
% 1.60/0.60  fof(f19,plain,(
% 1.60/0.60    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.60/0.60    inference(ennf_transformation,[],[f10])).
% 1.60/0.60  fof(f10,axiom,(
% 1.60/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 1.60/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).
% 1.60/0.60  fof(f51,plain,(
% 1.60/0.60    k1_xboole_0 != k1_tops_1(sK0,sK1) | spl2_2),
% 1.60/0.60    inference(avatar_component_clause,[],[f50])).
% 1.60/0.60  fof(f50,plain,(
% 1.60/0.60    spl2_2 <=> k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 1.60/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.60/0.60  fof(f940,plain,(
% 1.60/0.60    spl2_1 | ~spl2_3),
% 1.60/0.60    inference(avatar_split_clause,[],[f939,f103,f47])).
% 1.60/0.60  fof(f47,plain,(
% 1.60/0.60    spl2_1 <=> v2_tops_1(sK1,sK0)),
% 1.60/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.60/0.60  fof(f103,plain,(
% 1.60/0.60    spl2_3 <=> v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)),
% 1.60/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.60/0.60  fof(f939,plain,(
% 1.60/0.60    ~v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) | v2_tops_1(sK1,sK0)),
% 1.60/0.60    inference(global_subsumption,[],[f61,f179])).
% 1.60/0.60  fof(f179,plain,(
% 1.60/0.60    ~v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | v2_tops_1(sK1,sK0)),
% 1.60/0.60    inference(superposition,[],[f83,f62])).
% 1.60/0.60  fof(f83,plain,(
% 1.60/0.60    ( ! [X0] : (~v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v2_tops_1(X0,sK0)) )),
% 1.60/0.60    inference(global_subsumption,[],[f31,f82])).
% 1.60/0.60  fof(f82,plain,(
% 1.60/0.60    ( ! [X0] : (~v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | v2_tops_1(X0,sK0)) )),
% 1.60/0.60    inference(superposition,[],[f39,f57])).
% 1.60/0.60  fof(f39,plain,(
% 1.60/0.60    ( ! [X0,X1] : (~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_tops_1(X1,X0)) )),
% 1.60/0.60    inference(cnf_transformation,[],[f21])).
% 1.60/0.60  fof(f21,plain,(
% 1.60/0.60    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.60/0.60    inference(ennf_transformation,[],[f12])).
% 1.60/0.60  fof(f12,axiom,(
% 1.60/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 1.60/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_1)).
% 1.60/0.60  fof(f938,plain,(
% 1.60/0.60    spl2_4 | ~spl2_3),
% 1.60/0.60    inference(avatar_split_clause,[],[f937,f103,f106])).
% 1.60/0.60  fof(f937,plain,(
% 1.60/0.60    ~v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) | k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))),
% 1.60/0.60    inference(global_subsumption,[],[f98])).
% 1.60/0.60  fof(f98,plain,(
% 1.60/0.60    k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) | ~v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)),
% 1.60/0.60    inference(resolution,[],[f80,f68])).
% 1.60/0.60  fof(f68,plain,(
% 1.60/0.60    m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.60/0.60    inference(global_subsumption,[],[f61,f67])).
% 1.60/0.60  fof(f67,plain,(
% 1.60/0.60    m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.60/0.60    inference(superposition,[],[f41,f62])).
% 1.60/0.60  fof(f80,plain,(
% 1.60/0.60    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,X0) | ~v1_tops_1(X0,sK0)) )),
% 1.60/0.60    inference(global_subsumption,[],[f31,f78])).
% 1.60/0.60  fof(f78,plain,(
% 1.60/0.60    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | k2_struct_0(sK0) = k2_pre_topc(sK0,X0) | ~v1_tops_1(X0,sK0)) )),
% 1.60/0.60    inference(superposition,[],[f38,f57])).
% 1.60/0.60  fof(f38,plain,(
% 1.60/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0)) )),
% 1.60/0.60    inference(cnf_transformation,[],[f20])).
% 1.60/0.60  fof(f20,plain,(
% 1.60/0.60    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.60/0.60    inference(ennf_transformation,[],[f11])).
% 1.60/0.60  fof(f11,axiom,(
% 1.60/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 1.60/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).
% 1.60/0.60  fof(f934,plain,(
% 1.60/0.60    ~spl2_1 | spl2_4),
% 1.60/0.60    inference(avatar_split_clause,[],[f933,f106,f47])).
% 1.60/0.60  fof(f933,plain,(
% 1.60/0.60    k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) | ~v2_tops_1(sK1,sK0)),
% 1.60/0.60    inference(forward_demodulation,[],[f492,f62])).
% 1.60/0.60  fof(f492,plain,(
% 1.60/0.60    k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) | ~v2_tops_1(sK1,sK0)),
% 1.60/0.60    inference(resolution,[],[f269,f61])).
% 1.60/0.60  fof(f269,plain,(
% 1.60/0.60    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0)) | ~v2_tops_1(X0,sK0)) )),
% 1.60/0.60    inference(global_subsumption,[],[f31,f267])).
% 1.60/0.60  fof(f267,plain,(
% 1.60/0.60    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0)) | ~v2_tops_1(X0,sK0)) )),
% 1.60/0.60    inference(superposition,[],[f176,f57])).
% 1.60/0.60  fof(f176,plain,(
% 1.60/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k2_struct_0(X0) = k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~v2_tops_1(X1,X0)) )),
% 1.60/0.60    inference(duplicate_literal_removal,[],[f172])).
% 1.60/0.60  fof(f172,plain,(
% 1.60/0.60    ( ! [X0,X1] : (k2_struct_0(X0) = k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_tops_1(X1,X0)) )),
% 1.60/0.60    inference(resolution,[],[f76,f40])).
% 1.60/0.60  fof(f40,plain,(
% 1.60/0.60    ( ! [X0,X1] : (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_tops_1(X1,X0)) )),
% 1.60/0.60    inference(cnf_transformation,[],[f21])).
% 1.60/0.60  fof(f76,plain,(
% 1.60/0.60    ( ! [X2,X3] : (~v1_tops_1(k3_subset_1(u1_struct_0(X2),X3),X2) | k2_struct_0(X2) = k2_pre_topc(X2,k3_subset_1(u1_struct_0(X2),X3)) | ~l1_pre_topc(X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) )),
% 1.60/0.60    inference(resolution,[],[f38,f41])).
% 1.60/0.60  fof(f932,plain,(
% 1.60/0.60    spl2_44),
% 1.60/0.60    inference(avatar_contradiction_clause,[],[f930])).
% 1.60/0.60  fof(f930,plain,(
% 1.60/0.60    $false | spl2_44),
% 1.60/0.60    inference(resolution,[],[f826,f68])).
% 1.60/0.60  fof(f826,plain,(
% 1.60/0.60    ~m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | spl2_44),
% 1.60/0.60    inference(avatar_component_clause,[],[f825])).
% 1.60/0.60  fof(f825,plain,(
% 1.60/0.60    spl2_44 <=> m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.60/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).
% 1.60/0.60  fof(f860,plain,(
% 1.60/0.60    spl2_45),
% 1.60/0.60    inference(avatar_contradiction_clause,[],[f859])).
% 1.60/0.60  fof(f859,plain,(
% 1.60/0.60    $false | spl2_45),
% 1.60/0.60    inference(resolution,[],[f833,f31])).
% 1.60/0.60  fof(f833,plain,(
% 1.60/0.60    ~l1_pre_topc(sK0) | spl2_45),
% 1.60/0.60    inference(avatar_component_clause,[],[f832])).
% 1.60/0.60  fof(f832,plain,(
% 1.60/0.60    spl2_45 <=> l1_pre_topc(sK0)),
% 1.60/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).
% 1.60/0.60  fof(f834,plain,(
% 1.60/0.60    spl2_3 | ~spl2_45 | ~spl2_44 | ~spl2_2),
% 1.60/0.60    inference(avatar_split_clause,[],[f829,f50,f825,f832,f103])).
% 1.60/0.60  fof(f829,plain,(
% 1.60/0.60    ~m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) | ~spl2_2),
% 1.60/0.60    inference(forward_demodulation,[],[f823,f57])).
% 1.60/0.60  fof(f823,plain,(
% 1.60/0.60    ~m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) | ~spl2_2),
% 1.60/0.60    inference(trivial_inequality_removal,[],[f821])).
% 1.60/0.60  fof(f821,plain,(
% 1.60/0.60    k2_struct_0(sK0) != k2_struct_0(sK0) | ~m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) | ~spl2_2),
% 1.60/0.60    inference(superposition,[],[f37,f797])).
% 1.60/0.60  fof(f797,plain,(
% 1.60/0.60    k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) | ~spl2_2),
% 1.60/0.60    inference(forward_demodulation,[],[f796,f117])).
% 1.60/0.60  fof(f796,plain,(
% 1.60/0.60    k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k1_xboole_0) | ~spl2_2),
% 1.60/0.60    inference(forward_demodulation,[],[f795,f516])).
% 1.60/0.60  fof(f516,plain,(
% 1.60/0.60    k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) | ~spl2_2),
% 1.60/0.60    inference(forward_demodulation,[],[f515,f54])).
% 1.60/0.60  fof(f54,plain,(
% 1.60/0.60    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~spl2_2),
% 1.60/0.60    inference(avatar_component_clause,[],[f50])).
% 1.60/0.60  fof(f515,plain,(
% 1.60/0.60    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)))),
% 1.60/0.60    inference(forward_demodulation,[],[f507,f62])).
% 1.60/0.60  fof(f507,plain,(
% 1.60/0.60    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))),
% 1.60/0.60    inference(resolution,[],[f96,f61])).
% 1.60/0.60  fof(f96,plain,(
% 1.60/0.60    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k1_tops_1(sK0,X0) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0)))) )),
% 1.60/0.60    inference(global_subsumption,[],[f31,f94])).
% 1.60/0.60  fof(f94,plain,(
% 1.60/0.60    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | k1_tops_1(sK0,X0) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0)))) )),
% 1.60/0.60    inference(superposition,[],[f36,f57])).
% 1.60/0.60  fof(f795,plain,(
% 1.60/0.60    k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))))),
% 1.60/0.60    inference(forward_demodulation,[],[f788,f62])).
% 1.60/0.60  fof(f788,plain,(
% 1.60/0.60    k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))))),
% 1.60/0.60    inference(resolution,[],[f357,f61])).
% 1.60/0.60  fof(f357,plain,(
% 1.60/0.60    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0)) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))))) )),
% 1.60/0.60    inference(global_subsumption,[],[f31,f354])).
% 1.60/0.60  fof(f354,plain,(
% 1.60/0.60    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0)) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0)))) | ~l1_pre_topc(sK0)) )),
% 1.60/0.60    inference(superposition,[],[f157,f57])).
% 1.60/0.60  fof(f157,plain,(
% 1.60/0.60    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | k2_pre_topc(X2,k3_subset_1(u1_struct_0(X2),X3)) = k3_subset_1(u1_struct_0(X2),k3_subset_1(u1_struct_0(X2),k2_pre_topc(X2,k3_subset_1(u1_struct_0(X2),X3)))) | ~l1_pre_topc(X2)) )),
% 1.60/0.60    inference(resolution,[],[f69,f41])).
% 1.60/0.60  fof(f69,plain,(
% 1.60/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | k2_pre_topc(X1,X0) = k3_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0)))) )),
% 1.60/0.60    inference(resolution,[],[f44,f43])).
% 1.60/0.60  fof(f44,plain,(
% 1.60/0.60    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.60/0.60    inference(cnf_transformation,[],[f26])).
% 1.60/0.60  fof(f26,plain,(
% 1.60/0.60    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.60/0.60    inference(flattening,[],[f25])).
% 1.60/0.60  fof(f25,plain,(
% 1.60/0.60    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.60/0.60    inference(ennf_transformation,[],[f8])).
% 1.60/0.60  fof(f8,axiom,(
% 1.60/0.60    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.60/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 1.60/0.60  fof(f37,plain,(
% 1.60/0.60    ( ! [X0,X1] : (k2_struct_0(X0) != k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v1_tops_1(X1,X0)) )),
% 1.60/0.60    inference(cnf_transformation,[],[f20])).
% 1.60/0.60  fof(f55,plain,(
% 1.60/0.60    spl2_1 | spl2_2),
% 1.60/0.60    inference(avatar_split_clause,[],[f28,f50,f47])).
% 1.60/0.60  fof(f28,plain,(
% 1.60/0.60    k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)),
% 1.60/0.60    inference(cnf_transformation,[],[f16])).
% 1.60/0.60  fof(f52,plain,(
% 1.60/0.60    ~spl2_1 | ~spl2_2),
% 1.60/0.60    inference(avatar_split_clause,[],[f29,f50,f47])).
% 1.60/0.60  fof(f29,plain,(
% 1.60/0.60    k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)),
% 1.60/0.60    inference(cnf_transformation,[],[f16])).
% 1.60/0.60  % SZS output end Proof for theBenchmark
% 1.60/0.60  % (5324)------------------------------
% 1.60/0.60  % (5324)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.60  % (5324)Termination reason: Refutation
% 1.60/0.60  
% 1.60/0.60  % (5324)Memory used [KB]: 11385
% 1.60/0.60  % (5324)Time elapsed: 0.172 s
% 1.60/0.60  % (5324)------------------------------
% 1.60/0.60  % (5324)------------------------------
% 1.60/0.60  % (5311)Success in time 0.231 s
%------------------------------------------------------------------------------
