%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:28 EST 2020

% Result     : Theorem 1.87s
% Output     : Refutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 151 expanded)
%              Number of leaves         :   17 (  42 expanded)
%              Depth                    :   21
%              Number of atoms          :  297 ( 488 expanded)
%              Number of equality atoms :   16 (  25 expanded)
%              Maximal formula depth    :    9 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f454,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f58,f63,f311,f453])).

fof(f453,plain,
    ( ~ spl2_2
    | ~ spl2_3
    | spl2_1 ),
    inference(avatar_split_clause,[],[f448,f50,f60,f55])).

fof(f55,plain,
    ( spl2_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f60,plain,
    ( spl2_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f50,plain,
    ( spl2_1
  <=> r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f448,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_1 ),
    inference(resolution,[],[f446,f52])).

fof(f52,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f446,plain,(
    ! [X2,X3] :
      ( r1_xboole_0(k1_tops_1(X2,X3),k2_tops_1(X2,X3))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(duplicate_literal_removal,[],[f441])).

fof(f441,plain,(
    ! [X2,X3] :
      ( r1_xboole_0(k1_tops_1(X2,X3),k2_tops_1(X2,X3))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(resolution,[],[f435,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f435,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k3_subset_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
      | r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(duplicate_literal_removal,[],[f434])).

fof(f434,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f426,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_1)).

fof(f426,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(global_subsumption,[],[f45,f424])).

fof(f424,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(duplicate_literal_removal,[],[f423])).

fof(f423,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f349,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

fof(f349,plain,(
    ! [X12,X13] :
      ( ~ m1_subset_1(k3_subset_1(u1_struct_0(X12),k2_pre_topc(X12,X13)),k1_zfmisc_1(u1_struct_0(X12)))
      | r1_xboole_0(k3_subset_1(u1_struct_0(X12),k2_pre_topc(X12,X13)),k2_tops_1(X12,X13))
      | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
      | ~ l1_pre_topc(X12) ) ),
    inference(global_subsumption,[],[f46,f344])).

fof(f344,plain,(
    ! [X12,X13] :
      ( ~ m1_subset_1(k3_subset_1(u1_struct_0(X12),k2_pre_topc(X12,X13)),k1_zfmisc_1(u1_struct_0(X12)))
      | r1_xboole_0(k3_subset_1(u1_struct_0(X12),k2_pre_topc(X12,X13)),k2_tops_1(X12,X13))
      | ~ m1_subset_1(k2_tops_1(X12,X13),k1_zfmisc_1(u1_struct_0(X12)))
      | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
      | ~ l1_pre_topc(X12) ) ),
    inference(duplicate_literal_removal,[],[f343])).

fof(f343,plain,(
    ! [X12,X13] :
      ( ~ m1_subset_1(k3_subset_1(u1_struct_0(X12),k2_pre_topc(X12,X13)),k1_zfmisc_1(u1_struct_0(X12)))
      | r1_xboole_0(k3_subset_1(u1_struct_0(X12),k2_pre_topc(X12,X13)),k2_tops_1(X12,X13))
      | ~ m1_subset_1(k2_tops_1(X12,X13),k1_zfmisc_1(u1_struct_0(X12)))
      | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
      | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
      | ~ l1_pre_topc(X12) ) ),
    inference(superposition,[],[f210,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f210,plain,(
    ! [X10,X11,X9] :
      ( ~ m1_subset_1(k3_subset_1(X9,k4_subset_1(X9,X10,X11)),k1_zfmisc_1(X9))
      | r1_xboole_0(k3_subset_1(X9,k4_subset_1(X9,X10,X11)),X11)
      | ~ m1_subset_1(X11,k1_zfmisc_1(X9))
      | ~ m1_subset_1(X10,k1_zfmisc_1(X9)) ) ),
    inference(duplicate_literal_removal,[],[f199])).

fof(f199,plain,(
    ! [X10,X11,X9] :
      ( r1_xboole_0(k3_subset_1(X9,k4_subset_1(X9,X10,X11)),X11)
      | ~ m1_subset_1(k3_subset_1(X9,k4_subset_1(X9,X10,X11)),k1_zfmisc_1(X9))
      | ~ m1_subset_1(X11,k1_zfmisc_1(X9))
      | ~ m1_subset_1(X10,k1_zfmisc_1(X9))
      | ~ m1_subset_1(X11,k1_zfmisc_1(X9)) ) ),
    inference(resolution,[],[f194,f111])).

fof(f111,plain,(
    ! [X4,X5,X3] :
      ( r1_tarski(k3_subset_1(X3,k4_subset_1(X3,X5,X4)),k3_subset_1(X3,X4))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3)) ) ),
    inference(duplicate_literal_removal,[],[f103])).

fof(f103,plain,(
    ! [X4,X5,X3] :
      ( r1_tarski(k3_subset_1(X3,k4_subset_1(X3,X5,X4)),k3_subset_1(X3,X4))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3)) ) ),
    inference(superposition,[],[f42,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_subset_1)).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_subset_1)).

fof(f194,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_subset_1(X1,X2))
      | r1_xboole_0(X0,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ) ),
    inference(duplicate_literal_removal,[],[f190])).

fof(f190,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_subset_1(X1,X2))
      | r1_xboole_0(X0,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f67,f40])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ r1_tarski(X2,k3_subset_1(X0,X1))
      | r1_xboole_0(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f44,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X1,k3_subset_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
              | ~ r1_tarski(X1,X2) )
            & ( r1_tarski(X1,X2)
              | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_subset_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(f311,plain,
    ( ~ spl2_3
    | spl2_4
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f303,f55,f308,f60])).

fof(f308,plain,
    ( spl2_4
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f303,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(resolution,[],[f298,f57])).

fof(f57,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f298,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | r1_tarski(k1_tops_1(X1,X0),X0)
      | ~ l1_pre_topc(X1) ) ),
    inference(duplicate_literal_removal,[],[f295])).

fof(f295,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | r1_tarski(k1_tops_1(X1,X0),X0)
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f294,f45])).

fof(f294,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f288])).

fof(f288,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(resolution,[],[f285,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X1,k3_subset_1(X0,X2))
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f285,plain,(
    ! [X2,X3] :
      ( r1_xboole_0(k1_tops_1(X2,X3),k3_subset_1(u1_struct_0(X2),X3))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(duplicate_literal_removal,[],[f280])).

fof(f280,plain,(
    ! [X2,X3] :
      ( r1_xboole_0(k1_tops_1(X2,X3),k3_subset_1(u1_struct_0(X2),X3))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(resolution,[],[f264,f40])).

fof(f264,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k3_subset_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
      | r1_xboole_0(k1_tops_1(X0,X1),k3_subset_1(u1_struct_0(X0),X1))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(global_subsumption,[],[f45,f262])).

fof(f262,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | r1_xboole_0(k1_tops_1(X0,X1),k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(duplicate_literal_removal,[],[f261])).

fof(f261,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | r1_xboole_0(k1_tops_1(X0,X1),k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f209,f39])).

fof(f209,plain,(
    ! [X28,X29] :
      ( ~ m1_subset_1(k3_subset_1(u1_struct_0(X28),k2_pre_topc(X28,X29)),k1_zfmisc_1(u1_struct_0(X28)))
      | r1_xboole_0(k3_subset_1(u1_struct_0(X28),k2_pre_topc(X28,X29)),X29)
      | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
      | ~ l1_pre_topc(X28) ) ),
    inference(duplicate_literal_removal,[],[f204])).

fof(f204,plain,(
    ! [X28,X29] :
      ( r1_xboole_0(k3_subset_1(u1_struct_0(X28),k2_pre_topc(X28,X29)),X29)
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(X28),k2_pre_topc(X28,X29)),k1_zfmisc_1(u1_struct_0(X28)))
      | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
      | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
      | ~ l1_pre_topc(X28) ) ),
    inference(resolution,[],[f194,f113])).

fof(f113,plain,(
    ! [X12,X13] :
      ( r1_tarski(k3_subset_1(u1_struct_0(X12),k2_pre_topc(X12,X13)),k3_subset_1(u1_struct_0(X12),X13))
      | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
      | ~ l1_pre_topc(X12) ) ),
    inference(global_subsumption,[],[f46,f108])).

fof(f108,plain,(
    ! [X12,X13] :
      ( r1_tarski(k3_subset_1(u1_struct_0(X12),k2_pre_topc(X12,X13)),k3_subset_1(u1_struct_0(X12),X13))
      | ~ m1_subset_1(k2_tops_1(X12,X13),k1_zfmisc_1(u1_struct_0(X12)))
      | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
      | ~ l1_pre_topc(X12) ) ),
    inference(duplicate_literal_removal,[],[f106])).

fof(f106,plain,(
    ! [X12,X13] :
      ( r1_tarski(k3_subset_1(u1_struct_0(X12),k2_pre_topc(X12,X13)),k3_subset_1(u1_struct_0(X12),X13))
      | ~ m1_subset_1(k2_tops_1(X12,X13),k1_zfmisc_1(u1_struct_0(X12)))
      | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
      | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
      | ~ l1_pre_topc(X12) ) ),
    inference(superposition,[],[f42,f38])).

fof(f63,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f34,f60])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f31,f30])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ r1_xboole_0(k1_tops_1(sK0,X1),k2_tops_1(sK0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X1] :
        ( ~ r1_xboole_0(k1_tops_1(sK0,X1),k2_tops_1(sK0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_tops_1)).

fof(f58,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f35,f55])).

fof(f35,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f53,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f36,f50])).

fof(f36,plain,(
    ~ r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.11/0.33  % Computer   : n021.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 12:50:34 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.20/0.48  % (10482)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.20/0.48  % (10486)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.48  % (10483)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.48  % (10484)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.48  % (10487)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.49  % (10505)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.20/0.49  % (10500)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.20/0.49  % (10497)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.20/0.49  % (10504)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.20/0.49  % (10490)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.20/0.49  % (10503)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.20/0.49  % (10485)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.49  % (10501)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.20/0.49  % (10496)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.20/0.50  % (10485)Refutation not found, incomplete strategy% (10485)------------------------------
% 0.20/0.50  % (10485)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (10485)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (10485)Memory used [KB]: 10490
% 0.20/0.50  % (10485)Time elapsed: 0.101 s
% 0.20/0.50  % (10485)------------------------------
% 0.20/0.50  % (10485)------------------------------
% 0.20/0.50  % (10489)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (10499)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.20/0.50  % (10494)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.50  % (10488)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.20/0.50  % (10495)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.20/0.50  % (10492)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.20/0.50  % (10493)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.20/0.50  % (10492)Refutation not found, incomplete strategy% (10492)------------------------------
% 0.20/0.50  % (10492)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (10492)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (10492)Memory used [KB]: 10618
% 0.20/0.50  % (10492)Time elapsed: 0.105 s
% 0.20/0.50  % (10492)------------------------------
% 0.20/0.50  % (10492)------------------------------
% 0.20/0.50  % (10498)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.20/0.51  % (10502)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.20/0.52  % (10505)Refutation not found, incomplete strategy% (10505)------------------------------
% 0.20/0.52  % (10505)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (10505)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (10505)Memory used [KB]: 10618
% 0.20/0.52  % (10505)Time elapsed: 0.101 s
% 0.20/0.52  % (10505)------------------------------
% 0.20/0.52  % (10505)------------------------------
% 0.20/0.52  % (10491)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 1.87/0.58  % (10504)Refutation not found, incomplete strategy% (10504)------------------------------
% 1.87/0.58  % (10504)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.58  % (10504)Termination reason: Refutation not found, incomplete strategy
% 1.87/0.58  
% 1.87/0.58  % (10504)Memory used [KB]: 1535
% 1.87/0.58  % (10504)Time elapsed: 0.175 s
% 1.87/0.58  % (10504)------------------------------
% 1.87/0.58  % (10504)------------------------------
% 1.87/0.62  % (10486)Refutation found. Thanks to Tanya!
% 1.87/0.62  % SZS status Theorem for theBenchmark
% 1.87/0.62  % SZS output start Proof for theBenchmark
% 1.87/0.62  fof(f454,plain,(
% 1.87/0.62    $false),
% 1.87/0.62    inference(avatar_sat_refutation,[],[f53,f58,f63,f311,f453])).
% 1.87/0.62  fof(f453,plain,(
% 1.87/0.62    ~spl2_2 | ~spl2_3 | spl2_1),
% 1.87/0.62    inference(avatar_split_clause,[],[f448,f50,f60,f55])).
% 1.87/0.62  fof(f55,plain,(
% 1.87/0.62    spl2_2 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.87/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.87/0.62  fof(f60,plain,(
% 1.87/0.62    spl2_3 <=> l1_pre_topc(sK0)),
% 1.87/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.87/0.62  fof(f50,plain,(
% 1.87/0.62    spl2_1 <=> r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))),
% 1.87/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.87/0.62  fof(f448,plain,(
% 1.87/0.62    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl2_1),
% 1.87/0.62    inference(resolution,[],[f446,f52])).
% 1.87/0.62  fof(f52,plain,(
% 1.87/0.62    ~r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) | spl2_1),
% 1.87/0.62    inference(avatar_component_clause,[],[f50])).
% 1.87/0.62  fof(f446,plain,(
% 1.87/0.62    ( ! [X2,X3] : (r1_xboole_0(k1_tops_1(X2,X3),k2_tops_1(X2,X3)) | ~l1_pre_topc(X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) )),
% 1.87/0.62    inference(duplicate_literal_removal,[],[f441])).
% 1.87/0.62  fof(f441,plain,(
% 1.87/0.62    ( ! [X2,X3] : (r1_xboole_0(k1_tops_1(X2,X3),k2_tops_1(X2,X3)) | ~l1_pre_topc(X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) )),
% 1.87/0.62    inference(resolution,[],[f435,f40])).
% 1.87/0.62  fof(f40,plain,(
% 1.87/0.62    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.87/0.62    inference(cnf_transformation,[],[f18])).
% 1.87/0.62  fof(f18,plain,(
% 1.87/0.62    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.87/0.62    inference(ennf_transformation,[],[f2])).
% 1.87/0.62  fof(f2,axiom,(
% 1.87/0.62    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.87/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.87/0.62  fof(f435,plain,(
% 1.87/0.62    ( ! [X0,X1] : (~m1_subset_1(k3_subset_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.87/0.62    inference(duplicate_literal_removal,[],[f434])).
% 1.87/0.62  fof(f434,plain,(
% 1.87/0.62    ( ! [X0,X1] : (r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) | ~m1_subset_1(k3_subset_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.87/0.62    inference(superposition,[],[f426,f37])).
% 1.87/0.62  fof(f37,plain,(
% 1.87/0.62    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.87/0.62    inference(cnf_transformation,[],[f15])).
% 1.87/0.62  fof(f15,plain,(
% 1.87/0.62    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.87/0.62    inference(ennf_transformation,[],[f10])).
% 1.87/0.62  fof(f10,axiom,(
% 1.87/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))))),
% 1.87/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_1)).
% 1.87/0.62  fof(f426,plain,(
% 1.87/0.62    ( ! [X0,X1] : (r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(k3_subset_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.87/0.62    inference(global_subsumption,[],[f45,f424])).
% 1.87/0.62  fof(f424,plain,(
% 1.87/0.62    ( ! [X0,X1] : (~m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(k3_subset_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.87/0.62    inference(duplicate_literal_removal,[],[f423])).
% 1.87/0.62  fof(f423,plain,(
% 1.87/0.62    ( ! [X0,X1] : (~m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(k3_subset_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.87/0.62    inference(superposition,[],[f349,f39])).
% 1.87/0.62  fof(f39,plain,(
% 1.87/0.62    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.87/0.62    inference(cnf_transformation,[],[f17])).
% 1.87/0.62  fof(f17,plain,(
% 1.87/0.62    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.87/0.62    inference(ennf_transformation,[],[f7])).
% 1.87/0.62  fof(f7,axiom,(
% 1.87/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 1.87/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).
% 1.87/0.62  fof(f349,plain,(
% 1.87/0.62    ( ! [X12,X13] : (~m1_subset_1(k3_subset_1(u1_struct_0(X12),k2_pre_topc(X12,X13)),k1_zfmisc_1(u1_struct_0(X12))) | r1_xboole_0(k3_subset_1(u1_struct_0(X12),k2_pre_topc(X12,X13)),k2_tops_1(X12,X13)) | ~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12))) | ~l1_pre_topc(X12)) )),
% 1.87/0.62    inference(global_subsumption,[],[f46,f344])).
% 1.87/0.62  fof(f344,plain,(
% 1.87/0.62    ( ! [X12,X13] : (~m1_subset_1(k3_subset_1(u1_struct_0(X12),k2_pre_topc(X12,X13)),k1_zfmisc_1(u1_struct_0(X12))) | r1_xboole_0(k3_subset_1(u1_struct_0(X12),k2_pre_topc(X12,X13)),k2_tops_1(X12,X13)) | ~m1_subset_1(k2_tops_1(X12,X13),k1_zfmisc_1(u1_struct_0(X12))) | ~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12))) | ~l1_pre_topc(X12)) )),
% 1.87/0.62    inference(duplicate_literal_removal,[],[f343])).
% 1.87/0.62  fof(f343,plain,(
% 1.87/0.62    ( ! [X12,X13] : (~m1_subset_1(k3_subset_1(u1_struct_0(X12),k2_pre_topc(X12,X13)),k1_zfmisc_1(u1_struct_0(X12))) | r1_xboole_0(k3_subset_1(u1_struct_0(X12),k2_pre_topc(X12,X13)),k2_tops_1(X12,X13)) | ~m1_subset_1(k2_tops_1(X12,X13),k1_zfmisc_1(u1_struct_0(X12))) | ~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12))) | ~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12))) | ~l1_pre_topc(X12)) )),
% 1.87/0.62    inference(superposition,[],[f210,f38])).
% 1.87/0.62  fof(f38,plain,(
% 1.87/0.62    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.87/0.62    inference(cnf_transformation,[],[f16])).
% 1.87/0.62  fof(f16,plain,(
% 1.87/0.62    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.87/0.62    inference(ennf_transformation,[],[f11])).
% 1.87/0.62  fof(f11,axiom,(
% 1.87/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 1.87/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 1.87/0.62  fof(f210,plain,(
% 1.87/0.62    ( ! [X10,X11,X9] : (~m1_subset_1(k3_subset_1(X9,k4_subset_1(X9,X10,X11)),k1_zfmisc_1(X9)) | r1_xboole_0(k3_subset_1(X9,k4_subset_1(X9,X10,X11)),X11) | ~m1_subset_1(X11,k1_zfmisc_1(X9)) | ~m1_subset_1(X10,k1_zfmisc_1(X9))) )),
% 1.87/0.62    inference(duplicate_literal_removal,[],[f199])).
% 1.87/0.62  fof(f199,plain,(
% 1.87/0.62    ( ! [X10,X11,X9] : (r1_xboole_0(k3_subset_1(X9,k4_subset_1(X9,X10,X11)),X11) | ~m1_subset_1(k3_subset_1(X9,k4_subset_1(X9,X10,X11)),k1_zfmisc_1(X9)) | ~m1_subset_1(X11,k1_zfmisc_1(X9)) | ~m1_subset_1(X10,k1_zfmisc_1(X9)) | ~m1_subset_1(X11,k1_zfmisc_1(X9))) )),
% 1.87/0.62    inference(resolution,[],[f194,f111])).
% 1.87/0.62  fof(f111,plain,(
% 1.87/0.62    ( ! [X4,X5,X3] : (r1_tarski(k3_subset_1(X3,k4_subset_1(X3,X5,X4)),k3_subset_1(X3,X4)) | ~m1_subset_1(X5,k1_zfmisc_1(X3)) | ~m1_subset_1(X4,k1_zfmisc_1(X3))) )),
% 1.87/0.62    inference(duplicate_literal_removal,[],[f103])).
% 1.87/0.62  fof(f103,plain,(
% 1.87/0.62    ( ! [X4,X5,X3] : (r1_tarski(k3_subset_1(X3,k4_subset_1(X3,X5,X4)),k3_subset_1(X3,X4)) | ~m1_subset_1(X5,k1_zfmisc_1(X3)) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(X3))) )),
% 1.87/0.62    inference(superposition,[],[f42,f48])).
% 1.87/0.62  fof(f48,plain,(
% 1.87/0.62    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.87/0.62    inference(cnf_transformation,[],[f29])).
% 1.87/0.62  fof(f29,plain,(
% 1.87/0.62    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.87/0.62    inference(flattening,[],[f28])).
% 1.87/0.62  fof(f28,plain,(
% 1.87/0.62    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.87/0.62    inference(ennf_transformation,[],[f1])).
% 1.87/0.62  fof(f1,axiom,(
% 1.87/0.62    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1))),
% 1.87/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_subset_1)).
% 1.87/0.62  fof(f42,plain,(
% 1.87/0.62    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.87/0.62    inference(cnf_transformation,[],[f20])).
% 1.87/0.62  fof(f20,plain,(
% 1.87/0.62    ! [X0,X1] : (! [X2] : (r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.87/0.62    inference(ennf_transformation,[],[f5])).
% 1.87/0.62  fof(f5,axiom,(
% 1.87/0.62    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 1.87/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_subset_1)).
% 1.87/0.62  fof(f194,plain,(
% 1.87/0.62    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_subset_1(X1,X2)) | r1_xboole_0(X0,X2) | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X1))) )),
% 1.87/0.62    inference(duplicate_literal_removal,[],[f190])).
% 1.87/0.62  fof(f190,plain,(
% 1.87/0.62    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_subset_1(X1,X2)) | r1_xboole_0(X0,X2) | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X1))) )),
% 1.87/0.62    inference(resolution,[],[f67,f40])).
% 1.87/0.62  fof(f67,plain,(
% 1.87/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~r1_tarski(X2,k3_subset_1(X0,X1)) | r1_xboole_0(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.87/0.62    inference(superposition,[],[f44,f41])).
% 1.87/0.62  fof(f41,plain,(
% 1.87/0.62    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.87/0.62    inference(cnf_transformation,[],[f19])).
% 1.87/0.62  fof(f19,plain,(
% 1.87/0.62    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.87/0.62    inference(ennf_transformation,[],[f3])).
% 1.87/0.62  fof(f3,axiom,(
% 1.87/0.62    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.87/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.87/0.62  fof(f44,plain,(
% 1.87/0.62    ( ! [X2,X0,X1] : (r1_xboole_0(X1,k3_subset_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.87/0.62    inference(cnf_transformation,[],[f33])).
% 1.87/0.62  fof(f33,plain,(
% 1.87/0.62    ! [X0,X1] : (! [X2] : (((r1_xboole_0(X1,k3_subset_1(X0,X2)) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r1_xboole_0(X1,k3_subset_1(X0,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.87/0.62    inference(nnf_transformation,[],[f21])).
% 1.87/0.62  fof(f21,plain,(
% 1.87/0.62    ! [X0,X1] : (! [X2] : ((r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.87/0.62    inference(ennf_transformation,[],[f6])).
% 1.87/0.62  fof(f6,axiom,(
% 1.87/0.62    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2))))),
% 1.87/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_subset_1)).
% 1.87/0.62  fof(f46,plain,(
% 1.87/0.62    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.87/0.62    inference(cnf_transformation,[],[f25])).
% 1.87/0.62  fof(f25,plain,(
% 1.87/0.62    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.87/0.62    inference(flattening,[],[f24])).
% 1.87/0.62  fof(f24,plain,(
% 1.87/0.62    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.87/0.62    inference(ennf_transformation,[],[f9])).
% 1.87/0.62  fof(f9,axiom,(
% 1.87/0.62    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.87/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 1.87/0.62  fof(f45,plain,(
% 1.87/0.62    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.87/0.62    inference(cnf_transformation,[],[f23])).
% 1.87/0.62  fof(f23,plain,(
% 1.87/0.62    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.87/0.62    inference(flattening,[],[f22])).
% 1.87/0.62  fof(f22,plain,(
% 1.87/0.62    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.87/0.62    inference(ennf_transformation,[],[f8])).
% 1.87/0.62  fof(f8,axiom,(
% 1.87/0.62    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.87/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).
% 1.87/0.62  fof(f311,plain,(
% 1.87/0.62    ~spl2_3 | spl2_4 | ~spl2_2),
% 1.87/0.62    inference(avatar_split_clause,[],[f303,f55,f308,f60])).
% 1.87/0.62  fof(f308,plain,(
% 1.87/0.62    spl2_4 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 1.87/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 1.87/0.62  fof(f303,plain,(
% 1.87/0.62    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0) | ~spl2_2),
% 1.87/0.62    inference(resolution,[],[f298,f57])).
% 1.87/0.62  fof(f57,plain,(
% 1.87/0.62    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_2),
% 1.87/0.62    inference(avatar_component_clause,[],[f55])).
% 1.87/0.62  fof(f298,plain,(
% 1.87/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | r1_tarski(k1_tops_1(X1,X0),X0) | ~l1_pre_topc(X1)) )),
% 1.87/0.62    inference(duplicate_literal_removal,[],[f295])).
% 1.87/0.62  fof(f295,plain,(
% 1.87/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | r1_tarski(k1_tops_1(X1,X0),X0) | ~l1_pre_topc(X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1)) )),
% 1.87/0.62    inference(resolution,[],[f294,f45])).
% 1.87/0.62  fof(f294,plain,(
% 1.87/0.62    ( ! [X0,X1] : (~m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) )),
% 1.87/0.62    inference(duplicate_literal_removal,[],[f288])).
% 1.87/0.62  fof(f288,plain,(
% 1.87/0.62    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.87/0.62    inference(resolution,[],[f285,f43])).
% 1.87/0.62  fof(f43,plain,(
% 1.87/0.62    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,k3_subset_1(X0,X2)) | r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.87/0.62    inference(cnf_transformation,[],[f33])).
% 1.87/0.62  fof(f285,plain,(
% 1.87/0.62    ( ! [X2,X3] : (r1_xboole_0(k1_tops_1(X2,X3),k3_subset_1(u1_struct_0(X2),X3)) | ~l1_pre_topc(X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) )),
% 1.87/0.62    inference(duplicate_literal_removal,[],[f280])).
% 1.87/0.62  fof(f280,plain,(
% 1.87/0.62    ( ! [X2,X3] : (r1_xboole_0(k1_tops_1(X2,X3),k3_subset_1(u1_struct_0(X2),X3)) | ~l1_pre_topc(X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) )),
% 1.87/0.62    inference(resolution,[],[f264,f40])).
% 1.87/0.62  fof(f264,plain,(
% 1.87/0.62    ( ! [X0,X1] : (~m1_subset_1(k3_subset_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | r1_xboole_0(k1_tops_1(X0,X1),k3_subset_1(u1_struct_0(X0),X1)) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.87/0.62    inference(global_subsumption,[],[f45,f262])).
% 1.87/0.62  fof(f262,plain,(
% 1.87/0.62    ( ! [X0,X1] : (~m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | r1_xboole_0(k1_tops_1(X0,X1),k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(k3_subset_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.87/0.62    inference(duplicate_literal_removal,[],[f261])).
% 1.87/0.62  fof(f261,plain,(
% 1.87/0.62    ( ! [X0,X1] : (~m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | r1_xboole_0(k1_tops_1(X0,X1),k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(k3_subset_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.87/0.62    inference(superposition,[],[f209,f39])).
% 1.87/0.62  fof(f209,plain,(
% 1.87/0.62    ( ! [X28,X29] : (~m1_subset_1(k3_subset_1(u1_struct_0(X28),k2_pre_topc(X28,X29)),k1_zfmisc_1(u1_struct_0(X28))) | r1_xboole_0(k3_subset_1(u1_struct_0(X28),k2_pre_topc(X28,X29)),X29) | ~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28))) | ~l1_pre_topc(X28)) )),
% 1.87/0.62    inference(duplicate_literal_removal,[],[f204])).
% 1.87/0.62  fof(f204,plain,(
% 1.87/0.62    ( ! [X28,X29] : (r1_xboole_0(k3_subset_1(u1_struct_0(X28),k2_pre_topc(X28,X29)),X29) | ~m1_subset_1(k3_subset_1(u1_struct_0(X28),k2_pre_topc(X28,X29)),k1_zfmisc_1(u1_struct_0(X28))) | ~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28))) | ~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28))) | ~l1_pre_topc(X28)) )),
% 1.87/0.62    inference(resolution,[],[f194,f113])).
% 1.87/0.62  fof(f113,plain,(
% 1.87/0.62    ( ! [X12,X13] : (r1_tarski(k3_subset_1(u1_struct_0(X12),k2_pre_topc(X12,X13)),k3_subset_1(u1_struct_0(X12),X13)) | ~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12))) | ~l1_pre_topc(X12)) )),
% 1.87/0.62    inference(global_subsumption,[],[f46,f108])).
% 1.87/0.62  fof(f108,plain,(
% 1.87/0.62    ( ! [X12,X13] : (r1_tarski(k3_subset_1(u1_struct_0(X12),k2_pre_topc(X12,X13)),k3_subset_1(u1_struct_0(X12),X13)) | ~m1_subset_1(k2_tops_1(X12,X13),k1_zfmisc_1(u1_struct_0(X12))) | ~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12))) | ~l1_pre_topc(X12)) )),
% 1.87/0.62    inference(duplicate_literal_removal,[],[f106])).
% 1.87/0.62  fof(f106,plain,(
% 1.87/0.62    ( ! [X12,X13] : (r1_tarski(k3_subset_1(u1_struct_0(X12),k2_pre_topc(X12,X13)),k3_subset_1(u1_struct_0(X12),X13)) | ~m1_subset_1(k2_tops_1(X12,X13),k1_zfmisc_1(u1_struct_0(X12))) | ~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12))) | ~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12))) | ~l1_pre_topc(X12)) )),
% 1.87/0.62    inference(superposition,[],[f42,f38])).
% 1.87/0.62  fof(f63,plain,(
% 1.87/0.62    spl2_3),
% 1.87/0.62    inference(avatar_split_clause,[],[f34,f60])).
% 1.87/0.62  fof(f34,plain,(
% 1.87/0.62    l1_pre_topc(sK0)),
% 1.87/0.62    inference(cnf_transformation,[],[f32])).
% 1.87/0.62  fof(f32,plain,(
% 1.87/0.62    (~r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 1.87/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f31,f30])).
% 1.87/0.62  fof(f30,plain,(
% 1.87/0.62    ? [X0] : (? [X1] : (~r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (~r1_xboole_0(k1_tops_1(sK0,X1),k2_tops_1(sK0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 1.87/0.62    introduced(choice_axiom,[])).
% 1.87/0.62  fof(f31,plain,(
% 1.87/0.62    ? [X1] : (~r1_xboole_0(k1_tops_1(sK0,X1),k2_tops_1(sK0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (~r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.87/0.62    introduced(choice_axiom,[])).
% 1.87/0.62  fof(f14,plain,(
% 1.87/0.62    ? [X0] : (? [X1] : (~r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.87/0.62    inference(ennf_transformation,[],[f13])).
% 1.87/0.62  fof(f13,negated_conjecture,(
% 1.87/0.62    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))))),
% 1.87/0.62    inference(negated_conjecture,[],[f12])).
% 1.87/0.62  fof(f12,conjecture,(
% 1.87/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))))),
% 1.87/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_tops_1)).
% 1.87/0.62  fof(f58,plain,(
% 1.87/0.62    spl2_2),
% 1.87/0.62    inference(avatar_split_clause,[],[f35,f55])).
% 1.87/0.62  fof(f35,plain,(
% 1.87/0.62    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.87/0.62    inference(cnf_transformation,[],[f32])).
% 1.87/0.62  fof(f53,plain,(
% 1.87/0.62    ~spl2_1),
% 1.87/0.62    inference(avatar_split_clause,[],[f36,f50])).
% 1.87/0.62  fof(f36,plain,(
% 1.87/0.62    ~r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))),
% 1.87/0.62    inference(cnf_transformation,[],[f32])).
% 1.87/0.62  % SZS output end Proof for theBenchmark
% 1.87/0.62  % (10486)------------------------------
% 1.87/0.62  % (10486)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.62  % (10486)Termination reason: Refutation
% 1.87/0.62  
% 1.87/0.62  % (10486)Memory used [KB]: 6396
% 1.87/0.62  % (10486)Time elapsed: 0.229 s
% 1.87/0.62  % (10486)------------------------------
% 1.87/0.62  % (10486)------------------------------
% 2.23/0.64  % (10481)Success in time 0.289 s
%------------------------------------------------------------------------------
