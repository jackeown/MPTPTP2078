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
% DateTime   : Thu Dec  3 13:11:25 EST 2020

% Result     : Theorem 0.80s
% Output     : Refutation 0.80s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 179 expanded)
%              Number of leaves         :   21 (  61 expanded)
%              Depth                    :   17
%              Number of atoms          :  191 ( 402 expanded)
%              Number of equality atoms :   40 ( 102 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f146,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f72,f74,f141,f143,f145])).

fof(f145,plain,(
    ~ spl2_6 ),
    inference(avatar_contradiction_clause,[],[f144])).

fof(f144,plain,
    ( $false
    | ~ spl2_6 ),
    inference(resolution,[],[f140,f32])).

fof(f32,plain,(
    ~ r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),sK1)
    & v4_pre_topc(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k2_tops_1(X0,X1),X1)
            & v4_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(sK0,X1),X1)
          & v4_pre_topc(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k2_tops_1(sK0,X1),X1)
        & v4_pre_topc(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r1_tarski(k2_tops_1(sK0,sK1),sK1)
      & v4_pre_topc(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),X1)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),X1)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

fof(f140,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl2_6
  <=> r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f143,plain,(
    spl2_5 ),
    inference(avatar_contradiction_clause,[],[f142])).

fof(f142,plain,
    ( $false
    | spl2_5 ),
    inference(resolution,[],[f136,f30])).

fof(f30,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f136,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_5 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl2_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f141,plain,
    ( ~ spl2_1
    | ~ spl2_5
    | spl2_6
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f130,f63,f138,f134,f59])).

fof(f59,plain,
    ( spl2_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f63,plain,
    ( spl2_2
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f130,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(superposition,[],[f129,f65])).

fof(f65,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f129,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f128])).

fof(f128,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f97,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,X1))
      | ~ m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f84,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k4_subset_1(X2,X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X2)) ) ),
    inference(superposition,[],[f75,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f41,f51])).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f37,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f38,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f40,f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f42,f47])).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f43,f46])).

fof(f46,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f44,f45])).

fof(f45,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f44,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f43,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f40,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f38,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f75,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) ),
    inference(superposition,[],[f52,f53])).

fof(f53,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f36,f51,f51])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f35,f51])).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f74,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f73])).

fof(f73,plain,
    ( $false
    | spl2_3 ),
    inference(resolution,[],[f69,f31])).

fof(f31,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f69,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl2_3
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f72,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f71])).

fof(f71,plain,
    ( $false
    | spl2_1 ),
    inference(resolution,[],[f61,f29])).

fof(f29,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f61,plain,
    ( ~ l1_pre_topc(sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f70,plain,
    ( ~ spl2_1
    | spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f55,f67,f63,f59])).

fof(f55,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | sK1 = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f34,f30])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => k2_pre_topc(X0,X1) = X1 ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:17:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.37  ipcrm: permission denied for id (1223458817)
% 0.13/0.37  ipcrm: permission denied for id (1223557124)
% 0.13/0.37  ipcrm: permission denied for id (1223622662)
% 0.13/0.38  ipcrm: permission denied for id (1223720969)
% 0.13/0.38  ipcrm: permission denied for id (1223753738)
% 0.13/0.38  ipcrm: permission denied for id (1223786507)
% 0.13/0.38  ipcrm: permission denied for id (1223819276)
% 0.13/0.38  ipcrm: permission denied for id (1223917583)
% 0.13/0.39  ipcrm: permission denied for id (1224015890)
% 0.13/0.39  ipcrm: permission denied for id (1224048659)
% 0.13/0.39  ipcrm: permission denied for id (1224114197)
% 0.13/0.39  ipcrm: permission denied for id (1224146966)
% 0.13/0.40  ipcrm: permission denied for id (1224278041)
% 0.13/0.40  ipcrm: permission denied for id (1224310810)
% 0.13/0.40  ipcrm: permission denied for id (1224343579)
% 0.13/0.40  ipcrm: permission denied for id (1224376348)
% 0.20/0.40  ipcrm: permission denied for id (1224507424)
% 0.20/0.41  ipcrm: permission denied for id (1224572962)
% 0.20/0.41  ipcrm: permission denied for id (1224605731)
% 0.20/0.41  ipcrm: permission denied for id (1224638500)
% 0.20/0.41  ipcrm: permission denied for id (1224671269)
% 0.20/0.41  ipcrm: permission denied for id (1224704038)
% 0.20/0.42  ipcrm: permission denied for id (1224769576)
% 0.20/0.42  ipcrm: permission denied for id (1224966190)
% 0.20/0.42  ipcrm: permission denied for id (1224998959)
% 0.20/0.43  ipcrm: permission denied for id (1225130035)
% 0.20/0.43  ipcrm: permission denied for id (1225228342)
% 0.20/0.43  ipcrm: permission denied for id (1225261111)
% 0.20/0.44  ipcrm: permission denied for id (1225326649)
% 0.20/0.44  ipcrm: permission denied for id (1225359418)
% 0.20/0.44  ipcrm: permission denied for id (1225424956)
% 0.20/0.44  ipcrm: permission denied for id (1225490494)
% 0.20/0.45  ipcrm: permission denied for id (1225588801)
% 0.20/0.45  ipcrm: permission denied for id (1225752645)
% 0.20/0.45  ipcrm: permission denied for id (1225785414)
% 0.20/0.46  ipcrm: permission denied for id (1225818183)
% 0.20/0.46  ipcrm: permission denied for id (1225850952)
% 0.20/0.46  ipcrm: permission denied for id (1225883721)
% 0.20/0.47  ipcrm: permission denied for id (1226113103)
% 0.20/0.47  ipcrm: permission denied for id (1226178641)
% 0.20/0.47  ipcrm: permission denied for id (1226244179)
% 0.20/0.47  ipcrm: permission denied for id (1226309717)
% 0.20/0.47  ipcrm: permission denied for id (1226342486)
% 0.20/0.48  ipcrm: permission denied for id (1226375255)
% 0.20/0.48  ipcrm: permission denied for id (1226408024)
% 0.20/0.48  ipcrm: permission denied for id (1226506331)
% 0.20/0.48  ipcrm: permission denied for id (1226539100)
% 0.20/0.48  ipcrm: permission denied for id (1226571869)
% 0.20/0.49  ipcrm: permission denied for id (1226604638)
% 0.20/0.49  ipcrm: permission denied for id (1226637407)
% 0.20/0.49  ipcrm: permission denied for id (1226702945)
% 0.20/0.49  ipcrm: permission denied for id (1226735714)
% 0.20/0.49  ipcrm: permission denied for id (1226768483)
% 0.20/0.50  ipcrm: permission denied for id (1226899558)
% 0.20/0.50  ipcrm: permission denied for id (1226997863)
% 0.20/0.51  ipcrm: permission denied for id (1227194478)
% 0.20/0.51  ipcrm: permission denied for id (1227227247)
% 0.20/0.51  ipcrm: permission denied for id (1227260016)
% 0.20/0.52  ipcrm: permission denied for id (1227456630)
% 0.20/0.52  ipcrm: permission denied for id (1227489399)
% 0.20/0.52  ipcrm: permission denied for id (1227587706)
% 0.63/0.60  % (26100)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.80/0.60  % (26100)Refutation found. Thanks to Tanya!
% 0.80/0.60  % SZS status Theorem for theBenchmark
% 0.80/0.60  % SZS output start Proof for theBenchmark
% 0.80/0.60  fof(f146,plain,(
% 0.80/0.60    $false),
% 0.80/0.60    inference(avatar_sat_refutation,[],[f70,f72,f74,f141,f143,f145])).
% 0.80/0.60  fof(f145,plain,(
% 0.80/0.60    ~spl2_6),
% 0.80/0.60    inference(avatar_contradiction_clause,[],[f144])).
% 0.80/0.60  fof(f144,plain,(
% 0.80/0.60    $false | ~spl2_6),
% 0.80/0.60    inference(resolution,[],[f140,f32])).
% 0.80/0.60  fof(f32,plain,(
% 0.80/0.60    ~r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 0.80/0.60    inference(cnf_transformation,[],[f28])).
% 0.80/0.60  fof(f28,plain,(
% 0.80/0.60    (~r1_tarski(k2_tops_1(sK0,sK1),sK1) & v4_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.80/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f27,f26])).
% 0.80/0.60  fof(f26,plain,(
% 0.80/0.60    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),X1) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (~r1_tarski(k2_tops_1(sK0,X1),X1) & v4_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.80/0.60    introduced(choice_axiom,[])).
% 0.80/0.60  fof(f27,plain,(
% 0.80/0.60    ? [X1] : (~r1_tarski(k2_tops_1(sK0,X1),X1) & v4_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (~r1_tarski(k2_tops_1(sK0,sK1),sK1) & v4_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.80/0.60    introduced(choice_axiom,[])).
% 0.80/0.60  fof(f18,plain,(
% 0.80/0.60    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),X1) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.80/0.60    inference(flattening,[],[f17])).
% 0.80/0.60  fof(f17,plain,(
% 0.80/0.60    ? [X0] : (? [X1] : ((~r1_tarski(k2_tops_1(X0,X1),X1) & v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.80/0.60    inference(ennf_transformation,[],[f15])).
% 0.80/0.60  fof(f15,negated_conjecture,(
% 0.80/0.60    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 0.80/0.60    inference(negated_conjecture,[],[f14])).
% 0.80/0.60  fof(f14,conjecture,(
% 0.80/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 0.80/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).
% 0.80/0.60  fof(f140,plain,(
% 0.80/0.60    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl2_6),
% 0.80/0.60    inference(avatar_component_clause,[],[f138])).
% 0.80/0.60  fof(f138,plain,(
% 0.80/0.60    spl2_6 <=> r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 0.80/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.80/0.60  fof(f143,plain,(
% 0.80/0.60    spl2_5),
% 0.80/0.60    inference(avatar_contradiction_clause,[],[f142])).
% 0.80/0.60  fof(f142,plain,(
% 0.80/0.60    $false | spl2_5),
% 0.80/0.60    inference(resolution,[],[f136,f30])).
% 0.80/0.60  fof(f30,plain,(
% 0.80/0.60    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.80/0.60    inference(cnf_transformation,[],[f28])).
% 0.80/0.60  fof(f136,plain,(
% 0.80/0.60    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl2_5),
% 0.80/0.60    inference(avatar_component_clause,[],[f134])).
% 0.80/0.60  fof(f134,plain,(
% 0.80/0.60    spl2_5 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.80/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.80/0.60  fof(f141,plain,(
% 0.80/0.60    ~spl2_1 | ~spl2_5 | spl2_6 | ~spl2_2),
% 0.80/0.60    inference(avatar_split_clause,[],[f130,f63,f138,f134,f59])).
% 0.80/0.60  fof(f59,plain,(
% 0.80/0.60    spl2_1 <=> l1_pre_topc(sK0)),
% 0.80/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.80/0.60  fof(f63,plain,(
% 0.80/0.60    spl2_2 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 0.80/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.80/0.60  fof(f130,plain,(
% 0.80/0.60    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_2),
% 0.80/0.60    inference(superposition,[],[f129,f65])).
% 0.80/0.60  fof(f65,plain,(
% 0.80/0.60    sK1 = k2_pre_topc(sK0,sK1) | ~spl2_2),
% 0.80/0.60    inference(avatar_component_clause,[],[f63])).
% 0.80/0.60  fof(f129,plain,(
% 0.80/0.60    ( ! [X0,X1] : (r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.80/0.60    inference(duplicate_literal_removal,[],[f128])).
% 0.80/0.60  fof(f128,plain,(
% 0.80/0.60    ( ! [X0,X1] : (r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.80/0.60    inference(resolution,[],[f97,f39])).
% 0.80/0.60  fof(f39,plain,(
% 0.80/0.60    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.80/0.60    inference(cnf_transformation,[],[f23])).
% 0.80/0.60  fof(f23,plain,(
% 0.80/0.60    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.80/0.60    inference(flattening,[],[f22])).
% 0.80/0.60  fof(f22,plain,(
% 0.80/0.60    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.80/0.60    inference(ennf_transformation,[],[f12])).
% 0.80/0.60  fof(f12,axiom,(
% 0.80/0.60    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.80/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 0.80/0.60  fof(f97,plain,(
% 0.80/0.60    ( ! [X0,X1] : (~m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.80/0.60    inference(duplicate_literal_removal,[],[f94])).
% 0.80/0.60  fof(f94,plain,(
% 0.80/0.60    ( ! [X0,X1] : (r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,X1)) | ~m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.80/0.60    inference(superposition,[],[f84,f33])).
% 0.80/0.60  fof(f33,plain,(
% 0.80/0.60    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.80/0.60    inference(cnf_transformation,[],[f19])).
% 0.80/0.60  fof(f19,plain,(
% 0.80/0.60    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.80/0.60    inference(ennf_transformation,[],[f13])).
% 0.80/0.60  fof(f13,axiom,(
% 0.80/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.80/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 0.80/0.60  fof(f84,plain,(
% 0.80/0.60    ( ! [X2,X0,X1] : (r1_tarski(X1,k4_subset_1(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~m1_subset_1(X0,k1_zfmisc_1(X2))) )),
% 0.80/0.60    inference(superposition,[],[f75,f54])).
% 0.80/0.60  fof(f54,plain,(
% 0.80/0.60    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.80/0.60    inference(definition_unfolding,[],[f41,f51])).
% 0.80/0.60  fof(f51,plain,(
% 0.80/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.80/0.60    inference(definition_unfolding,[],[f37,f50])).
% 0.80/0.60  fof(f50,plain,(
% 0.80/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.80/0.60    inference(definition_unfolding,[],[f38,f49])).
% 0.80/0.60  fof(f49,plain,(
% 0.80/0.60    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.80/0.60    inference(definition_unfolding,[],[f40,f48])).
% 0.80/0.60  fof(f48,plain,(
% 0.80/0.60    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.80/0.60    inference(definition_unfolding,[],[f42,f47])).
% 0.80/0.60  fof(f47,plain,(
% 0.80/0.60    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.80/0.60    inference(definition_unfolding,[],[f43,f46])).
% 0.80/0.60  fof(f46,plain,(
% 0.80/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.80/0.60    inference(definition_unfolding,[],[f44,f45])).
% 0.80/0.60  fof(f45,plain,(
% 0.80/0.60    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.80/0.60    inference(cnf_transformation,[],[f8])).
% 0.80/0.60  fof(f8,axiom,(
% 0.80/0.60    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.80/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.80/0.60  fof(f44,plain,(
% 0.80/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.80/0.60    inference(cnf_transformation,[],[f7])).
% 0.80/0.60  fof(f7,axiom,(
% 0.80/0.60    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.80/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.80/0.60  fof(f43,plain,(
% 0.80/0.60    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.80/0.60    inference(cnf_transformation,[],[f6])).
% 0.80/0.60  fof(f6,axiom,(
% 0.80/0.60    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.80/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.80/0.60  fof(f42,plain,(
% 0.80/0.60    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.80/0.60    inference(cnf_transformation,[],[f5])).
% 0.80/0.60  fof(f5,axiom,(
% 0.80/0.60    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.80/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.80/0.60  fof(f40,plain,(
% 0.80/0.60    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.80/0.60    inference(cnf_transformation,[],[f4])).
% 0.80/0.60  fof(f4,axiom,(
% 0.80/0.60    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.80/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.80/0.60  fof(f38,plain,(
% 0.80/0.60    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.80/0.60    inference(cnf_transformation,[],[f3])).
% 0.80/0.60  fof(f3,axiom,(
% 0.80/0.60    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.80/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.80/0.60  fof(f37,plain,(
% 0.80/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.80/0.60    inference(cnf_transformation,[],[f9])).
% 0.80/0.60  fof(f9,axiom,(
% 0.80/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.80/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.80/0.60  fof(f41,plain,(
% 0.80/0.60    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.80/0.60    inference(cnf_transformation,[],[f25])).
% 0.80/0.60  fof(f25,plain,(
% 0.80/0.60    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.80/0.60    inference(flattening,[],[f24])).
% 0.80/0.60  fof(f24,plain,(
% 0.80/0.60    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.80/0.60    inference(ennf_transformation,[],[f10])).
% 0.80/0.60  fof(f10,axiom,(
% 0.80/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.80/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.80/0.60  fof(f75,plain,(
% 0.80/0.60    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))) )),
% 0.80/0.60    inference(superposition,[],[f52,f53])).
% 0.80/0.60  fof(f53,plain,(
% 0.80/0.60    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) )),
% 0.80/0.60    inference(definition_unfolding,[],[f36,f51,f51])).
% 0.80/0.60  fof(f36,plain,(
% 0.80/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.80/0.60    inference(cnf_transformation,[],[f1])).
% 0.80/0.60  fof(f1,axiom,(
% 0.80/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.80/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.80/0.60  fof(f52,plain,(
% 0.80/0.60    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 0.80/0.60    inference(definition_unfolding,[],[f35,f51])).
% 0.80/0.60  fof(f35,plain,(
% 0.80/0.60    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.80/0.60    inference(cnf_transformation,[],[f2])).
% 0.80/0.60  fof(f2,axiom,(
% 0.80/0.60    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.80/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.80/0.60  fof(f74,plain,(
% 0.80/0.60    spl2_3),
% 0.80/0.60    inference(avatar_contradiction_clause,[],[f73])).
% 0.80/0.60  fof(f73,plain,(
% 0.80/0.60    $false | spl2_3),
% 0.80/0.60    inference(resolution,[],[f69,f31])).
% 0.80/0.60  fof(f31,plain,(
% 0.80/0.60    v4_pre_topc(sK1,sK0)),
% 0.80/0.60    inference(cnf_transformation,[],[f28])).
% 0.80/0.60  fof(f69,plain,(
% 0.80/0.60    ~v4_pre_topc(sK1,sK0) | spl2_3),
% 0.80/0.60    inference(avatar_component_clause,[],[f67])).
% 0.80/0.60  fof(f67,plain,(
% 0.80/0.60    spl2_3 <=> v4_pre_topc(sK1,sK0)),
% 0.80/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.80/0.60  fof(f72,plain,(
% 0.80/0.60    spl2_1),
% 0.80/0.60    inference(avatar_contradiction_clause,[],[f71])).
% 0.80/0.60  fof(f71,plain,(
% 0.80/0.60    $false | spl2_1),
% 0.80/0.60    inference(resolution,[],[f61,f29])).
% 0.80/0.60  fof(f29,plain,(
% 0.80/0.60    l1_pre_topc(sK0)),
% 0.80/0.60    inference(cnf_transformation,[],[f28])).
% 0.80/0.60  fof(f61,plain,(
% 0.80/0.60    ~l1_pre_topc(sK0) | spl2_1),
% 0.80/0.60    inference(avatar_component_clause,[],[f59])).
% 0.80/0.60  fof(f70,plain,(
% 0.80/0.60    ~spl2_1 | spl2_2 | ~spl2_3),
% 0.80/0.60    inference(avatar_split_clause,[],[f55,f67,f63,f59])).
% 0.80/0.60  fof(f55,plain,(
% 0.80/0.60    ~v4_pre_topc(sK1,sK0) | sK1 = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0)),
% 0.80/0.60    inference(resolution,[],[f34,f30])).
% 0.80/0.60  fof(f34,plain,(
% 0.80/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~l1_pre_topc(X0)) )),
% 0.80/0.60    inference(cnf_transformation,[],[f21])).
% 0.80/0.60  fof(f21,plain,(
% 0.80/0.60    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.80/0.60    inference(flattening,[],[f20])).
% 0.80/0.60  fof(f20,plain,(
% 0.80/0.60    ! [X0] : (! [X1] : ((k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.80/0.60    inference(ennf_transformation,[],[f16])).
% 0.80/0.60  fof(f16,plain,(
% 0.80/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1)))),
% 0.80/0.60    inference(pure_predicate_removal,[],[f11])).
% 0.80/0.60  fof(f11,axiom,(
% 0.80/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.80/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.80/0.60  % SZS output end Proof for theBenchmark
% 0.80/0.60  % (26100)------------------------------
% 0.80/0.60  % (26100)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.80/0.60  % (26100)Termination reason: Refutation
% 0.80/0.60  
% 0.80/0.60  % (26100)Memory used [KB]: 6140
% 0.80/0.60  % (26100)Time elapsed: 0.038 s
% 0.80/0.60  % (26100)------------------------------
% 0.80/0.60  % (26100)------------------------------
% 0.80/0.61  % (25869)Success in time 0.248 s
%------------------------------------------------------------------------------
