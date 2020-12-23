%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:43 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 190 expanded)
%              Number of leaves         :   20 (  54 expanded)
%              Depth                    :   12
%              Number of atoms          :  262 ( 625 expanded)
%              Number of equality atoms :   58 ( 128 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f317,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f58,f65,f273,f275,f277,f279,f283,f311,f316])).

fof(f316,plain,
    ( ~ spl2_7
    | ~ spl2_9
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f313,f63,f270,f264])).

fof(f264,plain,
    ( spl2_7
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f270,plain,
    ( spl2_9
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f63,plain,
    ( spl2_4
  <=> ! [X0,X2] :
        ( ~ v2_pre_topc(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f313,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_4 ),
    inference(resolution,[],[f64,f33])).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

fof(f64,plain,
    ( ! [X2,X0] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f63])).

fof(f311,plain,
    ( spl2_2
    | ~ spl2_10 ),
    inference(avatar_contradiction_clause,[],[f310])).

fof(f310,plain,
    ( $false
    | spl2_2
    | ~ spl2_10 ),
    inference(trivial_inequality_removal,[],[f308])).

fof(f308,plain,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1)
    | spl2_2
    | ~ spl2_10 ),
    inference(superposition,[],[f54,f305])).

fof(f305,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_10 ),
    inference(forward_demodulation,[],[f128,f282])).

fof(f282,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f281])).

fof(f281,plain,
    ( spl2_10
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f128,plain,(
    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(global_subsumption,[],[f35,f125])).

fof(f125,plain,
    ( ~ l1_pre_topc(sK0)
    | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f39,f33])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f35,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f54,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl2_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f283,plain,
    ( ~ spl2_7
    | ~ spl2_1
    | spl2_10
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f102,f60,f281,f50,f264])).

fof(f50,plain,
    ( spl2_1
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f60,plain,
    ( spl2_3
  <=> ! [X1,X3] :
        ( ~ l1_pre_topc(X1)
        | k1_tops_1(X1,X3) = X3
        | ~ v3_pre_topc(X3,X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f102,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_3 ),
    inference(resolution,[],[f61,f33])).

fof(f61,plain,
    ( ! [X3,X1] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | k1_tops_1(X1,X3) = X3
        | ~ v3_pre_topc(X3,X1)
        | ~ l1_pre_topc(X1) )
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f279,plain,(
    spl2_8 ),
    inference(avatar_contradiction_clause,[],[f278])).

fof(f278,plain,
    ( $false
    | spl2_8 ),
    inference(resolution,[],[f268,f33])).

fof(f268,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_8 ),
    inference(avatar_component_clause,[],[f267])).

fof(f267,plain,
    ( spl2_8
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f277,plain,(
    spl2_9 ),
    inference(avatar_contradiction_clause,[],[f276])).

fof(f276,plain,
    ( $false
    | spl2_9 ),
    inference(resolution,[],[f271,f34])).

fof(f34,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f271,plain,
    ( ~ v2_pre_topc(sK0)
    | spl2_9 ),
    inference(avatar_component_clause,[],[f270])).

fof(f275,plain,(
    spl2_7 ),
    inference(avatar_contradiction_clause,[],[f274])).

fof(f274,plain,
    ( $false
    | spl2_7 ),
    inference(resolution,[],[f265,f35])).

fof(f265,plain,
    ( ~ l1_pre_topc(sK0)
    | spl2_7 ),
    inference(avatar_component_clause,[],[f264])).

fof(f273,plain,
    ( ~ spl2_9
    | ~ spl2_8
    | ~ spl2_7
    | spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f260,f53,f50,f264,f267,f270])).

fof(f260,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(superposition,[],[f45,f244])).

fof(f244,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f116,f186])).

fof(f186,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f137,f182])).

fof(f182,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_2 ),
    inference(superposition,[],[f147,f57])).

fof(f57,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f147,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) = k4_xboole_0(k2_pre_topc(sK0,sK1),X0) ),
    inference(global_subsumption,[],[f35,f144])).

fof(f144,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) = k4_xboole_0(k2_pre_topc(sK0,sK1),X0) ) ),
    inference(resolution,[],[f101,f33])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),X2) = k4_xboole_0(k2_pre_topc(X1,X0),X2) ) ),
    inference(resolution,[],[f46,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f137,plain,(
    sK1 = k4_xboole_0(sK1,k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)) ),
    inference(superposition,[],[f81,f133])).

fof(f133,plain,(
    sK1 = k3_xboole_0(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(global_subsumption,[],[f35,f130])).

fof(f130,plain,
    ( ~ l1_pre_topc(sK0)
    | sK1 = k3_xboole_0(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f82,f33])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | k3_xboole_0(X0,k2_pre_topc(X1,X0)) = X0 ) ),
    inference(resolution,[],[f36,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f81,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k4_xboole_0(k3_xboole_0(X2,X3),k4_xboole_0(X3,X2)) ),
    inference(resolution,[],[f47,f73])).

fof(f73,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X1,X0),k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f43,f42])).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f43,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_xboole_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(X0,X1) = X0 ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f116,plain,(
    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(global_subsumption,[],[f35,f115])).

fof(f115,plain,
    ( k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(forward_demodulation,[],[f112,f89])).

fof(f89,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(resolution,[],[f48,f33])).

fof(f112,plain,
    ( ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f38,f33])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f65,plain,
    ( spl2_3
    | spl2_4 ),
    inference(avatar_split_clause,[],[f41,f63,f60])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v3_pre_topc(X3,X1)
      | k1_tops_1(X1,X3) = X3 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k1_tops_1(X0,X2) = X2
                     => v3_pre_topc(X2,X0) )
                    & ( v3_pre_topc(X3,X1)
                     => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).

fof(f58,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f31,f53,f50])).

fof(f31,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f55,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f32,f53,f50])).

fof(f32,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:13:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.46  % (32525)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.19/0.46  % (32523)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.19/0.47  % (32523)Refutation found. Thanks to Tanya!
% 0.19/0.47  % SZS status Theorem for theBenchmark
% 0.19/0.47  % SZS output start Proof for theBenchmark
% 0.19/0.47  fof(f317,plain,(
% 0.19/0.47    $false),
% 0.19/0.47    inference(avatar_sat_refutation,[],[f55,f58,f65,f273,f275,f277,f279,f283,f311,f316])).
% 0.19/0.47  fof(f316,plain,(
% 0.19/0.47    ~spl2_7 | ~spl2_9 | ~spl2_4),
% 0.19/0.47    inference(avatar_split_clause,[],[f313,f63,f270,f264])).
% 0.19/0.47  fof(f264,plain,(
% 0.19/0.47    spl2_7 <=> l1_pre_topc(sK0)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.19/0.47  fof(f270,plain,(
% 0.19/0.47    spl2_9 <=> v2_pre_topc(sK0)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.19/0.47  fof(f63,plain,(
% 0.19/0.47    spl2_4 <=> ! [X0,X2] : (~v2_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.19/0.47  fof(f313,plain,(
% 0.19/0.47    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~spl2_4),
% 0.19/0.47    inference(resolution,[],[f64,f33])).
% 0.19/0.47  fof(f33,plain,(
% 0.19/0.47    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.47    inference(cnf_transformation,[],[f17])).
% 0.19/0.47  fof(f17,plain,(
% 0.19/0.47    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.19/0.47    inference(flattening,[],[f16])).
% 0.19/0.47  fof(f16,plain,(
% 0.19/0.47    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.19/0.47    inference(ennf_transformation,[],[f14])).
% 0.19/0.47  fof(f14,negated_conjecture,(
% 0.19/0.47    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 0.19/0.47    inference(negated_conjecture,[],[f13])).
% 0.19/0.47  fof(f13,conjecture,(
% 0.19/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).
% 0.19/0.47  fof(f64,plain,(
% 0.19/0.47    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) ) | ~spl2_4),
% 0.19/0.47    inference(avatar_component_clause,[],[f63])).
% 0.19/0.47  fof(f311,plain,(
% 0.19/0.47    spl2_2 | ~spl2_10),
% 0.19/0.47    inference(avatar_contradiction_clause,[],[f310])).
% 0.19/0.47  fof(f310,plain,(
% 0.19/0.47    $false | (spl2_2 | ~spl2_10)),
% 0.19/0.47    inference(trivial_inequality_removal,[],[f308])).
% 0.19/0.47  fof(f308,plain,(
% 0.19/0.47    k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1) | (spl2_2 | ~spl2_10)),
% 0.19/0.47    inference(superposition,[],[f54,f305])).
% 0.19/0.47  fof(f305,plain,(
% 0.19/0.47    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl2_10),
% 0.19/0.47    inference(forward_demodulation,[],[f128,f282])).
% 0.19/0.48  fof(f282,plain,(
% 0.19/0.48    sK1 = k1_tops_1(sK0,sK1) | ~spl2_10),
% 0.19/0.48    inference(avatar_component_clause,[],[f281])).
% 0.19/0.48  fof(f281,plain,(
% 0.19/0.48    spl2_10 <=> sK1 = k1_tops_1(sK0,sK1)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.19/0.48  fof(f128,plain,(
% 0.19/0.48    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 0.19/0.48    inference(global_subsumption,[],[f35,f125])).
% 0.19/0.48  fof(f125,plain,(
% 0.19/0.48    ~l1_pre_topc(sK0) | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 0.19/0.48    inference(resolution,[],[f39,f33])).
% 0.19/0.48  fof(f39,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))) )),
% 0.19/0.48    inference(cnf_transformation,[],[f21])).
% 0.19/0.48  fof(f21,plain,(
% 0.19/0.48    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.48    inference(ennf_transformation,[],[f9])).
% 0.19/0.48  fof(f9,axiom,(
% 0.19/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 0.19/0.48  fof(f35,plain,(
% 0.19/0.48    l1_pre_topc(sK0)),
% 0.19/0.48    inference(cnf_transformation,[],[f17])).
% 0.19/0.48  fof(f54,plain,(
% 0.19/0.48    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | spl2_2),
% 0.19/0.48    inference(avatar_component_clause,[],[f53])).
% 0.19/0.48  fof(f53,plain,(
% 0.19/0.48    spl2_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.19/0.48  fof(f283,plain,(
% 0.19/0.48    ~spl2_7 | ~spl2_1 | spl2_10 | ~spl2_3),
% 0.19/0.48    inference(avatar_split_clause,[],[f102,f60,f281,f50,f264])).
% 0.19/0.48  fof(f50,plain,(
% 0.19/0.48    spl2_1 <=> v3_pre_topc(sK1,sK0)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.19/0.48  fof(f60,plain,(
% 0.19/0.48    spl2_3 <=> ! [X1,X3] : (~l1_pre_topc(X1) | k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.19/0.48  fof(f102,plain,(
% 0.19/0.48    sK1 = k1_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~spl2_3),
% 0.19/0.48    inference(resolution,[],[f61,f33])).
% 0.19/0.48  fof(f61,plain,(
% 0.19/0.48    ( ! [X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~l1_pre_topc(X1)) ) | ~spl2_3),
% 0.19/0.48    inference(avatar_component_clause,[],[f60])).
% 0.19/0.48  fof(f279,plain,(
% 0.19/0.48    spl2_8),
% 0.19/0.48    inference(avatar_contradiction_clause,[],[f278])).
% 0.19/0.48  fof(f278,plain,(
% 0.19/0.48    $false | spl2_8),
% 0.19/0.48    inference(resolution,[],[f268,f33])).
% 0.19/0.48  fof(f268,plain,(
% 0.19/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl2_8),
% 0.19/0.48    inference(avatar_component_clause,[],[f267])).
% 0.19/0.48  fof(f267,plain,(
% 0.19/0.48    spl2_8 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.19/0.48  fof(f277,plain,(
% 0.19/0.48    spl2_9),
% 0.19/0.48    inference(avatar_contradiction_clause,[],[f276])).
% 0.19/0.48  fof(f276,plain,(
% 0.19/0.48    $false | spl2_9),
% 0.19/0.48    inference(resolution,[],[f271,f34])).
% 0.19/0.48  fof(f34,plain,(
% 0.19/0.48    v2_pre_topc(sK0)),
% 0.19/0.48    inference(cnf_transformation,[],[f17])).
% 0.19/0.48  fof(f271,plain,(
% 0.19/0.48    ~v2_pre_topc(sK0) | spl2_9),
% 0.19/0.48    inference(avatar_component_clause,[],[f270])).
% 0.19/0.48  fof(f275,plain,(
% 0.19/0.48    spl2_7),
% 0.19/0.48    inference(avatar_contradiction_clause,[],[f274])).
% 0.19/0.48  fof(f274,plain,(
% 0.19/0.48    $false | spl2_7),
% 0.19/0.48    inference(resolution,[],[f265,f35])).
% 0.19/0.48  fof(f265,plain,(
% 0.19/0.48    ~l1_pre_topc(sK0) | spl2_7),
% 0.19/0.48    inference(avatar_component_clause,[],[f264])).
% 0.19/0.48  fof(f273,plain,(
% 0.19/0.48    ~spl2_9 | ~spl2_8 | ~spl2_7 | spl2_1 | ~spl2_2),
% 0.19/0.48    inference(avatar_split_clause,[],[f260,f53,f50,f264,f267,f270])).
% 0.19/0.48  fof(f260,plain,(
% 0.19/0.48    v3_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~spl2_2),
% 0.19/0.48    inference(superposition,[],[f45,f244])).
% 0.19/0.48  fof(f244,plain,(
% 0.19/0.48    sK1 = k1_tops_1(sK0,sK1) | ~spl2_2),
% 0.19/0.48    inference(backward_demodulation,[],[f116,f186])).
% 0.19/0.48  fof(f186,plain,(
% 0.19/0.48    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_2),
% 0.19/0.48    inference(backward_demodulation,[],[f137,f182])).
% 0.19/0.48  fof(f182,plain,(
% 0.19/0.48    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~spl2_2),
% 0.19/0.48    inference(superposition,[],[f147,f57])).
% 0.19/0.48  fof(f57,plain,(
% 0.19/0.48    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl2_2),
% 0.19/0.48    inference(avatar_component_clause,[],[f53])).
% 0.19/0.48  fof(f147,plain,(
% 0.19/0.48    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) = k4_xboole_0(k2_pre_topc(sK0,sK1),X0)) )),
% 0.19/0.48    inference(global_subsumption,[],[f35,f144])).
% 0.19/0.48  fof(f144,plain,(
% 0.19/0.48    ( ! [X0] : (~l1_pre_topc(sK0) | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) = k4_xboole_0(k2_pre_topc(sK0,sK1),X0)) )),
% 0.19/0.48    inference(resolution,[],[f101,f33])).
% 0.19/0.48  fof(f101,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),X2) = k4_xboole_0(k2_pre_topc(X1,X0),X2)) )),
% 0.19/0.48    inference(resolution,[],[f46,f48])).
% 0.19/0.48  fof(f48,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f30])).
% 0.19/0.48  fof(f30,plain,(
% 0.19/0.48    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.48    inference(ennf_transformation,[],[f5])).
% 0.19/0.48  fof(f5,axiom,(
% 0.19/0.48    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.19/0.48  fof(f46,plain,(
% 0.19/0.48    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f28])).
% 0.19/0.48  fof(f28,plain,(
% 0.19/0.48    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.19/0.48    inference(flattening,[],[f27])).
% 0.19/0.48  fof(f27,plain,(
% 0.19/0.48    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.19/0.48    inference(ennf_transformation,[],[f6])).
% 0.19/0.48  fof(f6,axiom,(
% 0.19/0.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.19/0.48  fof(f137,plain,(
% 0.19/0.48    sK1 = k4_xboole_0(sK1,k4_xboole_0(k2_pre_topc(sK0,sK1),sK1))),
% 0.19/0.48    inference(superposition,[],[f81,f133])).
% 0.19/0.48  fof(f133,plain,(
% 0.19/0.48    sK1 = k3_xboole_0(sK1,k2_pre_topc(sK0,sK1))),
% 0.19/0.48    inference(global_subsumption,[],[f35,f130])).
% 0.19/0.48  fof(f130,plain,(
% 0.19/0.48    ~l1_pre_topc(sK0) | sK1 = k3_xboole_0(sK1,k2_pre_topc(sK0,sK1))),
% 0.19/0.48    inference(resolution,[],[f82,f33])).
% 0.19/0.48  fof(f82,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | k3_xboole_0(X0,k2_pre_topc(X1,X0)) = X0) )),
% 0.19/0.48    inference(resolution,[],[f36,f44])).
% 0.19/0.48  fof(f44,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.19/0.48    inference(cnf_transformation,[],[f24])).
% 0.19/0.48  fof(f24,plain,(
% 0.19/0.48    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.19/0.48    inference(ennf_transformation,[],[f2])).
% 0.19/0.48  fof(f2,axiom,(
% 0.19/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.19/0.48  fof(f36,plain,(
% 0.19/0.48    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f18])).
% 0.19/0.48  fof(f18,plain,(
% 0.19/0.48    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.48    inference(ennf_transformation,[],[f7])).
% 0.19/0.48  fof(f7,axiom,(
% 0.19/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).
% 0.19/0.48  fof(f81,plain,(
% 0.19/0.48    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k4_xboole_0(k3_xboole_0(X2,X3),k4_xboole_0(X3,X2))) )),
% 0.19/0.48    inference(resolution,[],[f47,f73])).
% 0.19/0.48  fof(f73,plain,(
% 0.19/0.48    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X1,X0),k4_xboole_0(X0,X1))) )),
% 0.19/0.48    inference(superposition,[],[f43,f42])).
% 0.19/0.48  fof(f42,plain,(
% 0.19/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f1])).
% 0.19/0.48  fof(f1,axiom,(
% 0.19/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.19/0.48  fof(f43,plain,(
% 0.19/0.48    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))) )),
% 0.19/0.48    inference(cnf_transformation,[],[f4])).
% 0.19/0.48  fof(f4,axiom,(
% 0.19/0.48    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_xboole_1)).
% 0.19/0.48  fof(f47,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 0.19/0.48    inference(cnf_transformation,[],[f29])).
% 0.19/0.48  fof(f29,plain,(
% 0.19/0.48    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 0.19/0.48    inference(ennf_transformation,[],[f15])).
% 0.19/0.48  fof(f15,plain,(
% 0.19/0.48    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(X0,X1) = X0)),
% 0.19/0.48    inference(unused_predicate_definition_removal,[],[f3])).
% 0.19/0.48  fof(f3,axiom,(
% 0.19/0.48    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.19/0.48  fof(f116,plain,(
% 0.19/0.48    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 0.19/0.48    inference(global_subsumption,[],[f35,f115])).
% 0.19/0.48  fof(f115,plain,(
% 0.19/0.48    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 0.19/0.48    inference(forward_demodulation,[],[f112,f89])).
% 0.19/0.48  fof(f89,plain,(
% 0.19/0.48    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)) )),
% 0.19/0.48    inference(resolution,[],[f48,f33])).
% 0.19/0.48  fof(f112,plain,(
% 0.19/0.48    ~l1_pre_topc(sK0) | k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 0.19/0.48    inference(resolution,[],[f38,f33])).
% 0.19/0.48  fof(f38,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 0.19/0.48    inference(cnf_transformation,[],[f20])).
% 0.19/0.48  fof(f20,plain,(
% 0.19/0.48    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.48    inference(ennf_transformation,[],[f12])).
% 0.19/0.48  fof(f12,axiom,(
% 0.19/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 0.19/0.48  fof(f45,plain,(
% 0.19/0.48    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f26])).
% 0.19/0.48  fof(f26,plain,(
% 0.19/0.48    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.19/0.48    inference(flattening,[],[f25])).
% 0.19/0.48  fof(f25,plain,(
% 0.19/0.48    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.19/0.48    inference(ennf_transformation,[],[f8])).
% 0.19/0.48  fof(f8,axiom,(
% 0.19/0.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 0.19/0.48  fof(f65,plain,(
% 0.19/0.48    spl2_3 | spl2_4),
% 0.19/0.48    inference(avatar_split_clause,[],[f41,f63,f60])).
% 0.19/0.48  fof(f41,plain,(
% 0.19/0.48    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X3,X1) | k1_tops_1(X1,X3) = X3) )),
% 0.19/0.48    inference(cnf_transformation,[],[f23])).
% 0.19/0.48  fof(f23,plain,(
% 0.19/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.19/0.48    inference(flattening,[],[f22])).
% 0.19/0.48  fof(f22,plain,(
% 0.19/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.19/0.48    inference(ennf_transformation,[],[f10])).
% 0.19/0.48  fof(f10,axiom,(
% 0.19/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).
% 0.19/0.48  fof(f58,plain,(
% 0.19/0.48    spl2_1 | spl2_2),
% 0.19/0.48    inference(avatar_split_clause,[],[f31,f53,f50])).
% 0.19/0.48  fof(f31,plain,(
% 0.19/0.48    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 0.19/0.48    inference(cnf_transformation,[],[f17])).
% 0.19/0.48  fof(f55,plain,(
% 0.19/0.48    ~spl2_1 | ~spl2_2),
% 0.19/0.48    inference(avatar_split_clause,[],[f32,f53,f50])).
% 0.19/0.48  fof(f32,plain,(
% 0.19/0.48    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 0.19/0.48    inference(cnf_transformation,[],[f17])).
% 0.19/0.48  % SZS output end Proof for theBenchmark
% 0.19/0.48  % (32523)------------------------------
% 0.19/0.48  % (32523)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.48  % (32523)Termination reason: Refutation
% 0.19/0.48  
% 0.19/0.48  % (32523)Memory used [KB]: 10746
% 0.19/0.48  % (32523)Time elapsed: 0.076 s
% 0.19/0.48  % (32523)------------------------------
% 0.19/0.48  % (32523)------------------------------
% 0.19/0.48  % (32515)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.19/0.48  % (32510)Success in time 0.129 s
%------------------------------------------------------------------------------
