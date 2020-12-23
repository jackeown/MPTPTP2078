%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:59 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 148 expanded)
%              Number of leaves         :   27 (  51 expanded)
%              Depth                    :   12
%              Number of atoms          :  249 ( 355 expanded)
%              Number of equality atoms :   48 (  79 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f211,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f67,f70,f84,f86,f168,f170,f189,f191,f194,f210])).

fof(f210,plain,(
    spl1_8 ),
    inference(avatar_contradiction_clause,[],[f209])).

fof(f209,plain,
    ( $false
    | spl1_8 ),
    inference(resolution,[],[f208,f72])).

fof(f72,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(forward_demodulation,[],[f71,f43])).

fof(f43,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f71,plain,(
    ! [X0] : r1_tarski(k5_xboole_0(X0,k1_xboole_0),X0) ),
    inference(superposition,[],[f57,f42])).

fof(f42,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f57,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f51,f52])).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f208,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0))
    | spl1_8 ),
    inference(resolution,[],[f167,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f167,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl1_8 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl1_8
  <=> m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f194,plain,(
    spl1_6 ),
    inference(avatar_contradiction_clause,[],[f192])).

fof(f192,plain,
    ( $false
    | spl1_6 ),
    inference(resolution,[],[f159,f41])).

fof(f41,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f159,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl1_6 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl1_6
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f191,plain,(
    spl1_9 ),
    inference(avatar_contradiction_clause,[],[f190])).

fof(f190,plain,
    ( $false
    | spl1_9 ),
    inference(resolution,[],[f188,f35])).

fof(f35,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0))
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0] :
      ( k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).

fof(f188,plain,
    ( ~ v2_pre_topc(sK0)
    | spl1_9 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl1_9
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f189,plain,
    ( ~ spl1_7
    | ~ spl1_9
    | ~ spl1_3
    | spl1_5 ),
    inference(avatar_split_clause,[],[f184,f153,f78,f186,f161])).

fof(f161,plain,
    ( spl1_7
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f78,plain,
    ( spl1_3
  <=> ! [X0] :
        ( v4_pre_topc(k1_xboole_0,X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f153,plain,
    ( spl1_5
  <=> v4_pre_topc(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f184,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl1_3
    | spl1_5 ),
    inference(resolution,[],[f155,f79])).

fof(f79,plain,
    ( ! [X0] :
        ( v4_pre_topc(k1_xboole_0,X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f78])).

fof(f155,plain,
    ( ~ v4_pre_topc(k1_xboole_0,sK0)
    | spl1_5 ),
    inference(avatar_component_clause,[],[f153])).

fof(f170,plain,(
    spl1_7 ),
    inference(avatar_contradiction_clause,[],[f169])).

fof(f169,plain,
    ( $false
    | spl1_7 ),
    inference(resolution,[],[f163,f36])).

fof(f36,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f163,plain,
    ( ~ l1_pre_topc(sK0)
    | spl1_7 ),
    inference(avatar_component_clause,[],[f161])).

fof(f168,plain,
    ( ~ spl1_5
    | ~ spl1_6
    | ~ spl1_7
    | ~ spl1_8
    | spl1_2 ),
    inference(avatar_split_clause,[],[f151,f64,f165,f161,f157,f153])).

fof(f64,plain,
    ( spl1_2
  <=> u1_struct_0(sK0) = k1_tops_1(sK0,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f151,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(k1_xboole_0,sK0)
    | spl1_2 ),
    inference(trivial_inequality_removal,[],[f150])).

fof(f150,plain,
    ( u1_struct_0(sK0) != u1_struct_0(sK0)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(k1_xboole_0,sK0)
    | spl1_2 ),
    inference(superposition,[],[f66,f131])).

fof(f131,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k1_tops_1(X0,u1_struct_0(X0))
      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(k1_xboole_0,X0) ) ),
    inference(forward_demodulation,[],[f130,f56])).

fof(f56,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f40,f55])).

fof(f55,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f44,f39])).

fof(f39,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f44,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

fof(f40,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f130,plain,(
    ! [X0] :
      ( k1_tops_1(X0,u1_struct_0(X0)) = k3_subset_1(u1_struct_0(X0),k1_xboole_0)
      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(k1_xboole_0,X0) ) ),
    inference(duplicate_literal_removal,[],[f122])).

fof(f122,plain,(
    ! [X0] :
      ( k1_tops_1(X0,u1_struct_0(X0)) = k3_subset_1(u1_struct_0(X0),k1_xboole_0)
      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(k1_xboole_0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f96,f87])).

fof(f87,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_pre_topc(X0,k1_xboole_0)
      | ~ v4_pre_topc(k1_xboole_0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f48,f41])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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

fof(f96,plain,(
    ! [X5] :
      ( k1_tops_1(X5,u1_struct_0(X5)) = k3_subset_1(u1_struct_0(X5),k2_pre_topc(X5,k1_xboole_0))
      | ~ m1_subset_1(u1_struct_0(X5),k1_zfmisc_1(u1_struct_0(X5)))
      | ~ l1_pre_topc(X5)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X5))) ) ),
    inference(superposition,[],[f47,f73])).

fof(f73,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_subset_1(X0,X0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f53,f56])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

fof(f66,plain,
    ( u1_struct_0(sK0) != k1_tops_1(sK0,u1_struct_0(sK0))
    | spl1_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f86,plain,(
    spl1_4 ),
    inference(avatar_contradiction_clause,[],[f85])).

fof(f85,plain,
    ( $false
    | spl1_4 ),
    inference(resolution,[],[f83,f38])).

fof(f38,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f83,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl1_4 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl1_4
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f84,plain,
    ( spl1_3
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f75,f81,f78])).

fof(f75,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | v4_pre_topc(k1_xboole_0,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f50,f41])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(X1)
      | v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).

fof(f70,plain,(
    spl1_1 ),
    inference(avatar_contradiction_clause,[],[f69])).

fof(f69,plain,
    ( $false
    | spl1_1 ),
    inference(resolution,[],[f68,f36])).

fof(f68,plain,
    ( ~ l1_pre_topc(sK0)
    | spl1_1 ),
    inference(resolution,[],[f62,f46])).

fof(f46,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f62,plain,
    ( ~ l1_struct_0(sK0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl1_1
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f67,plain,
    ( ~ spl1_1
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f58,f64,f60])).

fof(f58,plain,
    ( u1_struct_0(sK0) != k1_tops_1(sK0,u1_struct_0(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(superposition,[],[f37,f45])).

fof(f45,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f37,plain,(
    k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:47:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.42  % (15309)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.43  % (15309)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.43  fof(f211,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(avatar_sat_refutation,[],[f67,f70,f84,f86,f168,f170,f189,f191,f194,f210])).
% 0.22/0.43  fof(f210,plain,(
% 0.22/0.43    spl1_8),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f209])).
% 0.22/0.43  fof(f209,plain,(
% 0.22/0.43    $false | spl1_8),
% 0.22/0.43    inference(resolution,[],[f208,f72])).
% 0.22/0.43  fof(f72,plain,(
% 0.22/0.43    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.22/0.43    inference(forward_demodulation,[],[f71,f43])).
% 0.22/0.43  fof(f43,plain,(
% 0.22/0.43    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.43    inference(cnf_transformation,[],[f5])).
% 0.22/0.43  fof(f5,axiom,(
% 0.22/0.43    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.22/0.43  fof(f71,plain,(
% 0.22/0.43    ( ! [X0] : (r1_tarski(k5_xboole_0(X0,k1_xboole_0),X0)) )),
% 0.22/0.43    inference(superposition,[],[f57,f42])).
% 0.22/0.43  fof(f42,plain,(
% 0.22/0.43    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f3])).
% 0.22/0.43  fof(f3,axiom,(
% 0.22/0.43    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.22/0.43  fof(f57,plain,(
% 0.22/0.43    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 0.22/0.43    inference(definition_unfolding,[],[f51,f52])).
% 0.22/0.43  fof(f52,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f2])).
% 0.22/0.43  fof(f2,axiom,(
% 0.22/0.43    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.43  fof(f51,plain,(
% 0.22/0.43    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f4])).
% 0.22/0.43  fof(f4,axiom,(
% 0.22/0.43    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.22/0.43  fof(f208,plain,(
% 0.22/0.43    ~r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) | spl1_8),
% 0.22/0.43    inference(resolution,[],[f167,f54])).
% 0.22/0.43  fof(f54,plain,(
% 0.22/0.43    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f32])).
% 0.22/0.43  fof(f32,plain,(
% 0.22/0.43    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f20])).
% 0.22/0.43  fof(f20,plain,(
% 0.22/0.43    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.22/0.43    inference(unused_predicate_definition_removal,[],[f11])).
% 0.22/0.43  fof(f11,axiom,(
% 0.22/0.43    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.43  fof(f167,plain,(
% 0.22/0.43    ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | spl1_8),
% 0.22/0.43    inference(avatar_component_clause,[],[f165])).
% 0.22/0.43  fof(f165,plain,(
% 0.22/0.43    spl1_8 <=> m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.22/0.43  fof(f194,plain,(
% 0.22/0.43    spl1_6),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f192])).
% 0.22/0.43  fof(f192,plain,(
% 0.22/0.43    $false | spl1_6),
% 0.22/0.43    inference(resolution,[],[f159,f41])).
% 0.22/0.43  fof(f41,plain,(
% 0.22/0.43    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f10])).
% 0.22/0.43  fof(f10,axiom,(
% 0.22/0.43    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.43  fof(f159,plain,(
% 0.22/0.43    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | spl1_6),
% 0.22/0.43    inference(avatar_component_clause,[],[f157])).
% 0.22/0.43  fof(f157,plain,(
% 0.22/0.43    spl1_6 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.22/0.43  fof(f191,plain,(
% 0.22/0.43    spl1_9),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f190])).
% 0.22/0.43  fof(f190,plain,(
% 0.22/0.43    $false | spl1_9),
% 0.22/0.43    inference(resolution,[],[f188,f35])).
% 0.22/0.43  fof(f35,plain,(
% 0.22/0.43    v2_pre_topc(sK0)),
% 0.22/0.43    inference(cnf_transformation,[],[f34])).
% 0.22/0.43  fof(f34,plain,(
% 0.22/0.43    k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f33])).
% 0.22/0.43  fof(f33,plain,(
% 0.22/0.43    ? [X0] : (k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f23,plain,(
% 0.22/0.43    ? [X0] : (k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.43    inference(flattening,[],[f22])).
% 0.22/0.43  fof(f22,plain,(
% 0.22/0.43    ? [X0] : (k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0)) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.22/0.43    inference(ennf_transformation,[],[f19])).
% 0.22/0.43  fof(f19,negated_conjecture,(
% 0.22/0.43    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)))),
% 0.22/0.43    inference(negated_conjecture,[],[f18])).
% 0.22/0.43  fof(f18,conjecture,(
% 0.22/0.43    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).
% 0.22/0.43  fof(f188,plain,(
% 0.22/0.43    ~v2_pre_topc(sK0) | spl1_9),
% 0.22/0.43    inference(avatar_component_clause,[],[f186])).
% 0.22/0.43  fof(f186,plain,(
% 0.22/0.43    spl1_9 <=> v2_pre_topc(sK0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.22/0.43  fof(f189,plain,(
% 0.22/0.43    ~spl1_7 | ~spl1_9 | ~spl1_3 | spl1_5),
% 0.22/0.43    inference(avatar_split_clause,[],[f184,f153,f78,f186,f161])).
% 0.22/0.43  fof(f161,plain,(
% 0.22/0.43    spl1_7 <=> l1_pre_topc(sK0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.22/0.43  fof(f78,plain,(
% 0.22/0.43    spl1_3 <=> ! [X0] : (v4_pre_topc(k1_xboole_0,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.22/0.43  fof(f153,plain,(
% 0.22/0.43    spl1_5 <=> v4_pre_topc(k1_xboole_0,sK0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.22/0.43  fof(f184,plain,(
% 0.22/0.43    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | (~spl1_3 | spl1_5)),
% 0.22/0.43    inference(resolution,[],[f155,f79])).
% 0.22/0.43  fof(f79,plain,(
% 0.22/0.43    ( ! [X0] : (v4_pre_topc(k1_xboole_0,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) ) | ~spl1_3),
% 0.22/0.43    inference(avatar_component_clause,[],[f78])).
% 0.22/0.43  fof(f155,plain,(
% 0.22/0.43    ~v4_pre_topc(k1_xboole_0,sK0) | spl1_5),
% 0.22/0.43    inference(avatar_component_clause,[],[f153])).
% 0.22/0.43  fof(f170,plain,(
% 0.22/0.43    spl1_7),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f169])).
% 0.22/0.43  fof(f169,plain,(
% 0.22/0.43    $false | spl1_7),
% 0.22/0.43    inference(resolution,[],[f163,f36])).
% 0.22/0.43  fof(f36,plain,(
% 0.22/0.43    l1_pre_topc(sK0)),
% 0.22/0.43    inference(cnf_transformation,[],[f34])).
% 0.22/0.43  fof(f163,plain,(
% 0.22/0.43    ~l1_pre_topc(sK0) | spl1_7),
% 0.22/0.43    inference(avatar_component_clause,[],[f161])).
% 0.22/0.43  fof(f168,plain,(
% 0.22/0.43    ~spl1_5 | ~spl1_6 | ~spl1_7 | ~spl1_8 | spl1_2),
% 0.22/0.43    inference(avatar_split_clause,[],[f151,f64,f165,f161,f157,f153])).
% 0.22/0.43  fof(f64,plain,(
% 0.22/0.43    spl1_2 <=> u1_struct_0(sK0) = k1_tops_1(sK0,u1_struct_0(sK0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.22/0.43  fof(f151,plain,(
% 0.22/0.43    ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(k1_xboole_0,sK0) | spl1_2),
% 0.22/0.43    inference(trivial_inequality_removal,[],[f150])).
% 0.22/0.43  fof(f150,plain,(
% 0.22/0.43    u1_struct_0(sK0) != u1_struct_0(sK0) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(k1_xboole_0,sK0) | spl1_2),
% 0.22/0.43    inference(superposition,[],[f66,f131])).
% 0.22/0.43  fof(f131,plain,(
% 0.22/0.43    ( ! [X0] : (u1_struct_0(X0) = k1_tops_1(X0,u1_struct_0(X0)) | ~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(k1_xboole_0,X0)) )),
% 0.22/0.43    inference(forward_demodulation,[],[f130,f56])).
% 0.22/0.43  fof(f56,plain,(
% 0.22/0.43    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 0.22/0.43    inference(definition_unfolding,[],[f40,f55])).
% 0.22/0.43  fof(f55,plain,(
% 0.22/0.43    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 0.22/0.43    inference(definition_unfolding,[],[f44,f39])).
% 0.22/0.43  fof(f39,plain,(
% 0.22/0.43    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f6])).
% 0.22/0.43  fof(f6,axiom,(
% 0.22/0.43    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 0.22/0.43  fof(f44,plain,(
% 0.22/0.43    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f9])).
% 0.22/0.43  fof(f9,axiom,(
% 0.22/0.43    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).
% 0.22/0.43  fof(f40,plain,(
% 0.22/0.43    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.22/0.43    inference(cnf_transformation,[],[f7])).
% 0.22/0.43  fof(f7,axiom,(
% 0.22/0.43    ! [X0] : k2_subset_1(X0) = X0),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.22/0.43  fof(f130,plain,(
% 0.22/0.43    ( ! [X0] : (k1_tops_1(X0,u1_struct_0(X0)) = k3_subset_1(u1_struct_0(X0),k1_xboole_0) | ~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(k1_xboole_0,X0)) )),
% 0.22/0.43    inference(duplicate_literal_removal,[],[f122])).
% 0.22/0.43  fof(f122,plain,(
% 0.22/0.43    ( ! [X0] : (k1_tops_1(X0,u1_struct_0(X0)) = k3_subset_1(u1_struct_0(X0),k1_xboole_0) | ~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(k1_xboole_0,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.43    inference(superposition,[],[f96,f87])).
% 0.22/0.43  fof(f87,plain,(
% 0.22/0.43    ( ! [X0] : (k1_xboole_0 = k2_pre_topc(X0,k1_xboole_0) | ~v4_pre_topc(k1_xboole_0,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.43    inference(resolution,[],[f48,f41])).
% 0.22/0.43  fof(f48,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~l1_pre_topc(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f28])).
% 0.22/0.43  fof(f28,plain,(
% 0.22/0.43    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.43    inference(flattening,[],[f27])).
% 0.22/0.43  fof(f27,plain,(
% 0.22/0.43    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.43    inference(ennf_transformation,[],[f16])).
% 0.22/0.43  fof(f16,axiom,(
% 0.22/0.43    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.22/0.43  fof(f96,plain,(
% 0.22/0.43    ( ! [X5] : (k1_tops_1(X5,u1_struct_0(X5)) = k3_subset_1(u1_struct_0(X5),k2_pre_topc(X5,k1_xboole_0)) | ~m1_subset_1(u1_struct_0(X5),k1_zfmisc_1(u1_struct_0(X5))) | ~l1_pre_topc(X5) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X5)))) )),
% 0.22/0.43    inference(superposition,[],[f47,f73])).
% 0.22/0.43  fof(f73,plain,(
% 0.22/0.43    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.43    inference(superposition,[],[f53,f56])).
% 0.22/0.43  fof(f53,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f31])).
% 0.22/0.43  fof(f31,plain,(
% 0.22/0.43    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.43    inference(ennf_transformation,[],[f8])).
% 0.22/0.43  fof(f8,axiom,(
% 0.22/0.43    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.22/0.43  fof(f47,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f26])).
% 0.22/0.43  fof(f26,plain,(
% 0.22/0.43    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.43    inference(ennf_transformation,[],[f17])).
% 0.22/0.43  fof(f17,axiom,(
% 0.22/0.43    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).
% 0.22/0.43  fof(f66,plain,(
% 0.22/0.43    u1_struct_0(sK0) != k1_tops_1(sK0,u1_struct_0(sK0)) | spl1_2),
% 0.22/0.43    inference(avatar_component_clause,[],[f64])).
% 0.22/0.43  fof(f86,plain,(
% 0.22/0.43    spl1_4),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f85])).
% 0.22/0.43  fof(f85,plain,(
% 0.22/0.43    $false | spl1_4),
% 0.22/0.43    inference(resolution,[],[f83,f38])).
% 0.22/0.43  fof(f38,plain,(
% 0.22/0.43    v1_xboole_0(k1_xboole_0)),
% 0.22/0.43    inference(cnf_transformation,[],[f1])).
% 0.22/0.43  fof(f1,axiom,(
% 0.22/0.43    v1_xboole_0(k1_xboole_0)),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.43  fof(f83,plain,(
% 0.22/0.43    ~v1_xboole_0(k1_xboole_0) | spl1_4),
% 0.22/0.43    inference(avatar_component_clause,[],[f81])).
% 0.22/0.43  fof(f81,plain,(
% 0.22/0.43    spl1_4 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.22/0.43  fof(f84,plain,(
% 0.22/0.43    spl1_3 | ~spl1_4),
% 0.22/0.43    inference(avatar_split_clause,[],[f75,f81,f78])).
% 0.22/0.43  fof(f75,plain,(
% 0.22/0.43    ( ! [X0] : (~v1_xboole_0(k1_xboole_0) | v4_pre_topc(k1_xboole_0,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.43    inference(resolution,[],[f50,f41])).
% 0.22/0.43  fof(f50,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1) | v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f30])).
% 0.22/0.43  fof(f30,plain,(
% 0.22/0.43    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.43    inference(flattening,[],[f29])).
% 0.22/0.43  fof(f29,plain,(
% 0.22/0.43    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.43    inference(ennf_transformation,[],[f13])).
% 0.22/0.43  fof(f13,axiom,(
% 0.22/0.43    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v4_pre_topc(X1,X0))))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).
% 0.22/0.43  fof(f70,plain,(
% 0.22/0.43    spl1_1),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f69])).
% 0.22/0.43  fof(f69,plain,(
% 0.22/0.43    $false | spl1_1),
% 0.22/0.43    inference(resolution,[],[f68,f36])).
% 0.22/0.43  fof(f68,plain,(
% 0.22/0.43    ~l1_pre_topc(sK0) | spl1_1),
% 0.22/0.43    inference(resolution,[],[f62,f46])).
% 0.22/0.43  fof(f46,plain,(
% 0.22/0.43    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f25])).
% 0.22/0.43  fof(f25,plain,(
% 0.22/0.43    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.43    inference(ennf_transformation,[],[f15])).
% 0.22/0.43  fof(f15,axiom,(
% 0.22/0.43    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.43  fof(f62,plain,(
% 0.22/0.43    ~l1_struct_0(sK0) | spl1_1),
% 0.22/0.43    inference(avatar_component_clause,[],[f60])).
% 0.22/0.43  fof(f60,plain,(
% 0.22/0.43    spl1_1 <=> l1_struct_0(sK0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.22/0.43  fof(f67,plain,(
% 0.22/0.43    ~spl1_1 | ~spl1_2),
% 0.22/0.43    inference(avatar_split_clause,[],[f58,f64,f60])).
% 0.22/0.43  fof(f58,plain,(
% 0.22/0.43    u1_struct_0(sK0) != k1_tops_1(sK0,u1_struct_0(sK0)) | ~l1_struct_0(sK0)),
% 0.22/0.43    inference(superposition,[],[f37,f45])).
% 0.22/0.43  fof(f45,plain,(
% 0.22/0.43    ( ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f24])).
% 0.22/0.43  fof(f24,plain,(
% 0.22/0.43    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.43    inference(ennf_transformation,[],[f14])).
% 0.22/0.43  fof(f14,axiom,(
% 0.22/0.43    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.43  fof(f37,plain,(
% 0.22/0.43    k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0))),
% 0.22/0.43    inference(cnf_transformation,[],[f34])).
% 0.22/0.43  % SZS output end Proof for theBenchmark
% 0.22/0.43  % (15309)------------------------------
% 0.22/0.43  % (15309)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (15309)Termination reason: Refutation
% 0.22/0.43  
% 0.22/0.43  % (15309)Memory used [KB]: 6140
% 0.22/0.43  % (15309)Time elapsed: 0.011 s
% 0.22/0.43  % (15309)------------------------------
% 0.22/0.43  % (15309)------------------------------
% 0.22/0.43  % (15302)Success in time 0.068 s
%------------------------------------------------------------------------------
