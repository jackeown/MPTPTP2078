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
% DateTime   : Thu Dec  3 13:12:23 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 303 expanded)
%              Number of leaves         :   34 ( 130 expanded)
%              Depth                    :   12
%              Number of atoms          :  439 ( 873 expanded)
%              Number of equality atoms :   84 ( 208 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3341,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f80,f85,f90,f98,f106,f129,f157,f392,f422,f488,f494,f776,f3308,f3311,f3312,f3319,f3324,f3340])).

fof(f3340,plain,
    ( ~ spl2_4
    | spl2_29
    | ~ spl2_31
    | ~ spl2_6
    | ~ spl2_209 ),
    inference(avatar_split_clause,[],[f3339,f3288,f102,f341,f331,f87])).

fof(f87,plain,
    ( spl2_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f331,plain,
    ( spl2_29
  <=> v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f341,plain,
    ( spl2_31
  <=> m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).

fof(f102,plain,
    ( spl2_6
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f3288,plain,
    ( spl2_209
  <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_209])])).

fof(f3339,plain,
    ( ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_6
    | ~ spl2_209 ),
    inference(forward_demodulation,[],[f3335,f104])).

fof(f104,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f102])).

fof(f3335,plain,
    ( v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_209 ),
    inference(trivial_inequality_removal,[],[f3334])).

fof(f3334,plain,
    ( k2_struct_0(sK0) != k2_struct_0(sK0)
    | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_209 ),
    inference(superposition,[],[f52,f3290])).

fof(f3290,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))
    | ~ spl2_209 ),
    inference(avatar_component_clause,[],[f3288])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X0) != k2_pre_topc(X0,X1)
      | v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

fof(f3324,plain,
    ( ~ spl2_29
    | spl2_1
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_9
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f3323,f153,f126,f102,f87,f72,f331])).

fof(f72,plain,
    ( spl2_1
  <=> v2_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f126,plain,
    ( spl2_9
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f153,plain,
    ( spl2_11
  <=> k4_xboole_0(k2_struct_0(sK0),sK1) = k3_subset_1(k2_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f3323,plain,
    ( ~ v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | spl2_1
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_9
    | ~ spl2_11 ),
    inference(forward_demodulation,[],[f3322,f155])).

fof(f155,plain,
    ( k4_xboole_0(k2_struct_0(sK0),sK1) = k3_subset_1(k2_struct_0(sK0),sK1)
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f153])).

fof(f3322,plain,
    ( ~ v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | spl2_1
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_9 ),
    inference(unit_resulting_resolution,[],[f128,f74,f248])).

fof(f248,plain,
    ( ! [X0] :
        ( ~ v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | v2_tops_1(X0,sK0) )
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f247,f104])).

fof(f247,plain,
    ( ! [X0] :
        ( ~ v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tops_1(X0,sK0) )
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f246,f104])).

fof(f246,plain,
    ( ! [X0] :
        ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tops_1(X0,sK0) )
    | ~ spl2_4 ),
    inference(resolution,[],[f54,f89])).

fof(f89,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_1)).

fof(f74,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f128,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f126])).

fof(f3319,plain,
    ( spl2_209
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_43 ),
    inference(avatar_split_clause,[],[f3286,f468,f102,f87,f3288])).

fof(f468,plain,
    ( spl2_43
  <=> k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).

fof(f3286,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_43 ),
    inference(forward_demodulation,[],[f3269,f67])).

fof(f67,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f45,f65])).

fof(f65,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f47,f44])).

fof(f44,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f47,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

fof(f45,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f3269,plain,
    ( k3_subset_1(k2_struct_0(sK0),k1_xboole_0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_43 ),
    inference(superposition,[],[f832,f470])).

fof(f470,plain,
    ( k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)))
    | ~ spl2_43 ),
    inference(avatar_component_clause,[],[f468])).

fof(f832,plain,
    ( ! [X0] : k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),X0)) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),X0))))
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(unit_resulting_resolution,[],[f313,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f313,plain,
    ( ! [X0] : m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),X0)),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(unit_resulting_resolution,[],[f115,f231])).

fof(f231,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f230,f104])).

fof(f230,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f229,f104])).

fof(f229,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_4 ),
    inference(resolution,[],[f62,f89])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f115,plain,(
    ! [X0,X1] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f55,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f55,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f3312,plain,
    ( k2_struct_0(sK0) != k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))
    | k1_tops_1(sK0,sK1) != k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)))
    | k1_xboole_0 != k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0))
    | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f3311,plain,
    ( ~ spl2_4
    | spl2_209
    | ~ spl2_31
    | ~ spl2_6
    | ~ spl2_29 ),
    inference(avatar_split_clause,[],[f3310,f331,f102,f341,f3288,f87])).

fof(f3310,plain,
    ( ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_6
    | ~ spl2_29 ),
    inference(forward_demodulation,[],[f3309,f104])).

fof(f3309,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))
    | ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_29 ),
    inference(resolution,[],[f332,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_tops_1(X1,X0)
      | k2_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f332,plain,
    ( v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ spl2_29 ),
    inference(avatar_component_clause,[],[f331])).

fof(f3308,plain,
    ( ~ spl2_4
    | spl2_29
    | ~ spl2_9
    | ~ spl2_1
    | ~ spl2_6
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f3307,f153,f102,f72,f126,f331,f87])).

fof(f3307,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_1
    | ~ spl2_6
    | ~ spl2_11 ),
    inference(forward_demodulation,[],[f3306,f104])).

fof(f3306,plain,
    ( v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_1
    | ~ spl2_6
    | ~ spl2_11 ),
    inference(forward_demodulation,[],[f3305,f155])).

fof(f3305,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_1
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f3304,f104])).

fof(f3304,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(resolution,[],[f73,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v2_tops_1(X1,X0)
      | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f73,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f776,plain,(
    spl2_31 ),
    inference(avatar_contradiction_clause,[],[f771])).

fof(f771,plain,
    ( $false
    | spl2_31 ),
    inference(unit_resulting_resolution,[],[f55,f343,f64])).

fof(f343,plain,
    ( ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl2_31 ),
    inference(avatar_component_clause,[],[f341])).

fof(f494,plain,
    ( spl2_46
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_9
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f465,f153,f126,f102,f87,f490])).

fof(f490,plain,
    ( spl2_46
  <=> k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).

fof(f465,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)))
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_9
    | ~ spl2_11 ),
    inference(forward_demodulation,[],[f459,f155])).

fof(f459,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_9 ),
    inference(unit_resulting_resolution,[],[f128,f251])).

fof(f251,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | k1_tops_1(sK0,X0) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) )
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f250,f104])).

fof(f250,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) )
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f249,f104])).

fof(f249,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) )
    | ~ spl2_4 ),
    inference(resolution,[],[f50,f89])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

fof(f488,plain,
    ( spl2_43
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_9
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f487,f153,f126,f102,f87,f76,f468])).

fof(f76,plain,
    ( spl2_2
  <=> k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f487,plain,
    ( k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)))
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_9
    | ~ spl2_11 ),
    inference(forward_demodulation,[],[f486,f77])).

fof(f77,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f486,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)))
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_9
    | ~ spl2_11 ),
    inference(forward_demodulation,[],[f464,f155])).

fof(f464,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_9 ),
    inference(resolution,[],[f251,f128])).

fof(f422,plain,
    ( spl2_39
    | ~ spl2_34 ),
    inference(avatar_split_clause,[],[f421,f354,f410])).

fof(f410,plain,
    ( spl2_39
  <=> k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).

fof(f354,plain,
    ( spl2_34
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f421,plain,
    ( k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ spl2_34 ),
    inference(forward_demodulation,[],[f399,f67])).

fof(f399,plain,
    ( k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k1_xboole_0))
    | ~ spl2_34 ),
    inference(resolution,[],[f355,f61])).

fof(f355,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl2_34 ),
    inference(avatar_component_clause,[],[f354])).

fof(f392,plain,(
    spl2_34 ),
    inference(avatar_contradiction_clause,[],[f390])).

fof(f390,plain,
    ( $false
    | spl2_34 ),
    inference(unit_resulting_resolution,[],[f135,f356,f64])).

fof(f356,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_struct_0(sK0)))
    | spl2_34 ),
    inference(avatar_component_clause,[],[f354])).

fof(f135,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(superposition,[],[f55,f68])).

fof(f68,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f46,f58])).

fof(f58,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f157,plain,
    ( spl2_11
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f151,f126,f153])).

fof(f151,plain,
    ( k4_xboole_0(k2_struct_0(sK0),sK1) = k3_subset_1(k2_struct_0(sK0),sK1)
    | ~ spl2_9 ),
    inference(resolution,[],[f60,f128])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f129,plain,
    ( spl2_9
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f119,f102,f82,f126])).

fof(f82,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f119,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(backward_demodulation,[],[f84,f104])).

fof(f84,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f82])).

fof(f106,plain,
    ( spl2_6
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f100,f94,f102])).

fof(f94,plain,
    ( spl2_5
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f100,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl2_5 ),
    inference(resolution,[],[f48,f96])).

fof(f96,plain,
    ( l1_struct_0(sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f94])).

fof(f48,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f98,plain,
    ( spl2_5
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f92,f87,f94])).

fof(f92,plain,
    ( l1_struct_0(sK0)
    | ~ spl2_4 ),
    inference(resolution,[],[f49,f89])).

fof(f49,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f90,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f40,f87])).

fof(f40,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ( k1_xboole_0 != k1_tops_1(sK0,sK1)
      | ~ v2_tops_1(sK1,sK0) )
    & ( k1_xboole_0 = k1_tops_1(sK0,sK1)
      | v2_tops_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f33,f35,f34])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k1_xboole_0 != k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | v2_tops_1(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(sK0,X1)
            | ~ v2_tops_1(X1,sK0) )
          & ( k1_xboole_0 = k1_tops_1(sK0,X1)
            | v2_tops_1(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X1] :
        ( ( k1_xboole_0 != k1_tops_1(sK0,X1)
          | ~ v2_tops_1(X1,sK0) )
        & ( k1_xboole_0 = k1_tops_1(sK0,X1)
          | v2_tops_1(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k1_xboole_0 != k1_tops_1(sK0,sK1)
        | ~ v2_tops_1(sK1,sK0) )
      & ( k1_xboole_0 = k1_tops_1(sK0,sK1)
        | v2_tops_1(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(X0,X1)
            | ~ v2_tops_1(X1,X0) )
          & ( k1_xboole_0 = k1_tops_1(X0,X1)
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(X0,X1)
            | ~ v2_tops_1(X1,X0) )
          & ( k1_xboole_0 = k1_tops_1(X0,X1)
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> k1_xboole_0 = k1_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

fof(f85,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f41,f82])).

fof(f41,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f80,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f42,f76,f72])).

fof(f42,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f79,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f43,f76,f72])).

fof(f43,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:25:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.41  % (22138)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.45  % (22134)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.45  % (22135)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.45  % (22140)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.46  % (22144)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.46  % (22142)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.46  % (22132)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.46  % (22143)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.46  % (22136)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.49  % (22148)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.49  % (22129)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.49  % (22147)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.49  % (22146)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.49  % (22141)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.50  % (22133)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.50  % (22137)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.50  % (22139)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.51  % (22130)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.53  % (22136)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f3341,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(avatar_sat_refutation,[],[f79,f80,f85,f90,f98,f106,f129,f157,f392,f422,f488,f494,f776,f3308,f3311,f3312,f3319,f3324,f3340])).
% 0.20/0.53  fof(f3340,plain,(
% 0.20/0.53    ~spl2_4 | spl2_29 | ~spl2_31 | ~spl2_6 | ~spl2_209),
% 0.20/0.53    inference(avatar_split_clause,[],[f3339,f3288,f102,f341,f331,f87])).
% 0.20/0.53  fof(f87,plain,(
% 0.20/0.53    spl2_4 <=> l1_pre_topc(sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.53  fof(f331,plain,(
% 0.20/0.53    spl2_29 <=> v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 0.20/0.53  fof(f341,plain,(
% 0.20/0.53    spl2_31 <=> m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).
% 0.20/0.53  fof(f102,plain,(
% 0.20/0.53    spl2_6 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.53  fof(f3288,plain,(
% 0.20/0.53    spl2_209 <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_209])])).
% 0.20/0.53  fof(f3339,plain,(
% 0.20/0.53    ~m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) | ~l1_pre_topc(sK0) | (~spl2_6 | ~spl2_209)),
% 0.20/0.53    inference(forward_demodulation,[],[f3335,f104])).
% 0.20/0.53  fof(f104,plain,(
% 0.20/0.53    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl2_6),
% 0.20/0.53    inference(avatar_component_clause,[],[f102])).
% 0.20/0.53  fof(f3335,plain,(
% 0.20/0.53    v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_209),
% 0.20/0.53    inference(trivial_inequality_removal,[],[f3334])).
% 0.20/0.53  fof(f3334,plain,(
% 0.20/0.53    k2_struct_0(sK0) != k2_struct_0(sK0) | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_209),
% 0.20/0.53    inference(superposition,[],[f52,f3290])).
% 0.20/0.53  fof(f3290,plain,(
% 0.20/0.53    k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) | ~spl2_209),
% 0.20/0.53    inference(avatar_component_clause,[],[f3288])).
% 0.20/0.53  fof(f52,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k2_struct_0(X0) != k2_pre_topc(X0,X1) | v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f37])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(nnf_transformation,[],[f25])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f17])).
% 0.20/0.53  fof(f17,axiom,(
% 0.20/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).
% 0.20/0.53  fof(f3324,plain,(
% 0.20/0.53    ~spl2_29 | spl2_1 | ~spl2_4 | ~spl2_6 | ~spl2_9 | ~spl2_11),
% 0.20/0.53    inference(avatar_split_clause,[],[f3323,f153,f126,f102,f87,f72,f331])).
% 0.20/0.53  fof(f72,plain,(
% 0.20/0.53    spl2_1 <=> v2_tops_1(sK1,sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.53  fof(f126,plain,(
% 0.20/0.53    spl2_9 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.20/0.53  fof(f153,plain,(
% 0.20/0.53    spl2_11 <=> k4_xboole_0(k2_struct_0(sK0),sK1) = k3_subset_1(k2_struct_0(sK0),sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.20/0.53  fof(f3323,plain,(
% 0.20/0.53    ~v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) | (spl2_1 | ~spl2_4 | ~spl2_6 | ~spl2_9 | ~spl2_11)),
% 0.20/0.53    inference(forward_demodulation,[],[f3322,f155])).
% 0.20/0.53  fof(f155,plain,(
% 0.20/0.53    k4_xboole_0(k2_struct_0(sK0),sK1) = k3_subset_1(k2_struct_0(sK0),sK1) | ~spl2_11),
% 0.20/0.53    inference(avatar_component_clause,[],[f153])).
% 0.20/0.53  fof(f3322,plain,(
% 0.20/0.53    ~v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | (spl2_1 | ~spl2_4 | ~spl2_6 | ~spl2_9)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f128,f74,f248])).
% 0.20/0.53  fof(f248,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v2_tops_1(X0,sK0)) ) | (~spl2_4 | ~spl2_6)),
% 0.20/0.53    inference(forward_demodulation,[],[f247,f104])).
% 0.20/0.53  fof(f247,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_1(X0,sK0)) ) | (~spl2_4 | ~spl2_6)),
% 0.20/0.53    inference(forward_demodulation,[],[f246,f104])).
% 0.20/0.53  fof(f246,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_1(X0,sK0)) ) | ~spl2_4),
% 0.20/0.53    inference(resolution,[],[f54,f89])).
% 0.20/0.53  fof(f89,plain,(
% 0.20/0.53    l1_pre_topc(sK0) | ~spl2_4),
% 0.20/0.53    inference(avatar_component_clause,[],[f87])).
% 0.20/0.53  fof(f54,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tops_1(X1,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f38])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(nnf_transformation,[],[f26])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f18])).
% 0.20/0.53  fof(f18,axiom,(
% 0.20/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_1)).
% 0.20/0.53  fof(f74,plain,(
% 0.20/0.53    ~v2_tops_1(sK1,sK0) | spl2_1),
% 0.20/0.53    inference(avatar_component_clause,[],[f72])).
% 0.20/0.53  fof(f128,plain,(
% 0.20/0.53    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~spl2_9),
% 0.20/0.53    inference(avatar_component_clause,[],[f126])).
% 0.20/0.53  fof(f3319,plain,(
% 0.20/0.53    spl2_209 | ~spl2_4 | ~spl2_6 | ~spl2_43),
% 0.20/0.53    inference(avatar_split_clause,[],[f3286,f468,f102,f87,f3288])).
% 0.20/0.53  fof(f468,plain,(
% 0.20/0.53    spl2_43 <=> k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_43])])).
% 0.20/0.53  fof(f3286,plain,(
% 0.20/0.53    k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) | (~spl2_4 | ~spl2_6 | ~spl2_43)),
% 0.20/0.53    inference(forward_demodulation,[],[f3269,f67])).
% 0.20/0.53  fof(f67,plain,(
% 0.20/0.53    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 0.20/0.53    inference(definition_unfolding,[],[f45,f65])).
% 0.20/0.53  fof(f65,plain,(
% 0.20/0.53    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 0.20/0.53    inference(definition_unfolding,[],[f47,f44])).
% 0.20/0.53  fof(f44,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f7])).
% 0.20/0.53  fof(f7,axiom,(
% 0.20/0.53    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 0.20/0.53  fof(f47,plain,(
% 0.20/0.53    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f11])).
% 0.20/0.53  fof(f11,axiom,(
% 0.20/0.53    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).
% 0.20/0.53  fof(f45,plain,(
% 0.20/0.53    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f8])).
% 0.20/0.53  fof(f8,axiom,(
% 0.20/0.53    ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.20/0.53  fof(f3269,plain,(
% 0.20/0.53    k3_subset_1(k2_struct_0(sK0),k1_xboole_0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) | (~spl2_4 | ~spl2_6 | ~spl2_43)),
% 0.20/0.53    inference(superposition,[],[f832,f470])).
% 0.20/0.53  fof(f470,plain,(
% 0.20/0.53    k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) | ~spl2_43),
% 0.20/0.53    inference(avatar_component_clause,[],[f468])).
% 0.20/0.53  fof(f832,plain,(
% 0.20/0.53    ( ! [X0] : (k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),X0)) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),X0))))) ) | (~spl2_4 | ~spl2_6)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f313,f61])).
% 0.20/0.53  fof(f61,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,axiom,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.20/0.53  fof(f313,plain,(
% 0.20/0.53    ( ! [X0] : (m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),X0)),k1_zfmisc_1(k2_struct_0(sK0)))) ) | (~spl2_4 | ~spl2_6)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f115,f231])).
% 0.20/0.53  fof(f231,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0)))) ) | (~spl2_4 | ~spl2_6)),
% 0.20/0.53    inference(forward_demodulation,[],[f230,f104])).
% 0.20/0.53  fof(f230,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl2_4 | ~spl2_6)),
% 0.20/0.53    inference(forward_demodulation,[],[f229,f104])).
% 0.20/0.53  fof(f229,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl2_4),
% 0.20/0.53    inference(resolution,[],[f62,f89])).
% 0.20/0.53  fof(f62,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f31])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(flattening,[],[f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f14])).
% 0.20/0.53  fof(f14,axiom,(
% 0.20/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.20/0.53  fof(f115,plain,(
% 0.20/0.53    ( ! [X0,X1] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))) )),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f55,f64])).
% 0.20/0.53  fof(f64,plain,(
% 0.20/0.53    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f39])).
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.53    inference(nnf_transformation,[],[f12])).
% 0.20/0.53  fof(f12,axiom,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.53  fof(f55,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.20/0.53  fof(f3312,plain,(
% 0.20/0.53    k2_struct_0(sK0) != k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) | k1_tops_1(sK0,sK1) != k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) | k1_xboole_0 != k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) | k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 0.20/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.53  fof(f3311,plain,(
% 0.20/0.53    ~spl2_4 | spl2_209 | ~spl2_31 | ~spl2_6 | ~spl2_29),
% 0.20/0.53    inference(avatar_split_clause,[],[f3310,f331,f102,f341,f3288,f87])).
% 0.20/0.53  fof(f3310,plain,(
% 0.20/0.53    ~m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) | ~l1_pre_topc(sK0) | (~spl2_6 | ~spl2_29)),
% 0.20/0.53    inference(forward_demodulation,[],[f3309,f104])).
% 0.20/0.53  fof(f3309,plain,(
% 0.20/0.53    k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) | ~m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_29),
% 0.20/0.53    inference(resolution,[],[f332,f51])).
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v1_tops_1(X1,X0) | k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f37])).
% 0.20/0.53  fof(f332,plain,(
% 0.20/0.53    v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) | ~spl2_29),
% 0.20/0.53    inference(avatar_component_clause,[],[f331])).
% 0.20/0.53  fof(f3308,plain,(
% 0.20/0.53    ~spl2_4 | spl2_29 | ~spl2_9 | ~spl2_1 | ~spl2_6 | ~spl2_11),
% 0.20/0.53    inference(avatar_split_clause,[],[f3307,f153,f102,f72,f126,f331,f87])).
% 0.20/0.53  fof(f3307,plain,(
% 0.20/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) | ~l1_pre_topc(sK0) | (~spl2_1 | ~spl2_6 | ~spl2_11)),
% 0.20/0.53    inference(forward_demodulation,[],[f3306,f104])).
% 0.20/0.53  fof(f3306,plain,(
% 0.20/0.53    v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl2_1 | ~spl2_6 | ~spl2_11)),
% 0.20/0.53    inference(forward_demodulation,[],[f3305,f155])).
% 0.20/0.53  fof(f3305,plain,(
% 0.20/0.53    v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl2_1 | ~spl2_6)),
% 0.20/0.53    inference(forward_demodulation,[],[f3304,f104])).
% 0.20/0.53  fof(f3304,plain,(
% 0.20/0.53    v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_1),
% 0.20/0.53    inference(resolution,[],[f73,f53])).
% 0.20/0.53  fof(f53,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v2_tops_1(X1,X0) | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f38])).
% 0.20/0.53  fof(f73,plain,(
% 0.20/0.53    v2_tops_1(sK1,sK0) | ~spl2_1),
% 0.20/0.53    inference(avatar_component_clause,[],[f72])).
% 0.20/0.53  fof(f776,plain,(
% 0.20/0.53    spl2_31),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f771])).
% 0.20/0.53  fof(f771,plain,(
% 0.20/0.53    $false | spl2_31),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f55,f343,f64])).
% 0.20/0.53  fof(f343,plain,(
% 0.20/0.53    ~m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | spl2_31),
% 0.20/0.53    inference(avatar_component_clause,[],[f341])).
% 0.20/0.53  fof(f494,plain,(
% 0.20/0.53    spl2_46 | ~spl2_4 | ~spl2_6 | ~spl2_9 | ~spl2_11),
% 0.20/0.53    inference(avatar_split_clause,[],[f465,f153,f126,f102,f87,f490])).
% 0.20/0.53  fof(f490,plain,(
% 0.20/0.53    spl2_46 <=> k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).
% 0.20/0.53  fof(f465,plain,(
% 0.20/0.53    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) | (~spl2_4 | ~spl2_6 | ~spl2_9 | ~spl2_11)),
% 0.20/0.53    inference(forward_demodulation,[],[f459,f155])).
% 0.20/0.53  fof(f459,plain,(
% 0.20/0.53    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) | (~spl2_4 | ~spl2_6 | ~spl2_9)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f128,f251])).
% 0.20/0.53  fof(f251,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k1_tops_1(sK0,X0) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0)))) ) | (~spl2_4 | ~spl2_6)),
% 0.20/0.53    inference(forward_demodulation,[],[f250,f104])).
% 0.20/0.53  fof(f250,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)))) ) | (~spl2_4 | ~spl2_6)),
% 0.20/0.53    inference(forward_demodulation,[],[f249,f104])).
% 0.20/0.53  fof(f249,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)))) ) | ~spl2_4),
% 0.20/0.53    inference(resolution,[],[f50,f89])).
% 0.20/0.53  fof(f50,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f16])).
% 0.20/0.53  fof(f16,axiom,(
% 0.20/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).
% 0.20/0.53  fof(f488,plain,(
% 0.20/0.53    spl2_43 | ~spl2_2 | ~spl2_4 | ~spl2_6 | ~spl2_9 | ~spl2_11),
% 0.20/0.53    inference(avatar_split_clause,[],[f487,f153,f126,f102,f87,f76,f468])).
% 0.20/0.53  fof(f76,plain,(
% 0.20/0.53    spl2_2 <=> k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.53  fof(f487,plain,(
% 0.20/0.53    k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) | (~spl2_2 | ~spl2_4 | ~spl2_6 | ~spl2_9 | ~spl2_11)),
% 0.20/0.53    inference(forward_demodulation,[],[f486,f77])).
% 0.20/0.53  fof(f77,plain,(
% 0.20/0.53    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~spl2_2),
% 0.20/0.53    inference(avatar_component_clause,[],[f76])).
% 0.20/0.53  fof(f486,plain,(
% 0.20/0.53    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) | (~spl2_4 | ~spl2_6 | ~spl2_9 | ~spl2_11)),
% 0.20/0.53    inference(forward_demodulation,[],[f464,f155])).
% 0.20/0.53  fof(f464,plain,(
% 0.20/0.53    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) | (~spl2_4 | ~spl2_6 | ~spl2_9)),
% 0.20/0.53    inference(resolution,[],[f251,f128])).
% 0.20/0.53  fof(f422,plain,(
% 0.20/0.53    spl2_39 | ~spl2_34),
% 0.20/0.53    inference(avatar_split_clause,[],[f421,f354,f410])).
% 0.20/0.53  fof(f410,plain,(
% 0.20/0.53    spl2_39 <=> k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).
% 0.20/0.53  fof(f354,plain,(
% 0.20/0.53    spl2_34 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 0.20/0.53  fof(f421,plain,(
% 0.20/0.53    k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) | ~spl2_34),
% 0.20/0.53    inference(forward_demodulation,[],[f399,f67])).
% 0.20/0.53  fof(f399,plain,(
% 0.20/0.53    k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k1_xboole_0)) | ~spl2_34),
% 0.20/0.53    inference(resolution,[],[f355,f61])).
% 0.20/0.53  fof(f355,plain,(
% 0.20/0.53    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_struct_0(sK0))) | ~spl2_34),
% 0.20/0.53    inference(avatar_component_clause,[],[f354])).
% 0.20/0.53  fof(f392,plain,(
% 0.20/0.53    spl2_34),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f390])).
% 0.20/0.53  fof(f390,plain,(
% 0.20/0.53    $false | spl2_34),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f135,f356,f64])).
% 0.20/0.53  fof(f356,plain,(
% 0.20/0.53    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_struct_0(sK0))) | spl2_34),
% 0.20/0.53    inference(avatar_component_clause,[],[f354])).
% 0.20/0.53  fof(f135,plain,(
% 0.20/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.53    inference(superposition,[],[f55,f68])).
% 0.20/0.53  fof(f68,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.20/0.53    inference(definition_unfolding,[],[f46,f58])).
% 0.20/0.53  fof(f58,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.53  fof(f46,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.20/0.53  fof(f157,plain,(
% 0.20/0.53    spl2_11 | ~spl2_9),
% 0.20/0.53    inference(avatar_split_clause,[],[f151,f126,f153])).
% 0.20/0.53  fof(f151,plain,(
% 0.20/0.53    k4_xboole_0(k2_struct_0(sK0),sK1) = k3_subset_1(k2_struct_0(sK0),sK1) | ~spl2_9),
% 0.20/0.53    inference(resolution,[],[f60,f128])).
% 0.20/0.53  fof(f60,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f28])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,axiom,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.20/0.53  fof(f129,plain,(
% 0.20/0.53    spl2_9 | ~spl2_3 | ~spl2_6),
% 0.20/0.53    inference(avatar_split_clause,[],[f119,f102,f82,f126])).
% 0.20/0.53  fof(f82,plain,(
% 0.20/0.53    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.53  fof(f119,plain,(
% 0.20/0.53    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl2_3 | ~spl2_6)),
% 0.20/0.53    inference(backward_demodulation,[],[f84,f104])).
% 0.20/0.53  fof(f84,plain,(
% 0.20/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 0.20/0.53    inference(avatar_component_clause,[],[f82])).
% 0.20/0.53  fof(f106,plain,(
% 0.20/0.53    spl2_6 | ~spl2_5),
% 0.20/0.53    inference(avatar_split_clause,[],[f100,f94,f102])).
% 0.20/0.53  fof(f94,plain,(
% 0.20/0.53    spl2_5 <=> l1_struct_0(sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.53  fof(f100,plain,(
% 0.20/0.53    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl2_5),
% 0.20/0.53    inference(resolution,[],[f48,f96])).
% 0.20/0.53  fof(f96,plain,(
% 0.20/0.53    l1_struct_0(sK0) | ~spl2_5),
% 0.20/0.53    inference(avatar_component_clause,[],[f94])).
% 0.20/0.53  fof(f48,plain,(
% 0.20/0.53    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f22])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f13])).
% 0.20/0.53  fof(f13,axiom,(
% 0.20/0.53    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.53  fof(f98,plain,(
% 0.20/0.53    spl2_5 | ~spl2_4),
% 0.20/0.53    inference(avatar_split_clause,[],[f92,f87,f94])).
% 0.20/0.53  fof(f92,plain,(
% 0.20/0.53    l1_struct_0(sK0) | ~spl2_4),
% 0.20/0.53    inference(resolution,[],[f49,f89])).
% 0.20/0.53  fof(f49,plain,(
% 0.20/0.53    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f23])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f15])).
% 0.20/0.53  fof(f15,axiom,(
% 0.20/0.53    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.53  fof(f90,plain,(
% 0.20/0.53    spl2_4),
% 0.20/0.53    inference(avatar_split_clause,[],[f40,f87])).
% 0.20/0.53  fof(f40,plain,(
% 0.20/0.53    l1_pre_topc(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f36])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ((k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f33,f35,f34])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((k1_xboole_0 != k1_tops_1(sK0,X1) | ~v2_tops_1(X1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,X1) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    ? [X1] : ((k1_xboole_0 != k1_tops_1(sK0,X1) | ~v2_tops_1(X1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,X1) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.20/0.53    inference(flattening,[],[f32])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : (((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.20/0.53    inference(nnf_transformation,[],[f21])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> k1_xboole_0 = k1_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f20])).
% 0.20/0.53  fof(f20,negated_conjecture,(
% 0.20/0.53    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 0.20/0.53    inference(negated_conjecture,[],[f19])).
% 0.20/0.53  fof(f19,conjecture,(
% 0.20/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).
% 0.20/0.53  fof(f85,plain,(
% 0.20/0.53    spl2_3),
% 0.20/0.53    inference(avatar_split_clause,[],[f41,f82])).
% 0.20/0.53  fof(f41,plain,(
% 0.20/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.53    inference(cnf_transformation,[],[f36])).
% 0.20/0.53  fof(f80,plain,(
% 0.20/0.53    spl2_1 | spl2_2),
% 0.20/0.53    inference(avatar_split_clause,[],[f42,f76,f72])).
% 0.20/0.53  fof(f42,plain,(
% 0.20/0.53    k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f36])).
% 0.20/0.53  fof(f79,plain,(
% 0.20/0.53    ~spl2_1 | ~spl2_2),
% 0.20/0.53    inference(avatar_split_clause,[],[f43,f76,f72])).
% 0.20/0.53  fof(f43,plain,(
% 0.20/0.53    k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f36])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (22136)------------------------------
% 0.20/0.53  % (22136)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (22136)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (22136)Memory used [KB]: 8187
% 0.20/0.53  % (22136)Time elapsed: 0.068 s
% 0.20/0.53  % (22136)------------------------------
% 0.20/0.53  % (22136)------------------------------
% 0.20/0.53  % (22128)Success in time 0.174 s
%------------------------------------------------------------------------------
