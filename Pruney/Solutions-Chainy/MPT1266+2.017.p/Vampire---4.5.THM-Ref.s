%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:25 EST 2020

% Result     : Theorem 2.16s
% Output     : Refutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :  183 (1289 expanded)
%              Number of leaves         :   31 ( 376 expanded)
%              Depth                    :   24
%              Number of atoms          :  448 (4476 expanded)
%              Number of equality atoms :   96 (1304 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2986,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f1367,f1460,f2235,f2729,f2883,f2888,f2920,f2923,f2972,f2981,f2985])).

fof(f2985,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f2984])).

fof(f2984,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(resolution,[],[f88,f81])).

fof(f81,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl2_1
  <=> v2_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f88,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ spl2_2 ),
    inference(trivial_inequality_removal,[],[f87])).

fof(f87,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v2_tops_1(sK1,sK0)
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f50,f85])).

fof(f85,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl2_2
  <=> k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f50,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( ( k1_xboole_0 != k1_tops_1(sK0,sK1)
      | ~ v2_tops_1(sK1,sK0) )
    & ( k1_xboole_0 = k1_tops_1(sK0,sK1)
      | v2_tops_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f40,f42,f41])).

fof(f41,plain,
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

fof(f42,plain,
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

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(X0,X1)
            | ~ v2_tops_1(X1,X0) )
          & ( k1_xboole_0 = k1_tops_1(X0,X1)
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(X0,X1)
            | ~ v2_tops_1(X1,X0) )
          & ( k1_xboole_0 = k1_tops_1(X0,X1)
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> k1_xboole_0 = k1_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

fof(f2981,plain,
    ( spl2_2
    | ~ spl2_61 ),
    inference(avatar_contradiction_clause,[],[f2980])).

fof(f2980,plain,
    ( $false
    | spl2_2
    | ~ spl2_61 ),
    inference(trivial_inequality_removal,[],[f2979])).

fof(f2979,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl2_2
    | ~ spl2_61 ),
    inference(superposition,[],[f84,f2978])).

fof(f2978,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl2_61 ),
    inference(forward_demodulation,[],[f2975,f113])).

fof(f113,plain,(
    ! [X3] : k1_xboole_0 = k3_subset_1(X3,X3) ),
    inference(forward_demodulation,[],[f110,f74])).

fof(f74,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f51,f73])).

fof(f73,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f54,f52])).

fof(f52,plain,(
    ! [X0] : k1_subset_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_subset_1(X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f54,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

fof(f51,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f110,plain,(
    ! [X3] : k1_xboole_0 = k3_subset_1(X3,k3_subset_1(X3,k1_xboole_0)) ),
    inference(resolution,[],[f66,f53])).

fof(f53,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f2975,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ spl2_61 ),
    inference(backward_demodulation,[],[f2047,f2971])).

fof(f2971,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))
    | ~ spl2_61 ),
    inference(avatar_component_clause,[],[f2969])).

fof(f2969,plain,
    ( spl2_61
  <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_61])])).

fof(f2047,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) ),
    inference(resolution,[],[f2033,f90])).

fof(f90,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f48,f89])).

fof(f89,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f55,f77])).

fof(f77,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f56,f47])).

fof(f47,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f56,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f55,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f48,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f2033,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k1_tops_1(sK0,X0) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) ) ),
    inference(forward_demodulation,[],[f2032,f89])).

fof(f2032,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) ) ),
    inference(forward_demodulation,[],[f2031,f89])).

fof(f2031,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) ) ),
    inference(resolution,[],[f58,f47])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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

fof(f84,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f2972,plain,
    ( ~ spl2_54
    | spl2_61
    | ~ spl2_57
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f2926,f1364,f2880,f2969,f2712])).

fof(f2712,plain,
    ( spl2_54
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).

fof(f2880,plain,
    ( spl2_57
  <=> m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_57])])).

fof(f1364,plain,
    ( spl2_18
  <=> v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f2926,plain,
    ( ~ m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_18 ),
    inference(forward_demodulation,[],[f2925,f89])).

fof(f2925,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))
    | ~ m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_18 ),
    inference(resolution,[],[f1365,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_tops_1(X1,X0)
      | k2_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
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

fof(f1365,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f1364])).

fof(f2923,plain,(
    spl2_58 ),
    inference(avatar_contradiction_clause,[],[f2921])).

fof(f2921,plain,
    ( $false
    | spl2_58 ),
    inference(resolution,[],[f2919,f90])).

fof(f2919,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | spl2_58 ),
    inference(avatar_component_clause,[],[f2917])).

fof(f2917,plain,
    ( spl2_58
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_58])])).

fof(f2920,plain,
    ( ~ spl2_54
    | spl2_18
    | ~ spl2_58
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f2891,f79,f2917,f1364,f2712])).

fof(f2891,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(forward_demodulation,[],[f2890,f89])).

fof(f2890,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(forward_demodulation,[],[f2889,f89])).

fof(f2889,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(resolution,[],[f81,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v2_tops_1(X1,X0)
      | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
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

fof(f2888,plain,(
    spl2_57 ),
    inference(avatar_contradiction_clause,[],[f2886])).

fof(f2886,plain,
    ( $false
    | spl2_57 ),
    inference(resolution,[],[f2884,f90])).

fof(f2884,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | spl2_57 ),
    inference(resolution,[],[f2882,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f2882,plain,
    ( ~ m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl2_57 ),
    inference(avatar_component_clause,[],[f2880])).

fof(f2883,plain,
    ( ~ spl2_54
    | spl2_18
    | ~ spl2_57
    | ~ spl2_2
    | ~ spl2_48 ),
    inference(avatar_split_clause,[],[f2878,f2232,f83,f2880,f1364,f2712])).

fof(f2232,plain,
    ( spl2_48
  <=> r1_tarski(k2_tops_1(sK0,k3_subset_1(k2_struct_0(sK0),sK1)),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_48])])).

fof(f2878,plain,
    ( ~ m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_2
    | ~ spl2_48 ),
    inference(forward_demodulation,[],[f2877,f89])).

fof(f2877,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_2
    | ~ spl2_48 ),
    inference(trivial_inequality_removal,[],[f2876])).

fof(f2876,plain,
    ( k2_struct_0(sK0) != k2_struct_0(sK0)
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_2
    | ~ spl2_48 ),
    inference(superposition,[],[f60,f2867])).

fof(f2867,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))
    | ~ spl2_2
    | ~ spl2_48 ),
    inference(forward_demodulation,[],[f2836,f74])).

fof(f2836,plain,
    ( k3_subset_1(k2_struct_0(sK0),k1_xboole_0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))
    | ~ spl2_2
    | ~ spl2_48 ),
    inference(backward_demodulation,[],[f2823,f2834])).

fof(f2834,plain,
    ( k1_xboole_0 = k7_subset_1(sK1,sK1,k2_tops_1(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))
    | ~ spl2_2
    | ~ spl2_48 ),
    inference(forward_demodulation,[],[f2827,f2055])).

fof(f2055,plain,
    ( k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f2047,f85])).

fof(f2827,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) = k7_subset_1(sK1,sK1,k2_tops_1(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))
    | ~ spl2_48 ),
    inference(superposition,[],[f802,f2823])).

fof(f802,plain,(
    ! [X6] : k7_subset_1(sK1,sK1,X6) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k7_subset_1(sK1,sK1,X6))) ),
    inference(resolution,[],[f798,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(resolution,[],[f66,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
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

fof(f798,plain,(
    ! [X0] : r1_tarski(k7_subset_1(sK1,sK1,X0),k2_struct_0(sK0)) ),
    inference(resolution,[],[f795,f101])).

fof(f101,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(resolution,[],[f99,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f99,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f98,f53])).

fof(f98,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
      | m1_subset_1(X0,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f65,f74])).

fof(f795,plain,(
    ! [X114,X113] :
      ( ~ r1_tarski(k2_struct_0(sK0),X113)
      | r1_tarski(k7_subset_1(sK1,sK1,X114),X113) ) ),
    inference(resolution,[],[f487,f92])).

fof(f92,plain,(
    r1_tarski(sK1,k2_struct_0(sK0)) ),
    inference(resolution,[],[f69,f90])).

fof(f487,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(k7_subset_1(X0,X0,X3),X2) ) ),
    inference(backward_demodulation,[],[f107,f373])).

fof(f373,plain,(
    ! [X4,X3] : k7_subset_1(X3,X3,X4) = k5_xboole_0(X3,k3_xboole_0(X3,X4)) ),
    inference(resolution,[],[f76,f99])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f71,f64])).

fof(f64,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f107,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X3)),X2) ) ),
    inference(resolution,[],[f96,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f96,plain,(
    ! [X4,X5,X3] :
      ( r1_tarski(k5_xboole_0(X3,k3_xboole_0(X3,X5)),X4)
      | ~ r1_tarski(X3,X4) ) ),
    inference(resolution,[],[f72,f75])).

fof(f75,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f63,f64])).

fof(f63,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f2823,plain,
    ( k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k7_subset_1(sK1,sK1,k2_tops_1(sK0,k3_subset_1(k2_struct_0(sK0),sK1))))
    | ~ spl2_48 ),
    inference(forward_demodulation,[],[f2814,f1678])).

fof(f1678,plain,(
    k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k4_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1),k2_tops_1(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) ),
    inference(resolution,[],[f1662,f134])).

fof(f134,plain,(
    r1_tarski(k3_subset_1(k2_struct_0(sK0),sK1),k2_struct_0(sK0)) ),
    inference(resolution,[],[f131,f101])).

fof(f131,plain,(
    ! [X10] :
      ( ~ r1_tarski(k2_struct_0(sK0),X10)
      | r1_tarski(k3_subset_1(k2_struct_0(sK0),sK1),X10) ) ),
    inference(resolution,[],[f105,f90])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X1,X2)
      | r1_tarski(k3_subset_1(X1,X0),X2) ) ),
    inference(resolution,[],[f97,f72])).

fof(f97,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_subset_1(X1,X0),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f65,f69])).

fof(f1662,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_struct_0(sK0))
      | k2_pre_topc(sK0,X0) = k4_subset_1(k2_struct_0(sK0),X0,k2_tops_1(sK0,X0)) ) ),
    inference(resolution,[],[f1661,f70])).

fof(f1661,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = k4_subset_1(k2_struct_0(sK0),X0,k2_tops_1(sK0,X0)) ) ),
    inference(forward_demodulation,[],[f1660,f89])).

fof(f1660,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) ) ),
    inference(forward_demodulation,[],[f1659,f89])).

fof(f1659,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) ) ),
    inference(resolution,[],[f57,f47])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f2814,plain,
    ( k4_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1),k2_tops_1(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) = k3_subset_1(k2_struct_0(sK0),k7_subset_1(sK1,sK1,k2_tops_1(sK0,k3_subset_1(k2_struct_0(sK0),sK1))))
    | ~ spl2_48 ),
    inference(resolution,[],[f2672,f2234])).

fof(f2234,plain,
    ( r1_tarski(k2_tops_1(sK0,k3_subset_1(k2_struct_0(sK0),sK1)),k2_struct_0(sK0))
    | ~ spl2_48 ),
    inference(avatar_component_clause,[],[f2232])).

fof(f2672,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_struct_0(sK0))
      | k3_subset_1(k2_struct_0(sK0),k7_subset_1(sK1,sK1,X0)) = k4_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1),X0) ) ),
    inference(resolution,[],[f2296,f70])).

fof(f2296,plain,(
    ! [X20] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(k2_struct_0(sK0)))
      | k4_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1),X20) = k3_subset_1(k2_struct_0(sK0),k7_subset_1(sK1,sK1,X20)) ) ),
    inference(forward_demodulation,[],[f2288,f514])).

fof(f514,plain,(
    ! [X16] : k7_subset_1(k2_struct_0(sK0),sK1,X16) = k7_subset_1(sK1,sK1,X16) ),
    inference(backward_demodulation,[],[f381,f373])).

fof(f381,plain,(
    ! [X16] : k7_subset_1(k2_struct_0(sK0),sK1,X16) = k5_xboole_0(sK1,k3_xboole_0(sK1,X16)) ),
    inference(resolution,[],[f76,f90])).

fof(f2288,plain,(
    ! [X20] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(k2_struct_0(sK0)))
      | k3_subset_1(k2_struct_0(sK0),k7_subset_1(k2_struct_0(sK0),sK1,X20)) = k4_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1),X20) ) ),
    inference(resolution,[],[f67,f90])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_subset_1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X0) != k2_pre_topc(X0,X1)
      | v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f2729,plain,(
    spl2_54 ),
    inference(avatar_contradiction_clause,[],[f2728])).

fof(f2728,plain,
    ( $false
    | spl2_54 ),
    inference(resolution,[],[f2714,f47])).

fof(f2714,plain,
    ( ~ l1_pre_topc(sK0)
    | spl2_54 ),
    inference(avatar_component_clause,[],[f2712])).

fof(f2235,plain,
    ( ~ spl2_31
    | spl2_48 ),
    inference(avatar_split_clause,[],[f2223,f2232,f1445])).

fof(f1445,plain,
    ( spl2_31
  <=> r1_tarski(k3_subset_1(k2_struct_0(sK0),sK1),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).

fof(f2223,plain,
    ( r1_tarski(k2_tops_1(sK0,k3_subset_1(k2_struct_0(sK0),sK1)),k2_struct_0(sK0))
    | ~ r1_tarski(k3_subset_1(k2_struct_0(sK0),sK1),k2_struct_0(sK0)) ),
    inference(superposition,[],[f2182,f314])).

fof(f314,plain,(
    k2_tops_1(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_tops_1(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))) ),
    inference(resolution,[],[f212,f134])).

fof(f212,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_struct_0(sK0))
      | k2_tops_1(sK0,X0) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_tops_1(sK0,X0))) ) ),
    inference(resolution,[],[f202,f70])).

fof(f202,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_tops_1(sK0,X2) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_tops_1(sK0,X2))) ) ),
    inference(resolution,[],[f200,f66])).

fof(f200,plain,(
    ! [X0] :
      ( m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f199,f89])).

fof(f199,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f198,f89])).

fof(f198,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f68,f47])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f2182,plain,(
    ! [X0] :
      ( r1_tarski(k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_tops_1(sK0,X0))),k2_struct_0(sK0))
      | ~ r1_tarski(X0,k2_struct_0(sK0)) ) ),
    inference(resolution,[],[f2181,f70])).

fof(f2181,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | r1_tarski(k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_tops_1(sK0,X0))),k2_struct_0(sK0)) ) ),
    inference(resolution,[],[f1824,f101])).

fof(f1824,plain,(
    ! [X15,X16] :
      ( ~ r1_tarski(k2_struct_0(sK0),X16)
      | r1_tarski(k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_tops_1(sK0,X15))),X16)
      | ~ m1_subset_1(X15,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(resolution,[],[f130,f200])).

fof(f130,plain,(
    ! [X8,X7,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(X7))
      | r1_tarski(k3_subset_1(X7,k3_subset_1(X7,X9)),X8)
      | ~ r1_tarski(X7,X8) ) ),
    inference(resolution,[],[f105,f65])).

fof(f1460,plain,(
    spl2_31 ),
    inference(avatar_contradiction_clause,[],[f1457])).

fof(f1457,plain,
    ( $false
    | spl2_31 ),
    inference(resolution,[],[f1447,f134])).

fof(f1447,plain,
    ( ~ r1_tarski(k3_subset_1(k2_struct_0(sK0),sK1),k2_struct_0(sK0))
    | spl2_31 ),
    inference(avatar_component_clause,[],[f1445])).

fof(f1367,plain,
    ( spl2_1
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f1338,f1364,f79])).

fof(f1338,plain,
    ( ~ v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | v2_tops_1(sK1,sK0) ),
    inference(resolution,[],[f1325,f90])).

fof(f1325,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0)
      | v2_tops_1(X0,sK0) ) ),
    inference(forward_demodulation,[],[f1324,f89])).

fof(f1324,plain,(
    ! [X0] :
      ( ~ v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tops_1(X0,sK0) ) ),
    inference(forward_demodulation,[],[f1323,f89])).

fof(f1323,plain,(
    ! [X0] :
      ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tops_1(X0,sK0) ) ),
    inference(resolution,[],[f62,f47])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f86,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f49,f83,f79])).

fof(f49,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:10:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.45  % (9365)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.46  % (9363)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.46  % (9369)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.46  % (9362)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.46  % (9368)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.46  % (9374)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.47  % (9376)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.47  % (9364)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.48  % (9372)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.48  % (9370)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.48  % (9366)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.48  % (9360)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.48  % (9373)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.49  % (9371)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.49  % (9359)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.50  % (9367)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.50  % (9361)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.52  % (9375)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 2.16/0.63  % (9361)Refutation found. Thanks to Tanya!
% 2.16/0.63  % SZS status Theorem for theBenchmark
% 2.16/0.63  % SZS output start Proof for theBenchmark
% 2.16/0.63  fof(f2986,plain,(
% 2.16/0.63    $false),
% 2.16/0.63    inference(avatar_sat_refutation,[],[f86,f1367,f1460,f2235,f2729,f2883,f2888,f2920,f2923,f2972,f2981,f2985])).
% 2.16/0.63  fof(f2985,plain,(
% 2.16/0.63    ~spl2_1 | ~spl2_2),
% 2.16/0.63    inference(avatar_contradiction_clause,[],[f2984])).
% 2.16/0.63  fof(f2984,plain,(
% 2.16/0.63    $false | (~spl2_1 | ~spl2_2)),
% 2.16/0.63    inference(resolution,[],[f88,f81])).
% 2.16/0.63  fof(f81,plain,(
% 2.16/0.63    v2_tops_1(sK1,sK0) | ~spl2_1),
% 2.16/0.63    inference(avatar_component_clause,[],[f79])).
% 2.16/0.63  fof(f79,plain,(
% 2.16/0.63    spl2_1 <=> v2_tops_1(sK1,sK0)),
% 2.16/0.63    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 2.16/0.63  fof(f88,plain,(
% 2.16/0.63    ~v2_tops_1(sK1,sK0) | ~spl2_2),
% 2.16/0.63    inference(trivial_inequality_removal,[],[f87])).
% 2.16/0.63  fof(f87,plain,(
% 2.16/0.63    k1_xboole_0 != k1_xboole_0 | ~v2_tops_1(sK1,sK0) | ~spl2_2),
% 2.16/0.63    inference(forward_demodulation,[],[f50,f85])).
% 2.16/0.63  fof(f85,plain,(
% 2.16/0.63    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~spl2_2),
% 2.16/0.63    inference(avatar_component_clause,[],[f83])).
% 2.16/0.63  fof(f83,plain,(
% 2.16/0.63    spl2_2 <=> k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 2.16/0.63    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 2.16/0.63  fof(f50,plain,(
% 2.16/0.63    k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)),
% 2.16/0.63    inference(cnf_transformation,[],[f43])).
% 2.16/0.63  fof(f43,plain,(
% 2.16/0.63    ((k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 2.16/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f40,f42,f41])).
% 2.16/0.63  fof(f41,plain,(
% 2.16/0.63    ? [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((k1_xboole_0 != k1_tops_1(sK0,X1) | ~v2_tops_1(X1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,X1) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 2.16/0.63    introduced(choice_axiom,[])).
% 2.16/0.63  fof(f42,plain,(
% 2.16/0.63    ? [X1] : ((k1_xboole_0 != k1_tops_1(sK0,X1) | ~v2_tops_1(X1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,X1) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.16/0.63    introduced(choice_axiom,[])).
% 2.16/0.63  fof(f40,plain,(
% 2.16/0.63    ? [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.16/0.63    inference(flattening,[],[f39])).
% 2.16/0.63  fof(f39,plain,(
% 2.16/0.63    ? [X0] : (? [X1] : (((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.16/0.63    inference(nnf_transformation,[],[f24])).
% 2.16/0.63  fof(f24,plain,(
% 2.16/0.63    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> k1_xboole_0 = k1_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.16/0.63    inference(ennf_transformation,[],[f22])).
% 2.16/0.63  fof(f22,negated_conjecture,(
% 2.16/0.63    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 2.16/0.63    inference(negated_conjecture,[],[f21])).
% 2.16/0.63  fof(f21,conjecture,(
% 2.16/0.63    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 2.16/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).
% 2.16/0.63  fof(f2981,plain,(
% 2.16/0.63    spl2_2 | ~spl2_61),
% 2.16/0.63    inference(avatar_contradiction_clause,[],[f2980])).
% 2.16/0.63  fof(f2980,plain,(
% 2.16/0.63    $false | (spl2_2 | ~spl2_61)),
% 2.16/0.63    inference(trivial_inequality_removal,[],[f2979])).
% 2.16/0.63  fof(f2979,plain,(
% 2.16/0.63    k1_xboole_0 != k1_xboole_0 | (spl2_2 | ~spl2_61)),
% 2.16/0.63    inference(superposition,[],[f84,f2978])).
% 2.16/0.63  fof(f2978,plain,(
% 2.16/0.63    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~spl2_61),
% 2.16/0.63    inference(forward_demodulation,[],[f2975,f113])).
% 2.16/0.63  fof(f113,plain,(
% 2.16/0.63    ( ! [X3] : (k1_xboole_0 = k3_subset_1(X3,X3)) )),
% 2.16/0.63    inference(forward_demodulation,[],[f110,f74])).
% 2.16/0.63  fof(f74,plain,(
% 2.16/0.63    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 2.16/0.63    inference(definition_unfolding,[],[f51,f73])).
% 2.16/0.63  fof(f73,plain,(
% 2.16/0.63    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 2.16/0.63    inference(definition_unfolding,[],[f54,f52])).
% 2.16/0.63  fof(f52,plain,(
% 2.16/0.63    ( ! [X0] : (k1_subset_1(X0) = k1_xboole_0) )),
% 2.16/0.63    inference(cnf_transformation,[],[f4])).
% 2.16/0.63  fof(f4,axiom,(
% 2.16/0.63    ! [X0] : k1_subset_1(X0) = k1_xboole_0),
% 2.16/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 2.16/0.63  fof(f54,plain,(
% 2.16/0.63    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 2.16/0.63    inference(cnf_transformation,[],[f9])).
% 2.16/0.63  fof(f9,axiom,(
% 2.16/0.63    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 2.16/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).
% 2.16/0.63  fof(f51,plain,(
% 2.16/0.63    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.16/0.63    inference(cnf_transformation,[],[f5])).
% 2.16/0.63  fof(f5,axiom,(
% 2.16/0.63    ! [X0] : k2_subset_1(X0) = X0),
% 2.16/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 2.16/0.63  fof(f110,plain,(
% 2.16/0.63    ( ! [X3] : (k1_xboole_0 = k3_subset_1(X3,k3_subset_1(X3,k1_xboole_0))) )),
% 2.16/0.63    inference(resolution,[],[f66,f53])).
% 2.16/0.63  fof(f53,plain,(
% 2.16/0.63    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.16/0.63    inference(cnf_transformation,[],[f11])).
% 2.16/0.63  fof(f11,axiom,(
% 2.16/0.63    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.16/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 2.16/0.63  fof(f66,plain,(
% 2.16/0.63    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 2.16/0.63    inference(cnf_transformation,[],[f32])).
% 2.16/0.63  fof(f32,plain,(
% 2.16/0.63    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.16/0.63    inference(ennf_transformation,[],[f7])).
% 2.16/0.63  fof(f7,axiom,(
% 2.16/0.63    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.16/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 2.16/0.63  fof(f2975,plain,(
% 2.16/0.63    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) | ~spl2_61),
% 2.16/0.63    inference(backward_demodulation,[],[f2047,f2971])).
% 2.16/0.63  fof(f2971,plain,(
% 2.16/0.63    k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) | ~spl2_61),
% 2.16/0.63    inference(avatar_component_clause,[],[f2969])).
% 2.16/0.63  fof(f2969,plain,(
% 2.16/0.63    spl2_61 <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))),
% 2.16/0.63    introduced(avatar_definition,[new_symbols(naming,[spl2_61])])).
% 2.16/0.63  fof(f2047,plain,(
% 2.16/0.63    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))),
% 2.16/0.63    inference(resolution,[],[f2033,f90])).
% 2.16/0.63  fof(f90,plain,(
% 2.16/0.63    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 2.16/0.63    inference(backward_demodulation,[],[f48,f89])).
% 2.16/0.63  fof(f89,plain,(
% 2.16/0.63    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 2.16/0.63    inference(resolution,[],[f55,f77])).
% 2.16/0.63  fof(f77,plain,(
% 2.16/0.63    l1_struct_0(sK0)),
% 2.16/0.63    inference(resolution,[],[f56,f47])).
% 2.16/0.63  fof(f47,plain,(
% 2.16/0.63    l1_pre_topc(sK0)),
% 2.16/0.63    inference(cnf_transformation,[],[f43])).
% 2.16/0.63  fof(f56,plain,(
% 2.16/0.63    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 2.16/0.63    inference(cnf_transformation,[],[f26])).
% 2.16/0.63  fof(f26,plain,(
% 2.16/0.63    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.16/0.63    inference(ennf_transformation,[],[f15])).
% 2.16/0.63  fof(f15,axiom,(
% 2.16/0.63    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.16/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 2.16/0.63  fof(f55,plain,(
% 2.16/0.63    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 2.16/0.63    inference(cnf_transformation,[],[f25])).
% 2.16/0.63  fof(f25,plain,(
% 2.16/0.63    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.16/0.63    inference(ennf_transformation,[],[f14])).
% 2.16/0.63  fof(f14,axiom,(
% 2.16/0.63    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.16/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 2.16/0.63  fof(f48,plain,(
% 2.16/0.63    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.16/0.63    inference(cnf_transformation,[],[f43])).
% 2.16/0.63  fof(f2033,plain,(
% 2.16/0.63    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k1_tops_1(sK0,X0) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0)))) )),
% 2.16/0.63    inference(forward_demodulation,[],[f2032,f89])).
% 2.16/0.63  fof(f2032,plain,(
% 2.16/0.63    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)))) )),
% 2.16/0.63    inference(forward_demodulation,[],[f2031,f89])).
% 2.16/0.63  fof(f2031,plain,(
% 2.16/0.63    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)))) )),
% 2.16/0.63    inference(resolution,[],[f58,f47])).
% 2.16/0.63  fof(f58,plain,(
% 2.16/0.63    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))) )),
% 2.16/0.63    inference(cnf_transformation,[],[f28])).
% 2.16/0.63  fof(f28,plain,(
% 2.16/0.63    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.16/0.63    inference(ennf_transformation,[],[f16])).
% 2.16/0.63  fof(f16,axiom,(
% 2.16/0.63    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 2.16/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).
% 2.16/0.63  fof(f84,plain,(
% 2.16/0.63    k1_xboole_0 != k1_tops_1(sK0,sK1) | spl2_2),
% 2.16/0.63    inference(avatar_component_clause,[],[f83])).
% 2.16/0.63  fof(f2972,plain,(
% 2.16/0.63    ~spl2_54 | spl2_61 | ~spl2_57 | ~spl2_18),
% 2.16/0.63    inference(avatar_split_clause,[],[f2926,f1364,f2880,f2969,f2712])).
% 2.16/0.63  fof(f2712,plain,(
% 2.16/0.63    spl2_54 <=> l1_pre_topc(sK0)),
% 2.16/0.63    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).
% 2.16/0.63  fof(f2880,plain,(
% 2.16/0.63    spl2_57 <=> m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))),
% 2.16/0.63    introduced(avatar_definition,[new_symbols(naming,[spl2_57])])).
% 2.16/0.63  fof(f1364,plain,(
% 2.16/0.63    spl2_18 <=> v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0)),
% 2.16/0.63    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 2.16/0.63  fof(f2926,plain,(
% 2.16/0.63    ~m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) | ~l1_pre_topc(sK0) | ~spl2_18),
% 2.16/0.63    inference(forward_demodulation,[],[f2925,f89])).
% 2.16/0.63  fof(f2925,plain,(
% 2.16/0.63    k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) | ~m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_18),
% 2.16/0.63    inference(resolution,[],[f1365,f59])).
% 2.16/0.63  fof(f59,plain,(
% 2.16/0.63    ( ! [X0,X1] : (~v1_tops_1(X1,X0) | k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.16/0.63    inference(cnf_transformation,[],[f44])).
% 2.16/0.63  fof(f44,plain,(
% 2.16/0.63    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.16/0.63    inference(nnf_transformation,[],[f29])).
% 2.16/0.63  fof(f29,plain,(
% 2.16/0.63    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.16/0.63    inference(ennf_transformation,[],[f17])).
% 2.16/0.63  fof(f17,axiom,(
% 2.16/0.63    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 2.16/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).
% 2.16/0.63  fof(f1365,plain,(
% 2.16/0.63    v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | ~spl2_18),
% 2.16/0.63    inference(avatar_component_clause,[],[f1364])).
% 2.16/0.63  fof(f2923,plain,(
% 2.16/0.63    spl2_58),
% 2.16/0.63    inference(avatar_contradiction_clause,[],[f2921])).
% 2.16/0.63  fof(f2921,plain,(
% 2.16/0.63    $false | spl2_58),
% 2.16/0.63    inference(resolution,[],[f2919,f90])).
% 2.16/0.63  fof(f2919,plain,(
% 2.16/0.63    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | spl2_58),
% 2.16/0.63    inference(avatar_component_clause,[],[f2917])).
% 2.16/0.63  fof(f2917,plain,(
% 2.16/0.63    spl2_58 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 2.16/0.63    introduced(avatar_definition,[new_symbols(naming,[spl2_58])])).
% 2.16/0.63  fof(f2920,plain,(
% 2.16/0.63    ~spl2_54 | spl2_18 | ~spl2_58 | ~spl2_1),
% 2.16/0.63    inference(avatar_split_clause,[],[f2891,f79,f2917,f1364,f2712])).
% 2.16/0.63  fof(f2891,plain,(
% 2.16/0.63    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | ~l1_pre_topc(sK0) | ~spl2_1),
% 2.16/0.63    inference(forward_demodulation,[],[f2890,f89])).
% 2.16/0.63  fof(f2890,plain,(
% 2.16/0.63    v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_1),
% 2.16/0.63    inference(forward_demodulation,[],[f2889,f89])).
% 2.16/0.63  fof(f2889,plain,(
% 2.16/0.63    v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_1),
% 2.16/0.63    inference(resolution,[],[f81,f61])).
% 2.16/0.63  fof(f61,plain,(
% 2.16/0.63    ( ! [X0,X1] : (~v2_tops_1(X1,X0) | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.16/0.63    inference(cnf_transformation,[],[f45])).
% 2.16/0.63  fof(f45,plain,(
% 2.16/0.63    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.16/0.63    inference(nnf_transformation,[],[f30])).
% 2.16/0.63  fof(f30,plain,(
% 2.16/0.63    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.16/0.63    inference(ennf_transformation,[],[f18])).
% 2.16/0.63  fof(f18,axiom,(
% 2.16/0.63    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 2.16/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_1)).
% 2.16/0.63  fof(f2888,plain,(
% 2.16/0.63    spl2_57),
% 2.16/0.63    inference(avatar_contradiction_clause,[],[f2886])).
% 2.16/0.63  fof(f2886,plain,(
% 2.16/0.63    $false | spl2_57),
% 2.16/0.63    inference(resolution,[],[f2884,f90])).
% 2.16/0.63  fof(f2884,plain,(
% 2.16/0.63    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | spl2_57),
% 2.16/0.63    inference(resolution,[],[f2882,f65])).
% 2.16/0.63  fof(f65,plain,(
% 2.16/0.63    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.16/0.63    inference(cnf_transformation,[],[f31])).
% 2.16/0.63  fof(f31,plain,(
% 2.16/0.63    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.16/0.63    inference(ennf_transformation,[],[f6])).
% 2.16/0.63  fof(f6,axiom,(
% 2.16/0.63    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.16/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 2.16/0.63  fof(f2882,plain,(
% 2.16/0.63    ~m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | spl2_57),
% 2.16/0.63    inference(avatar_component_clause,[],[f2880])).
% 2.16/0.63  fof(f2883,plain,(
% 2.16/0.63    ~spl2_54 | spl2_18 | ~spl2_57 | ~spl2_2 | ~spl2_48),
% 2.16/0.63    inference(avatar_split_clause,[],[f2878,f2232,f83,f2880,f1364,f2712])).
% 2.16/0.63  fof(f2232,plain,(
% 2.16/0.63    spl2_48 <=> r1_tarski(k2_tops_1(sK0,k3_subset_1(k2_struct_0(sK0),sK1)),k2_struct_0(sK0))),
% 2.16/0.63    introduced(avatar_definition,[new_symbols(naming,[spl2_48])])).
% 2.16/0.63  fof(f2878,plain,(
% 2.16/0.63    ~m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | ~l1_pre_topc(sK0) | (~spl2_2 | ~spl2_48)),
% 2.16/0.63    inference(forward_demodulation,[],[f2877,f89])).
% 2.16/0.63  fof(f2877,plain,(
% 2.16/0.63    v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl2_2 | ~spl2_48)),
% 2.16/0.63    inference(trivial_inequality_removal,[],[f2876])).
% 2.16/0.63  fof(f2876,plain,(
% 2.16/0.63    k2_struct_0(sK0) != k2_struct_0(sK0) | v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl2_2 | ~spl2_48)),
% 2.16/0.63    inference(superposition,[],[f60,f2867])).
% 2.16/0.63  fof(f2867,plain,(
% 2.16/0.63    k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) | (~spl2_2 | ~spl2_48)),
% 2.16/0.63    inference(forward_demodulation,[],[f2836,f74])).
% 2.16/0.63  fof(f2836,plain,(
% 2.16/0.63    k3_subset_1(k2_struct_0(sK0),k1_xboole_0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) | (~spl2_2 | ~spl2_48)),
% 2.16/0.63    inference(backward_demodulation,[],[f2823,f2834])).
% 2.16/0.63  fof(f2834,plain,(
% 2.16/0.63    k1_xboole_0 = k7_subset_1(sK1,sK1,k2_tops_1(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) | (~spl2_2 | ~spl2_48)),
% 2.16/0.63    inference(forward_demodulation,[],[f2827,f2055])).
% 2.16/0.63  fof(f2055,plain,(
% 2.16/0.63    k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) | ~spl2_2),
% 2.16/0.63    inference(forward_demodulation,[],[f2047,f85])).
% 2.16/0.63  fof(f2827,plain,(
% 2.16/0.63    k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) = k7_subset_1(sK1,sK1,k2_tops_1(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) | ~spl2_48),
% 2.16/0.63    inference(superposition,[],[f802,f2823])).
% 2.16/0.63  fof(f802,plain,(
% 2.16/0.63    ( ! [X6] : (k7_subset_1(sK1,sK1,X6) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k7_subset_1(sK1,sK1,X6)))) )),
% 2.16/0.63    inference(resolution,[],[f798,f108])).
% 2.16/0.63  fof(f108,plain,(
% 2.16/0.63    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 2.16/0.63    inference(resolution,[],[f66,f70])).
% 2.16/0.63  fof(f70,plain,(
% 2.16/0.63    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.16/0.63    inference(cnf_transformation,[],[f46])).
% 2.16/0.63  fof(f46,plain,(
% 2.16/0.63    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.16/0.63    inference(nnf_transformation,[],[f12])).
% 2.16/0.63  fof(f12,axiom,(
% 2.16/0.63    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.16/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.16/0.63  fof(f798,plain,(
% 2.16/0.63    ( ! [X0] : (r1_tarski(k7_subset_1(sK1,sK1,X0),k2_struct_0(sK0))) )),
% 2.16/0.63    inference(resolution,[],[f795,f101])).
% 2.16/0.63  fof(f101,plain,(
% 2.16/0.63    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 2.16/0.63    inference(resolution,[],[f99,f69])).
% 2.16/0.63  fof(f69,plain,(
% 2.16/0.63    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.16/0.63    inference(cnf_transformation,[],[f46])).
% 2.16/0.63  fof(f99,plain,(
% 2.16/0.63    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 2.16/0.63    inference(resolution,[],[f98,f53])).
% 2.16/0.63  fof(f98,plain,(
% 2.16/0.63    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) | m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 2.16/0.63    inference(superposition,[],[f65,f74])).
% 2.16/0.63  fof(f795,plain,(
% 2.16/0.63    ( ! [X114,X113] : (~r1_tarski(k2_struct_0(sK0),X113) | r1_tarski(k7_subset_1(sK1,sK1,X114),X113)) )),
% 2.16/0.63    inference(resolution,[],[f487,f92])).
% 2.16/0.63  fof(f92,plain,(
% 2.16/0.63    r1_tarski(sK1,k2_struct_0(sK0))),
% 2.16/0.63    inference(resolution,[],[f69,f90])).
% 2.16/0.63  fof(f487,plain,(
% 2.16/0.63    ( ! [X2,X0,X3,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(k7_subset_1(X0,X0,X3),X2)) )),
% 2.16/0.63    inference(backward_demodulation,[],[f107,f373])).
% 2.16/0.63  fof(f373,plain,(
% 2.16/0.63    ( ! [X4,X3] : (k7_subset_1(X3,X3,X4) = k5_xboole_0(X3,k3_xboole_0(X3,X4))) )),
% 2.16/0.63    inference(resolution,[],[f76,f99])).
% 2.16/0.63  fof(f76,plain,(
% 2.16/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2))) )),
% 2.16/0.63    inference(definition_unfolding,[],[f71,f64])).
% 2.16/0.63  fof(f64,plain,(
% 2.16/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.16/0.63    inference(cnf_transformation,[],[f1])).
% 2.16/0.63  fof(f1,axiom,(
% 2.16/0.63    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.16/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.16/0.63  fof(f71,plain,(
% 2.16/0.63    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.16/0.63    inference(cnf_transformation,[],[f36])).
% 2.16/0.63  fof(f36,plain,(
% 2.16/0.63    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.16/0.63    inference(ennf_transformation,[],[f8])).
% 2.16/0.63  fof(f8,axiom,(
% 2.16/0.63    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 2.16/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.16/0.63  fof(f107,plain,(
% 2.16/0.63    ( ! [X2,X0,X3,X1] : (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1) | r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X3)),X2)) )),
% 2.16/0.63    inference(resolution,[],[f96,f72])).
% 2.16/0.63  fof(f72,plain,(
% 2.16/0.63    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 2.16/0.63    inference(cnf_transformation,[],[f38])).
% 2.16/0.63  fof(f38,plain,(
% 2.16/0.63    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.16/0.63    inference(flattening,[],[f37])).
% 2.16/0.63  fof(f37,plain,(
% 2.16/0.63    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.16/0.63    inference(ennf_transformation,[],[f2])).
% 2.16/0.63  fof(f2,axiom,(
% 2.16/0.63    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.16/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 2.16/0.63  fof(f96,plain,(
% 2.16/0.63    ( ! [X4,X5,X3] : (r1_tarski(k5_xboole_0(X3,k3_xboole_0(X3,X5)),X4) | ~r1_tarski(X3,X4)) )),
% 2.16/0.63    inference(resolution,[],[f72,f75])).
% 2.16/0.63  fof(f75,plain,(
% 2.16/0.63    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 2.16/0.63    inference(definition_unfolding,[],[f63,f64])).
% 2.16/0.63  fof(f63,plain,(
% 2.16/0.63    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.16/0.63    inference(cnf_transformation,[],[f3])).
% 2.16/0.63  fof(f3,axiom,(
% 2.16/0.63    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.16/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.16/0.63  fof(f2823,plain,(
% 2.16/0.63    k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k7_subset_1(sK1,sK1,k2_tops_1(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))) | ~spl2_48),
% 2.16/0.63    inference(forward_demodulation,[],[f2814,f1678])).
% 2.16/0.63  fof(f1678,plain,(
% 2.16/0.63    k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k4_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1),k2_tops_1(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))),
% 2.16/0.63    inference(resolution,[],[f1662,f134])).
% 2.16/0.63  fof(f134,plain,(
% 2.16/0.63    r1_tarski(k3_subset_1(k2_struct_0(sK0),sK1),k2_struct_0(sK0))),
% 2.16/0.63    inference(resolution,[],[f131,f101])).
% 2.16/0.63  fof(f131,plain,(
% 2.16/0.63    ( ! [X10] : (~r1_tarski(k2_struct_0(sK0),X10) | r1_tarski(k3_subset_1(k2_struct_0(sK0),sK1),X10)) )),
% 2.16/0.63    inference(resolution,[],[f105,f90])).
% 2.16/0.63  fof(f105,plain,(
% 2.16/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X1,X2) | r1_tarski(k3_subset_1(X1,X0),X2)) )),
% 2.16/0.63    inference(resolution,[],[f97,f72])).
% 2.16/0.63  fof(f97,plain,(
% 2.16/0.63    ( ! [X0,X1] : (r1_tarski(k3_subset_1(X1,X0),X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.16/0.63    inference(resolution,[],[f65,f69])).
% 2.16/0.63  fof(f1662,plain,(
% 2.16/0.63    ( ! [X0] : (~r1_tarski(X0,k2_struct_0(sK0)) | k2_pre_topc(sK0,X0) = k4_subset_1(k2_struct_0(sK0),X0,k2_tops_1(sK0,X0))) )),
% 2.16/0.63    inference(resolution,[],[f1661,f70])).
% 2.16/0.63  fof(f1661,plain,(
% 2.16/0.63    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k4_subset_1(k2_struct_0(sK0),X0,k2_tops_1(sK0,X0))) )),
% 2.16/0.63    inference(forward_demodulation,[],[f1660,f89])).
% 2.16/0.63  fof(f1660,plain,(
% 2.16/0.63    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0))) )),
% 2.16/0.63    inference(forward_demodulation,[],[f1659,f89])).
% 2.16/0.63  fof(f1659,plain,(
% 2.16/0.63    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0))) )),
% 2.16/0.63    inference(resolution,[],[f57,f47])).
% 2.16/0.63  fof(f57,plain,(
% 2.16/0.63    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 2.16/0.63    inference(cnf_transformation,[],[f27])).
% 2.16/0.63  fof(f27,plain,(
% 2.16/0.63    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.16/0.63    inference(ennf_transformation,[],[f20])).
% 2.16/0.63  fof(f20,axiom,(
% 2.16/0.63    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.16/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 2.16/0.63  fof(f2814,plain,(
% 2.16/0.63    k4_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1),k2_tops_1(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) = k3_subset_1(k2_struct_0(sK0),k7_subset_1(sK1,sK1,k2_tops_1(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))) | ~spl2_48),
% 2.16/0.63    inference(resolution,[],[f2672,f2234])).
% 2.16/0.63  fof(f2234,plain,(
% 2.16/0.63    r1_tarski(k2_tops_1(sK0,k3_subset_1(k2_struct_0(sK0),sK1)),k2_struct_0(sK0)) | ~spl2_48),
% 2.16/0.63    inference(avatar_component_clause,[],[f2232])).
% 2.16/0.63  fof(f2672,plain,(
% 2.16/0.63    ( ! [X0] : (~r1_tarski(X0,k2_struct_0(sK0)) | k3_subset_1(k2_struct_0(sK0),k7_subset_1(sK1,sK1,X0)) = k4_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1),X0)) )),
% 2.16/0.63    inference(resolution,[],[f2296,f70])).
% 2.16/0.63  fof(f2296,plain,(
% 2.16/0.63    ( ! [X20] : (~m1_subset_1(X20,k1_zfmisc_1(k2_struct_0(sK0))) | k4_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1),X20) = k3_subset_1(k2_struct_0(sK0),k7_subset_1(sK1,sK1,X20))) )),
% 2.16/0.63    inference(forward_demodulation,[],[f2288,f514])).
% 2.16/0.63  fof(f514,plain,(
% 2.16/0.63    ( ! [X16] : (k7_subset_1(k2_struct_0(sK0),sK1,X16) = k7_subset_1(sK1,sK1,X16)) )),
% 2.16/0.63    inference(backward_demodulation,[],[f381,f373])).
% 2.16/0.63  fof(f381,plain,(
% 2.16/0.63    ( ! [X16] : (k7_subset_1(k2_struct_0(sK0),sK1,X16) = k5_xboole_0(sK1,k3_xboole_0(sK1,X16))) )),
% 2.16/0.63    inference(resolution,[],[f76,f90])).
% 2.16/0.63  fof(f2288,plain,(
% 2.16/0.63    ( ! [X20] : (~m1_subset_1(X20,k1_zfmisc_1(k2_struct_0(sK0))) | k3_subset_1(k2_struct_0(sK0),k7_subset_1(k2_struct_0(sK0),sK1,X20)) = k4_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1),X20)) )),
% 2.16/0.63    inference(resolution,[],[f67,f90])).
% 2.16/0.63  fof(f67,plain,(
% 2.16/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)) )),
% 2.16/0.63    inference(cnf_transformation,[],[f33])).
% 2.16/0.63  fof(f33,plain,(
% 2.16/0.63    ! [X0,X1] : (! [X2] : (k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.16/0.63    inference(ennf_transformation,[],[f10])).
% 2.16/0.63  fof(f10,axiom,(
% 2.16/0.63    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)))),
% 2.16/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_subset_1)).
% 2.16/0.63  fof(f60,plain,(
% 2.16/0.63    ( ! [X0,X1] : (k2_struct_0(X0) != k2_pre_topc(X0,X1) | v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.16/0.63    inference(cnf_transformation,[],[f44])).
% 2.16/0.63  fof(f2729,plain,(
% 2.16/0.63    spl2_54),
% 2.16/0.63    inference(avatar_contradiction_clause,[],[f2728])).
% 2.16/0.63  fof(f2728,plain,(
% 2.16/0.63    $false | spl2_54),
% 2.16/0.63    inference(resolution,[],[f2714,f47])).
% 2.16/0.63  fof(f2714,plain,(
% 2.16/0.63    ~l1_pre_topc(sK0) | spl2_54),
% 2.16/0.63    inference(avatar_component_clause,[],[f2712])).
% 2.16/0.63  fof(f2235,plain,(
% 2.16/0.63    ~spl2_31 | spl2_48),
% 2.16/0.63    inference(avatar_split_clause,[],[f2223,f2232,f1445])).
% 2.16/0.63  fof(f1445,plain,(
% 2.16/0.63    spl2_31 <=> r1_tarski(k3_subset_1(k2_struct_0(sK0),sK1),k2_struct_0(sK0))),
% 2.16/0.63    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).
% 2.16/0.63  fof(f2223,plain,(
% 2.16/0.63    r1_tarski(k2_tops_1(sK0,k3_subset_1(k2_struct_0(sK0),sK1)),k2_struct_0(sK0)) | ~r1_tarski(k3_subset_1(k2_struct_0(sK0),sK1),k2_struct_0(sK0))),
% 2.16/0.63    inference(superposition,[],[f2182,f314])).
% 2.16/0.63  fof(f314,plain,(
% 2.16/0.63    k2_tops_1(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_tops_1(sK0,k3_subset_1(k2_struct_0(sK0),sK1))))),
% 2.16/0.63    inference(resolution,[],[f212,f134])).
% 2.16/0.63  fof(f212,plain,(
% 2.16/0.63    ( ! [X0] : (~r1_tarski(X0,k2_struct_0(sK0)) | k2_tops_1(sK0,X0) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_tops_1(sK0,X0)))) )),
% 2.16/0.63    inference(resolution,[],[f202,f70])).
% 2.16/0.63  fof(f202,plain,(
% 2.16/0.63    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0))) | k2_tops_1(sK0,X2) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_tops_1(sK0,X2)))) )),
% 2.16/0.63    inference(resolution,[],[f200,f66])).
% 2.16/0.63  fof(f200,plain,(
% 2.16/0.63    ( ! [X0] : (m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 2.16/0.63    inference(forward_demodulation,[],[f199,f89])).
% 2.16/0.63  fof(f199,plain,(
% 2.16/0.63    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.16/0.63    inference(forward_demodulation,[],[f198,f89])).
% 2.16/0.63  fof(f198,plain,(
% 2.16/0.63    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.16/0.63    inference(resolution,[],[f68,f47])).
% 2.16/0.63  fof(f68,plain,(
% 2.16/0.63    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 2.16/0.63    inference(cnf_transformation,[],[f35])).
% 2.16/0.63  fof(f35,plain,(
% 2.16/0.63    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.16/0.63    inference(flattening,[],[f34])).
% 2.16/0.63  fof(f34,plain,(
% 2.16/0.63    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.16/0.63    inference(ennf_transformation,[],[f19])).
% 2.16/0.63  fof(f19,axiom,(
% 2.16/0.63    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.16/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 2.16/0.63  fof(f2182,plain,(
% 2.16/0.63    ( ! [X0] : (r1_tarski(k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_tops_1(sK0,X0))),k2_struct_0(sK0)) | ~r1_tarski(X0,k2_struct_0(sK0))) )),
% 2.16/0.63    inference(resolution,[],[f2181,f70])).
% 2.16/0.63  fof(f2181,plain,(
% 2.16/0.63    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | r1_tarski(k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_tops_1(sK0,X0))),k2_struct_0(sK0))) )),
% 2.16/0.63    inference(resolution,[],[f1824,f101])).
% 2.16/0.63  fof(f1824,plain,(
% 2.16/0.63    ( ! [X15,X16] : (~r1_tarski(k2_struct_0(sK0),X16) | r1_tarski(k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_tops_1(sK0,X15))),X16) | ~m1_subset_1(X15,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 2.16/0.63    inference(resolution,[],[f130,f200])).
% 2.16/0.63  fof(f130,plain,(
% 2.16/0.63    ( ! [X8,X7,X9] : (~m1_subset_1(X9,k1_zfmisc_1(X7)) | r1_tarski(k3_subset_1(X7,k3_subset_1(X7,X9)),X8) | ~r1_tarski(X7,X8)) )),
% 2.16/0.63    inference(resolution,[],[f105,f65])).
% 2.16/0.63  fof(f1460,plain,(
% 2.16/0.63    spl2_31),
% 2.16/0.63    inference(avatar_contradiction_clause,[],[f1457])).
% 2.16/0.63  fof(f1457,plain,(
% 2.16/0.63    $false | spl2_31),
% 2.16/0.63    inference(resolution,[],[f1447,f134])).
% 2.16/0.63  fof(f1447,plain,(
% 2.16/0.63    ~r1_tarski(k3_subset_1(k2_struct_0(sK0),sK1),k2_struct_0(sK0)) | spl2_31),
% 2.16/0.63    inference(avatar_component_clause,[],[f1445])).
% 2.16/0.63  fof(f1367,plain,(
% 2.16/0.63    spl2_1 | ~spl2_18),
% 2.16/0.63    inference(avatar_split_clause,[],[f1338,f1364,f79])).
% 2.16/0.63  fof(f1338,plain,(
% 2.16/0.63    ~v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | v2_tops_1(sK1,sK0)),
% 2.16/0.63    inference(resolution,[],[f1325,f90])).
% 2.16/0.63  fof(f1325,plain,(
% 2.16/0.63    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) | v2_tops_1(X0,sK0)) )),
% 2.16/0.63    inference(forward_demodulation,[],[f1324,f89])).
% 2.16/0.63  fof(f1324,plain,(
% 2.16/0.63    ( ! [X0] : (~v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_1(X0,sK0)) )),
% 2.16/0.63    inference(forward_demodulation,[],[f1323,f89])).
% 2.16/0.63  fof(f1323,plain,(
% 2.16/0.63    ( ! [X0] : (~v1_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_1(X0,sK0)) )),
% 2.16/0.63    inference(resolution,[],[f62,f47])).
% 2.16/0.63  fof(f62,plain,(
% 2.16/0.63    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tops_1(X1,X0)) )),
% 2.16/0.63    inference(cnf_transformation,[],[f45])).
% 2.16/0.63  fof(f86,plain,(
% 2.16/0.63    spl2_1 | spl2_2),
% 2.16/0.63    inference(avatar_split_clause,[],[f49,f83,f79])).
% 2.16/0.63  fof(f49,plain,(
% 2.16/0.63    k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)),
% 2.16/0.63    inference(cnf_transformation,[],[f43])).
% 2.16/0.63  % SZS output end Proof for theBenchmark
% 2.16/0.63  % (9361)------------------------------
% 2.16/0.63  % (9361)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.63  % (9361)Termination reason: Refutation
% 2.16/0.63  
% 2.16/0.63  % (9361)Memory used [KB]: 7931
% 2.16/0.63  % (9361)Time elapsed: 0.226 s
% 2.16/0.63  % (9361)------------------------------
% 2.16/0.63  % (9361)------------------------------
% 2.16/0.63  % (9358)Success in time 0.281 s
%------------------------------------------------------------------------------
