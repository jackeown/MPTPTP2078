%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1315+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:18 EST 2020

% Result     : Theorem 50.42s
% Output     : Refutation 50.42s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 285 expanded)
%              Number of leaves         :   31 ( 119 expanded)
%              Depth                    :   16
%              Number of atoms          :  500 (1256 expanded)
%              Number of equality atoms :   80 ( 202 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f62892,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3784,f3789,f3794,f3804,f3814,f3824,f3847,f4103,f5968,f9754,f10585,f10821,f62891])).

fof(f62891,plain,
    ( ~ spl99_1
    | ~ spl99_2
    | ~ spl99_3
    | spl99_5
    | ~ spl99_7
    | ~ spl99_9
    | ~ spl99_13
    | ~ spl99_30
    | ~ spl99_69
    | ~ spl99_73 ),
    inference(avatar_contradiction_clause,[],[f62890])).

fof(f62890,plain,
    ( $false
    | ~ spl99_1
    | ~ spl99_2
    | ~ spl99_3
    | spl99_5
    | ~ spl99_7
    | ~ spl99_9
    | ~ spl99_13
    | ~ spl99_30
    | ~ spl99_69
    | ~ spl99_73 ),
    inference(subsumption_resolution,[],[f62878,f3813])).

fof(f3813,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl99_7 ),
    inference(avatar_component_clause,[],[f3811])).

fof(f3811,plain,
    ( spl99_7
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl99_7])])).

fof(f62878,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl99_1
    | ~ spl99_2
    | ~ spl99_3
    | spl99_5
    | ~ spl99_7
    | ~ spl99_9
    | ~ spl99_13
    | ~ spl99_30
    | ~ spl99_69
    | ~ spl99_73 ),
    inference(unit_resulting_resolution,[],[f3783,f3788,f3793,f11829])).

fof(f11829,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(sK1,X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl99_1
    | ~ spl99_3
    | spl99_5
    | ~ spl99_7
    | ~ spl99_9
    | ~ spl99_13
    | ~ spl99_30
    | ~ spl99_69
    | ~ spl99_73 ),
    inference(subsumption_resolution,[],[f11703,f3803])).

fof(f3803,plain,
    ( ~ v4_pre_topc(sK1,sK2)
    | spl99_5 ),
    inference(avatar_component_clause,[],[f3801])).

fof(f3801,plain,
    ( spl99_5
  <=> v4_pre_topc(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl99_5])])).

fof(f11703,plain,
    ( ! [X0] :
        ( v4_pre_topc(sK1,sK2)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v4_pre_topc(sK1,X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl99_1
    | ~ spl99_3
    | ~ spl99_7
    | ~ spl99_9
    | ~ spl99_13
    | ~ spl99_30
    | ~ spl99_69
    | ~ spl99_73 ),
    inference(backward_demodulation,[],[f5956,f11702])).

fof(f11702,plain,
    ( sK1 = k2_pre_topc(sK2,sK1)
    | ~ spl99_9
    | ~ spl99_69
    | ~ spl99_73 ),
    inference(forward_demodulation,[],[f11696,f11279])).

fof(f11279,plain,
    ( sK1 = k3_xboole_0(u1_struct_0(sK2),sK1)
    | ~ spl99_9
    | ~ spl99_73 ),
    inference(forward_demodulation,[],[f11278,f4908])).

fof(f4908,plain,
    ( sK1 = k3_subset_1(u1_struct_0(sK2),k4_xboole_0(u1_struct_0(sK2),sK1))
    | ~ spl99_9 ),
    inference(backward_demodulation,[],[f4893,f4898])).

fof(f4898,plain,
    ( k3_subset_1(u1_struct_0(sK2),sK1) = k4_xboole_0(u1_struct_0(sK2),sK1)
    | ~ spl99_9 ),
    inference(unit_resulting_resolution,[],[f3823,f3242])).

fof(f3242,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f2522])).

fof(f2522,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f462])).

fof(f462,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f3823,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl99_9 ),
    inference(avatar_component_clause,[],[f3821])).

fof(f3821,plain,
    ( spl99_9
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl99_9])])).

fof(f4893,plain,
    ( sK1 = k3_subset_1(u1_struct_0(sK2),k3_subset_1(u1_struct_0(sK2),sK1))
    | ~ spl99_9 ),
    inference(unit_resulting_resolution,[],[f3823,f3241])).

fof(f3241,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f2521])).

fof(f2521,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f487])).

fof(f487,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f11278,plain,
    ( k3_xboole_0(u1_struct_0(sK2),sK1) = k3_subset_1(u1_struct_0(sK2),k4_xboole_0(u1_struct_0(sK2),sK1))
    | ~ spl99_73 ),
    inference(forward_demodulation,[],[f11193,f3588])).

fof(f3588,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f11193,plain,
    ( k3_subset_1(u1_struct_0(sK2),k4_xboole_0(u1_struct_0(sK2),sK1)) = k4_xboole_0(u1_struct_0(sK2),k4_xboole_0(u1_struct_0(sK2),sK1))
    | ~ spl99_73 ),
    inference(unit_resulting_resolution,[],[f10820,f3242])).

fof(f10820,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK2),sK1),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl99_73 ),
    inference(avatar_component_clause,[],[f10818])).

fof(f10818,plain,
    ( spl99_73
  <=> m1_subset_1(k4_xboole_0(u1_struct_0(sK2),sK1),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl99_73])])).

fof(f11696,plain,
    ( k2_pre_topc(sK2,sK1) = k3_xboole_0(u1_struct_0(sK2),sK1)
    | ~ spl99_9
    | ~ spl99_69 ),
    inference(superposition,[],[f5650,f10584])).

fof(f10584,plain,
    ( k2_pre_topc(sK2,sK1) = k9_subset_1(u1_struct_0(sK2),sK1,u1_struct_0(sK2))
    | ~ spl99_69 ),
    inference(avatar_component_clause,[],[f10582])).

fof(f10582,plain,
    ( spl99_69
  <=> k2_pre_topc(sK2,sK1) = k9_subset_1(u1_struct_0(sK2),sK1,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl99_69])])).

fof(f5650,plain,
    ( ! [X0] : k3_xboole_0(X0,sK1) = k9_subset_1(u1_struct_0(sK2),sK1,X0)
    | ~ spl99_9 ),
    inference(forward_demodulation,[],[f5643,f4979])).

fof(f4979,plain,
    ( ! [X0] : k3_xboole_0(X0,sK1) = k9_subset_1(u1_struct_0(sK2),X0,sK1)
    | ~ spl99_9 ),
    inference(unit_resulting_resolution,[],[f3823,f3295])).

fof(f3295,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f2558])).

fof(f2558,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f496])).

fof(f496,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f5643,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK2),X0,sK1) = k9_subset_1(u1_struct_0(sK2),sK1,X0)
    | ~ spl99_9 ),
    inference(unit_resulting_resolution,[],[f3823,f3294])).

fof(f3294,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f2557])).

fof(f2557,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f454])).

fof(f454,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f5956,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v4_pre_topc(sK1,X0)
        | v4_pre_topc(k2_pre_topc(sK2,sK1),sK2)
        | ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl99_1
    | ~ spl99_3
    | ~ spl99_7
    | ~ spl99_9
    | ~ spl99_13
    | ~ spl99_30 ),
    inference(forward_demodulation,[],[f5955,f5949])).

fof(f5949,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl99_1
    | ~ spl99_3
    | ~ spl99_7 ),
    inference(unit_resulting_resolution,[],[f3783,f3793,f3813,f3350])).

fof(f3350,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f2608])).

fof(f2608,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2607])).

fof(f2607,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1843])).

fof(f1843,axiom,(
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

fof(f5955,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(sK1,X0)
        | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(X0)))
        | v4_pre_topc(k2_pre_topc(sK2,sK1),sK2)
        | ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl99_1
    | ~ spl99_3
    | ~ spl99_7
    | ~ spl99_9
    | ~ spl99_13
    | ~ spl99_30 ),
    inference(subsumption_resolution,[],[f5951,f5849])).

fof(f5849,plain,
    ( m1_subset_1(k2_pre_topc(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl99_9
    | ~ spl99_13 ),
    inference(unit_resulting_resolution,[],[f3846,f3823,f3319])).

fof(f3319,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2592])).

fof(f2592,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2591])).

fof(f2591,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1780])).

fof(f1780,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f3846,plain,
    ( l1_pre_topc(sK2)
    | ~ spl99_13 ),
    inference(avatar_component_clause,[],[f3844])).

fof(f3844,plain,
    ( spl99_13
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl99_13])])).

fof(f5951,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(sK1,X0)
        | ~ m1_subset_1(k2_pre_topc(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(X0)))
        | v4_pre_topc(k2_pre_topc(sK2,sK1),sK2)
        | ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl99_1
    | ~ spl99_3
    | ~ spl99_7
    | ~ spl99_30 ),
    inference(backward_demodulation,[],[f4104,f5949])).

fof(f4104,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_pre_topc(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ v4_pre_topc(k2_pre_topc(sK0,sK1),X0)
        | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(X0)))
        | v4_pre_topc(k2_pre_topc(sK2,sK1),sK2)
        | ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl99_30 ),
    inference(superposition,[],[f3651,f4102])).

fof(f4102,plain,
    ( k2_pre_topc(sK2,sK1) = k9_subset_1(u1_struct_0(sK2),k2_pre_topc(sK0,sK1),k2_struct_0(sK2))
    | ~ spl99_30 ),
    inference(avatar_component_clause,[],[f4100])).

fof(f4100,plain,
    ( spl99_30
  <=> k2_pre_topc(sK2,sK1) = k9_subset_1(u1_struct_0(sK2),k2_pre_topc(sK0,sK1),k2_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl99_30])])).

fof(f3651,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f3082])).

fof(f3082,plain,(
    ! [X2,X0,X3,X1] :
      ( v4_pre_topc(X2,X1)
      | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2837])).

fof(f2837,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v4_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ( k9_subset_1(u1_struct_0(X1),sK12(X0,X1,X2),k2_struct_0(X1)) = X2
                    & v4_pre_topc(sK12(X0,X1,X2),X0)
                    & m1_subset_1(sK12(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v4_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f2835,f2836])).

fof(f2836,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
          & v4_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X1),sK12(X0,X1,X2),k2_struct_0(X1)) = X2
        & v4_pre_topc(sK12(X0,X1,X2),X0)
        & m1_subset_1(sK12(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f2835,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v4_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X4] :
                      ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
                      & v4_pre_topc(X4,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v4_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f2834])).

fof(f2834,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v4_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                      & v4_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v4_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f2420])).

fof(f2420,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v4_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1834])).

fof(f1834,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ( v4_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_pre_topc)).

fof(f3793,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl99_3 ),
    inference(avatar_component_clause,[],[f3791])).

fof(f3791,plain,
    ( spl99_3
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl99_3])])).

fof(f3788,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl99_2 ),
    inference(avatar_component_clause,[],[f3786])).

fof(f3786,plain,
    ( spl99_2
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl99_2])])).

fof(f3783,plain,
    ( l1_pre_topc(sK0)
    | ~ spl99_1 ),
    inference(avatar_component_clause,[],[f3781])).

fof(f3781,plain,
    ( spl99_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl99_1])])).

fof(f10821,plain,
    ( spl99_73
    | ~ spl99_9 ),
    inference(avatar_split_clause,[],[f4909,f3821,f10818])).

fof(f4909,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK2),sK1),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl99_9 ),
    inference(backward_demodulation,[],[f4529,f4898])).

fof(f4529,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK2),sK1),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl99_9 ),
    inference(unit_resulting_resolution,[],[f3823,f3243])).

fof(f3243,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f2523])).

fof(f2523,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f466])).

fof(f466,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f10585,plain,
    ( spl99_69
    | ~ spl99_44
    | ~ spl99_64 ),
    inference(avatar_split_clause,[],[f10532,f9751,f5965,f10582])).

fof(f5965,plain,
    ( spl99_44
  <=> k2_pre_topc(sK2,sK1) = k9_subset_1(u1_struct_0(sK2),sK1,k2_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl99_44])])).

fof(f9751,plain,
    ( spl99_64
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl99_64])])).

fof(f10532,plain,
    ( k2_pre_topc(sK2,sK1) = k9_subset_1(u1_struct_0(sK2),sK1,u1_struct_0(sK2))
    | ~ spl99_44
    | ~ spl99_64 ),
    inference(backward_demodulation,[],[f5967,f10529])).

fof(f10529,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2)
    | ~ spl99_64 ),
    inference(unit_resulting_resolution,[],[f9753,f3316])).

fof(f3316,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2587])).

fof(f2587,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1773])).

fof(f1773,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f9753,plain,
    ( l1_struct_0(sK2)
    | ~ spl99_64 ),
    inference(avatar_component_clause,[],[f9751])).

fof(f5967,plain,
    ( k2_pre_topc(sK2,sK1) = k9_subset_1(u1_struct_0(sK2),sK1,k2_struct_0(sK2))
    | ~ spl99_44 ),
    inference(avatar_component_clause,[],[f5965])).

fof(f9754,plain,
    ( spl99_64
    | ~ spl99_13 ),
    inference(avatar_split_clause,[],[f9528,f3844,f9751])).

fof(f9528,plain,
    ( l1_struct_0(sK2)
    | ~ spl99_13 ),
    inference(unit_resulting_resolution,[],[f3846,f3607])).

fof(f3607,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2754])).

fof(f2754,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1782])).

fof(f1782,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f5968,plain,
    ( spl99_44
    | ~ spl99_1
    | ~ spl99_3
    | ~ spl99_7
    | ~ spl99_30 ),
    inference(avatar_split_clause,[],[f5950,f4100,f3811,f3791,f3781,f5965])).

fof(f5950,plain,
    ( k2_pre_topc(sK2,sK1) = k9_subset_1(u1_struct_0(sK2),sK1,k2_struct_0(sK2))
    | ~ spl99_1
    | ~ spl99_3
    | ~ spl99_7
    | ~ spl99_30 ),
    inference(backward_demodulation,[],[f4102,f5949])).

fof(f4103,plain,
    ( spl99_30
    | ~ spl99_1
    | ~ spl99_2
    | ~ spl99_7
    | ~ spl99_9 ),
    inference(avatar_split_clause,[],[f3892,f3821,f3811,f3786,f3781,f4100])).

fof(f3892,plain,
    ( k2_pre_topc(sK2,sK1) = k9_subset_1(u1_struct_0(sK2),k2_pre_topc(sK0,sK1),k2_struct_0(sK2))
    | ~ spl99_1
    | ~ spl99_2
    | ~ spl99_7
    | ~ spl99_9 ),
    inference(unit_resulting_resolution,[],[f3783,f3788,f3813,f3823,f3649])).

fof(f3649,plain,(
    ! [X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | k2_pre_topc(X1,X3) = k9_subset_1(u1_struct_0(X1),k2_pre_topc(X0,X3),k2_struct_0(X1)) ) ),
    inference(equality_resolution,[],[f3074])).

fof(f3074,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_pre_topc(X1,X3) = k9_subset_1(u1_struct_0(X1),k2_pre_topc(X0,X2),k2_struct_0(X1))
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2418])).

fof(f2418,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_pre_topc(X1,X3) = k9_subset_1(u1_struct_0(X1),k2_pre_topc(X0,X2),k2_struct_0(X1))
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2417])).

fof(f2417,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_pre_topc(X1,X3) = k9_subset_1(u1_struct_0(X1),k2_pre_topc(X0,X2),k2_struct_0(X1))
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1838])).

fof(f1838,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( X2 = X3
                   => k2_pre_topc(X1,X3) = k9_subset_1(u1_struct_0(X1),k2_pre_topc(X0,X2),k2_struct_0(X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_pre_topc)).

fof(f3847,plain,
    ( spl99_13
    | ~ spl99_1
    | ~ spl99_2 ),
    inference(avatar_split_clause,[],[f3842,f3786,f3781,f3844])).

fof(f3842,plain,
    ( l1_pre_topc(sK2)
    | ~ spl99_1
    | ~ spl99_2 ),
    inference(unit_resulting_resolution,[],[f3788,f3783,f3084])).

fof(f3084,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f2422])).

fof(f2422,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1784])).

fof(f1784,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f3824,plain,(
    spl99_9 ),
    inference(avatar_split_clause,[],[f3743,f3821])).

fof(f3743,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(forward_demodulation,[],[f3039,f3040])).

fof(f3040,plain,(
    sK1 = sK3 ),
    inference(cnf_transformation,[],[f2812])).

fof(f2812,plain,
    ( ~ v4_pre_topc(sK3,sK2)
    & sK1 = sK3
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & v4_pre_topc(sK1,sK0)
    & m1_pre_topc(sK2,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f2386,f2811,f2810,f2809,f2808])).

fof(f2808,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ v4_pre_topc(X3,X2)
                    & X1 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
                & v4_pre_topc(X1,X0)
                & m1_pre_topc(X2,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v4_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v4_pre_topc(X1,sK0)
              & m1_pre_topc(X2,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f2809,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ v4_pre_topc(X3,X2)
                & X1 = X3
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
            & v4_pre_topc(X1,sK0)
            & m1_pre_topc(X2,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ v4_pre_topc(X3,X2)
              & sK1 = X3
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
          & v4_pre_topc(sK1,sK0)
          & m1_pre_topc(X2,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f2810,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ v4_pre_topc(X3,X2)
            & sK1 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
        & v4_pre_topc(sK1,sK0)
        & m1_pre_topc(X2,sK0) )
   => ( ? [X3] :
          ( ~ v4_pre_topc(X3,sK2)
          & sK1 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
      & v4_pre_topc(sK1,sK0)
      & m1_pre_topc(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f2811,plain,
    ( ? [X3] :
        ( ~ v4_pre_topc(X3,sK2)
        & sK1 = X3
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( ~ v4_pre_topc(sK3,sK2)
      & sK1 = sK3
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f2386,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v4_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v4_pre_topc(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2385])).

fof(f2385,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v4_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v4_pre_topc(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2369])).

fof(f2369,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ( v4_pre_topc(X1,X0)
                 => ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                     => ( X1 = X3
                       => v4_pre_topc(X3,X2) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f2368])).

fof(f2368,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v4_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v4_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tops_2)).

fof(f3039,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f2812])).

fof(f3814,plain,(
    spl99_7 ),
    inference(avatar_split_clause,[],[f3036,f3811])).

fof(f3036,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f2812])).

fof(f3804,plain,(
    ~ spl99_5 ),
    inference(avatar_split_clause,[],[f3742,f3801])).

fof(f3742,plain,(
    ~ v4_pre_topc(sK1,sK2) ),
    inference(backward_demodulation,[],[f3041,f3040])).

fof(f3041,plain,(
    ~ v4_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f2812])).

fof(f3794,plain,(
    spl99_3 ),
    inference(avatar_split_clause,[],[f3038,f3791])).

fof(f3038,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f2812])).

fof(f3789,plain,(
    spl99_2 ),
    inference(avatar_split_clause,[],[f3037,f3786])).

fof(f3037,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f2812])).

fof(f3784,plain,(
    spl99_1 ),
    inference(avatar_split_clause,[],[f3035,f3781])).

fof(f3035,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f2812])).
%------------------------------------------------------------------------------
