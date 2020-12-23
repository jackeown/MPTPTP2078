%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:23 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 574 expanded)
%              Number of leaves         :   28 ( 180 expanded)
%              Depth                    :   17
%              Number of atoms          :  395 (2064 expanded)
%              Number of equality atoms :   89 ( 600 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2672,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f71,f72,f201,f203,f513,f1421,f1952,f1959,f1963,f2303,f2638,f2645,f2670,f2671])).

fof(f2671,plain,
    ( ~ spl2_1
    | ~ spl2_44
    | spl2_96
    | ~ spl2_57 ),
    inference(avatar_split_clause,[],[f1435,f1419,f1949,f1022,f64])).

fof(f64,plain,
    ( spl2_1
  <=> v2_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f1022,plain,
    ( spl2_44
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).

fof(f1949,plain,
    ( spl2_96
  <=> v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_96])])).

fof(f1419,plain,
    ( spl2_57
  <=> ! [X0] :
        ( v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v2_tops_1(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_57])])).

fof(f1435,plain,
    ( v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ v2_tops_1(sK1,sK0)
    | ~ spl2_57 ),
    inference(superposition,[],[f1420,f142])).

fof(f142,plain,(
    k4_xboole_0(k2_struct_0(sK0),sK1) = k3_subset_1(k2_struct_0(sK0),sK1) ),
    inference(resolution,[],[f58,f78])).

fof(f78,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f40,f77])).

fof(f77,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f75,f39])).

fof(f39,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( k1_xboole_0 != k1_tops_1(sK0,sK1)
      | ~ v2_tops_1(sK1,sK0) )
    & ( k1_xboole_0 = k1_tops_1(sK0,sK1)
      | v2_tops_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f34,f33])).

fof(f33,plain,
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

fof(f34,plain,
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

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(X0,X1)
            | ~ v2_tops_1(X1,X0) )
          & ( k1_xboole_0 = k1_tops_1(X0,X1)
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(X0,X1)
            | ~ v2_tops_1(X1,X0) )
          & ( k1_xboole_0 = k1_tops_1(X0,X1)
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> k1_xboole_0 = k1_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

fof(f75,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(resolution,[],[f46,f47])).

fof(f47,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f46,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f40,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f35])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f1420,plain,
    ( ! [X0] :
        ( v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v2_tops_1(X0,sK0) )
    | ~ spl2_57 ),
    inference(avatar_component_clause,[],[f1419])).

fof(f2670,plain,
    ( spl2_2
    | ~ spl2_5
    | ~ spl2_96
    | ~ spl2_115 ),
    inference(avatar_contradiction_clause,[],[f2669])).

fof(f2669,plain,
    ( $false
    | spl2_2
    | ~ spl2_5
    | ~ spl2_96
    | ~ spl2_115 ),
    inference(subsumption_resolution,[],[f70,f2668])).

fof(f2668,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl2_5
    | ~ spl2_96
    | ~ spl2_115 ),
    inference(forward_demodulation,[],[f2666,f180])).

fof(f180,plain,(
    ! [X2] : k1_xboole_0 = k3_subset_1(X2,X2) ),
    inference(forward_demodulation,[],[f176,f74])).

fof(f74,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f73,f44])).

fof(f44,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f73,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f45,f43])).

fof(f43,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(f45,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

fof(f176,plain,(
    ! [X2] : k1_xboole_0 = k3_subset_1(X2,k3_subset_1(X2,k1_xboole_0)) ),
    inference(resolution,[],[f172,f76])).

fof(f76,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(superposition,[],[f53,f55])).

fof(f55,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f53,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f172,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(resolution,[],[f59,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f2666,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ spl2_5
    | ~ spl2_96
    | ~ spl2_115 ),
    inference(backward_demodulation,[],[f2377,f2664])).

fof(f2664,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))
    | ~ spl2_5
    | ~ spl2_96 ),
    inference(resolution,[],[f1950,f557])).

fof(f557,plain,
    ( ! [X0] :
        ( ~ v1_tops_1(k4_xboole_0(k2_struct_0(sK0),X0),sK0)
        | k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),X0)) )
    | ~ spl2_5 ),
    inference(resolution,[],[f541,f53])).

fof(f541,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k2_struct_0(sK0))
        | ~ v1_tops_1(X0,sK0)
        | k2_struct_0(sK0) = k2_pre_topc(sK0,X0) )
    | ~ spl2_5 ),
    inference(resolution,[],[f512,f62])).

fof(f512,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | k2_struct_0(sK0) = k2_pre_topc(sK0,X0)
        | ~ v1_tops_1(X0,sK0) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f511])).

fof(f511,plain,
    ( spl2_5
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | k2_struct_0(sK0) = k2_pre_topc(sK0,X0)
        | ~ v1_tops_1(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f1950,plain,
    ( v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ spl2_96 ),
    inference(avatar_component_clause,[],[f1949])).

fof(f2377,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)))
    | ~ spl2_115 ),
    inference(forward_demodulation,[],[f2323,f142])).

fof(f2323,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))
    | ~ spl2_115 ),
    inference(resolution,[],[f2302,f78])).

fof(f2302,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | k1_tops_1(sK0,X0) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) )
    | ~ spl2_115 ),
    inference(avatar_component_clause,[],[f2301])).

fof(f2301,plain,
    ( spl2_115
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | k1_tops_1(sK0,X0) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_115])])).

fof(f70,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl2_2
  <=> k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f2645,plain,(
    spl2_44 ),
    inference(avatar_contradiction_clause,[],[f2644])).

fof(f2644,plain,
    ( $false
    | spl2_44 ),
    inference(subsumption_resolution,[],[f78,f1024])).

fof(f1024,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | spl2_44 ),
    inference(avatar_component_clause,[],[f1022])).

fof(f2638,plain,
    ( ~ spl2_2
    | ~ spl2_4
    | spl2_97
    | ~ spl2_115 ),
    inference(avatar_contradiction_clause,[],[f2634])).

fof(f2634,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_4
    | spl2_97
    | ~ spl2_115 ),
    inference(subsumption_resolution,[],[f1958,f2633])).

fof(f2633,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_115 ),
    inference(forward_demodulation,[],[f2604,f147])).

fof(f147,plain,(
    ! [X2] : k4_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f144,f74])).

fof(f144,plain,(
    ! [X2] : k4_xboole_0(X2,k1_xboole_0) = k3_subset_1(X2,k1_xboole_0) ),
    inference(resolution,[],[f141,f76])).

fof(f141,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(resolution,[],[f58,f62])).

fof(f2604,plain,
    ( k4_xboole_0(k2_struct_0(sK0),k1_xboole_0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_115 ),
    inference(superposition,[],[f758,f2439])).

fof(f2439,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)))
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_115 ),
    inference(superposition,[],[f2378,f442])).

fof(f442,plain,
    ( ! [X0] : k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),X0))) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),X0)))
    | ~ spl2_4 ),
    inference(resolution,[],[f395,f53])).

fof(f395,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k2_struct_0(sK0))
        | k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,X0)) = k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,X0)) )
    | ~ spl2_4 ),
    inference(resolution,[],[f220,f62])).

fof(f220,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,X1)) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,X1)) )
    | ~ spl2_4 ),
    inference(resolution,[],[f200,f58])).

fof(f200,plain,
    ( ! [X0] :
        ( m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl2_4
  <=> ! [X0] :
        ( m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f2378,plain,
    ( k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)))
    | ~ spl2_2
    | ~ spl2_115 ),
    inference(forward_demodulation,[],[f2377,f69])).

fof(f69,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f758,plain,
    ( ! [X1] : k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),X1)) = k4_xboole_0(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),X1))))
    | ~ spl2_4 ),
    inference(superposition,[],[f447,f143])).

fof(f143,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_subset_1(X0,k4_xboole_0(X0,X1)) ),
    inference(resolution,[],[f141,f53])).

fof(f447,plain,
    ( ! [X0] : k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),X0)) = k3_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),X0))))
    | ~ spl2_4 ),
    inference(backward_demodulation,[],[f391,f442])).

fof(f391,plain,
    ( ! [X0] : k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),X0)) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),X0))))
    | ~ spl2_4 ),
    inference(resolution,[],[f387,f53])).

fof(f387,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k2_struct_0(sK0))
        | k2_pre_topc(sK0,X0) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,X0))) )
    | ~ spl2_4 ),
    inference(resolution,[],[f219,f62])).

fof(f219,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,X0))) )
    | ~ spl2_4 ),
    inference(resolution,[],[f200,f59])).

fof(f1958,plain,
    ( k2_struct_0(sK0) != k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))
    | spl2_97 ),
    inference(avatar_component_clause,[],[f1956])).

fof(f1956,plain,
    ( spl2_97
  <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_97])])).

fof(f2303,plain,
    ( ~ spl2_3
    | spl2_115 ),
    inference(avatar_split_clause,[],[f2298,f2301,f195])).

fof(f195,plain,
    ( spl2_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f2298,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k1_tops_1(sK0,X0) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f48,f77])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

fof(f1963,plain,(
    spl2_59 ),
    inference(avatar_contradiction_clause,[],[f1961])).

fof(f1961,plain,
    ( $false
    | spl2_59 ),
    inference(resolution,[],[f1960,f53])).

fof(f1960,plain,
    ( ~ r1_tarski(k4_xboole_0(k2_struct_0(sK0),sK1),k2_struct_0(sK0))
    | spl2_59 ),
    inference(resolution,[],[f1447,f62])).

fof(f1447,plain,
    ( ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl2_59 ),
    inference(avatar_component_clause,[],[f1445])).

fof(f1445,plain,
    ( spl2_59
  <=> m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_59])])).

fof(f1959,plain,
    ( ~ spl2_3
    | ~ spl2_97
    | ~ spl2_59
    | spl2_96 ),
    inference(avatar_split_clause,[],[f1954,f1949,f1445,f1956,f195])).

fof(f1954,plain,
    ( ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | k2_struct_0(sK0) != k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))
    | ~ l1_pre_topc(sK0)
    | spl2_96 ),
    inference(forward_demodulation,[],[f1953,f77])).

fof(f1953,plain,
    ( k2_struct_0(sK0) != k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))
    | ~ m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_96 ),
    inference(resolution,[],[f1951,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | k2_struct_0(X0) != k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

fof(f1951,plain,
    ( ~ v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | spl2_96 ),
    inference(avatar_component_clause,[],[f1949])).

fof(f1952,plain,
    ( ~ spl2_3
    | ~ spl2_96
    | ~ spl2_44
    | spl2_1 ),
    inference(avatar_split_clause,[],[f1947,f64,f1022,f1949,f195])).

fof(f1947,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | spl2_1 ),
    inference(forward_demodulation,[],[f1946,f77])).

fof(f1946,plain,
    ( ~ v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_1 ),
    inference(forward_demodulation,[],[f1945,f142])).

fof(f1945,plain,
    ( ~ v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_1 ),
    inference(forward_demodulation,[],[f1902,f77])).

fof(f1902,plain,
    ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_1 ),
    inference(resolution,[],[f52,f66])).

fof(f66,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f64])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_1)).

fof(f1421,plain,
    ( ~ spl2_3
    | spl2_57 ),
    inference(avatar_split_clause,[],[f1413,f1419,f195])).

fof(f1413,plain,(
    ! [X0] :
      ( v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0)
      | ~ v2_tops_1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f51,f77])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f513,plain,
    ( ~ spl2_3
    | spl2_5 ),
    inference(avatar_split_clause,[],[f508,f511,f195])).

fof(f508,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v1_tops_1(X0,sK0)
      | k2_struct_0(sK0) = k2_pre_topc(sK0,X0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f49,f77])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_1(X1,X0)
      | k2_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f203,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f202])).

fof(f202,plain,
    ( $false
    | spl2_3 ),
    inference(subsumption_resolution,[],[f39,f197])).

fof(f197,plain,
    ( ~ l1_pre_topc(sK0)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f195])).

fof(f201,plain,
    ( ~ spl2_3
    | spl2_4 ),
    inference(avatar_split_clause,[],[f192,f199,f195])).

fof(f192,plain,(
    ! [X0] :
      ( m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f60,f77])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f72,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f41,f68,f64])).

fof(f41,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f71,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f42,f68,f64])).

fof(f42,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:17:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (15836)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.45  % (15848)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.46  % (15845)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.46  % (15837)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.46  % (15835)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.47  % (15843)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.48  % (15840)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.49  % (15834)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.50  % (15833)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.50  % (15832)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.50  % (15838)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.50  % (15846)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.50  % (15844)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.50  % (15839)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.51  % (15848)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f2672,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f71,f72,f201,f203,f513,f1421,f1952,f1959,f1963,f2303,f2638,f2645,f2670,f2671])).
% 0.20/0.51  fof(f2671,plain,(
% 0.20/0.51    ~spl2_1 | ~spl2_44 | spl2_96 | ~spl2_57),
% 0.20/0.51    inference(avatar_split_clause,[],[f1435,f1419,f1949,f1022,f64])).
% 0.20/0.51  fof(f64,plain,(
% 0.20/0.51    spl2_1 <=> v2_tops_1(sK1,sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.51  fof(f1022,plain,(
% 0.20/0.51    spl2_44 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).
% 0.20/0.51  fof(f1949,plain,(
% 0.20/0.51    spl2_96 <=> v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_96])])).
% 0.20/0.51  fof(f1419,plain,(
% 0.20/0.51    spl2_57 <=> ! [X0] : (v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v2_tops_1(X0,sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_57])])).
% 0.20/0.51  fof(f1435,plain,(
% 0.20/0.51    v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~v2_tops_1(sK1,sK0) | ~spl2_57),
% 0.20/0.51    inference(superposition,[],[f1420,f142])).
% 0.20/0.51  fof(f142,plain,(
% 0.20/0.51    k4_xboole_0(k2_struct_0(sK0),sK1) = k3_subset_1(k2_struct_0(sK0),sK1)),
% 0.20/0.51    inference(resolution,[],[f58,f78])).
% 0.20/0.51  fof(f78,plain,(
% 0.20/0.51    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.20/0.51    inference(backward_demodulation,[],[f40,f77])).
% 0.20/0.51  fof(f77,plain,(
% 0.20/0.51    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.20/0.51    inference(resolution,[],[f75,f39])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    l1_pre_topc(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f35])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ((k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f34,f33])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((k1_xboole_0 != k1_tops_1(sK0,X1) | ~v2_tops_1(X1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,X1) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ? [X1] : ((k1_xboole_0 != k1_tops_1(sK0,X1) | ~v2_tops_1(X1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,X1) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.20/0.51    inference(flattening,[],[f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.20/0.51    inference(nnf_transformation,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> k1_xboole_0 = k1_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f19])).
% 0.20/0.51  fof(f19,negated_conjecture,(
% 0.20/0.51    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 0.20/0.51    inference(negated_conjecture,[],[f18])).
% 0.20/0.51  fof(f18,conjecture,(
% 0.20/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).
% 0.20/0.51  fof(f75,plain,(
% 0.20/0.51    ( ! [X0] : (~l1_pre_topc(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.20/0.51    inference(resolution,[],[f46,f47])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,axiom,(
% 0.20/0.51    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,axiom,(
% 0.20/0.51    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.51    inference(cnf_transformation,[],[f35])).
% 0.20/0.51  fof(f58,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.20/0.51  fof(f1420,plain,(
% 0.20/0.51    ( ! [X0] : (v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v2_tops_1(X0,sK0)) ) | ~spl2_57),
% 0.20/0.51    inference(avatar_component_clause,[],[f1419])).
% 0.20/0.51  fof(f2670,plain,(
% 0.20/0.51    spl2_2 | ~spl2_5 | ~spl2_96 | ~spl2_115),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f2669])).
% 0.20/0.51  fof(f2669,plain,(
% 0.20/0.51    $false | (spl2_2 | ~spl2_5 | ~spl2_96 | ~spl2_115)),
% 0.20/0.51    inference(subsumption_resolution,[],[f70,f2668])).
% 0.20/0.51  fof(f2668,plain,(
% 0.20/0.51    k1_xboole_0 = k1_tops_1(sK0,sK1) | (~spl2_5 | ~spl2_96 | ~spl2_115)),
% 0.20/0.51    inference(forward_demodulation,[],[f2666,f180])).
% 0.20/0.51  fof(f180,plain,(
% 0.20/0.51    ( ! [X2] : (k1_xboole_0 = k3_subset_1(X2,X2)) )),
% 0.20/0.51    inference(forward_demodulation,[],[f176,f74])).
% 0.20/0.51  fof(f74,plain,(
% 0.20/0.51    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 0.20/0.51    inference(forward_demodulation,[],[f73,f44])).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.20/0.51  fof(f73,plain,(
% 0.20/0.51    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 0.20/0.51    inference(forward_demodulation,[],[f45,f43])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,axiom,(
% 0.20/0.51    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).
% 0.20/0.51  fof(f176,plain,(
% 0.20/0.51    ( ! [X2] : (k1_xboole_0 = k3_subset_1(X2,k3_subset_1(X2,k1_xboole_0))) )),
% 0.20/0.51    inference(resolution,[],[f172,f76])).
% 0.20/0.51  fof(f76,plain,(
% 0.20/0.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.51    inference(superposition,[],[f53,f55])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.20/0.51  fof(f172,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.20/0.51    inference(resolution,[],[f59,f62])).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f38])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.51    inference(nnf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,axiom,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.51  fof(f59,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,axiom,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.20/0.51  fof(f2666,plain,(
% 0.20/0.51    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) | (~spl2_5 | ~spl2_96 | ~spl2_115)),
% 0.20/0.51    inference(backward_demodulation,[],[f2377,f2664])).
% 0.20/0.51  fof(f2664,plain,(
% 0.20/0.51    k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) | (~spl2_5 | ~spl2_96)),
% 0.20/0.51    inference(resolution,[],[f1950,f557])).
% 0.20/0.51  fof(f557,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_tops_1(k4_xboole_0(k2_struct_0(sK0),X0),sK0) | k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),X0))) ) | ~spl2_5),
% 0.20/0.51    inference(resolution,[],[f541,f53])).
% 0.20/0.51  fof(f541,plain,(
% 0.20/0.51    ( ! [X0] : (~r1_tarski(X0,k2_struct_0(sK0)) | ~v1_tops_1(X0,sK0) | k2_struct_0(sK0) = k2_pre_topc(sK0,X0)) ) | ~spl2_5),
% 0.20/0.51    inference(resolution,[],[f512,f62])).
% 0.20/0.51  fof(f512,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,X0) | ~v1_tops_1(X0,sK0)) ) | ~spl2_5),
% 0.20/0.51    inference(avatar_component_clause,[],[f511])).
% 0.20/0.51  fof(f511,plain,(
% 0.20/0.51    spl2_5 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,X0) | ~v1_tops_1(X0,sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.51  fof(f1950,plain,(
% 0.20/0.51    v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) | ~spl2_96),
% 0.20/0.51    inference(avatar_component_clause,[],[f1949])).
% 0.20/0.51  fof(f2377,plain,(
% 0.20/0.51    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) | ~spl2_115),
% 0.20/0.51    inference(forward_demodulation,[],[f2323,f142])).
% 0.20/0.51  fof(f2323,plain,(
% 0.20/0.51    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) | ~spl2_115),
% 0.20/0.51    inference(resolution,[],[f2302,f78])).
% 0.20/0.51  fof(f2302,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k1_tops_1(sK0,X0) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0)))) ) | ~spl2_115),
% 0.20/0.51    inference(avatar_component_clause,[],[f2301])).
% 0.20/0.51  fof(f2301,plain,(
% 0.20/0.51    spl2_115 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k1_tops_1(sK0,X0) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_115])])).
% 0.20/0.51  fof(f70,plain,(
% 0.20/0.51    k1_xboole_0 != k1_tops_1(sK0,sK1) | spl2_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f68])).
% 0.20/0.51  fof(f68,plain,(
% 0.20/0.51    spl2_2 <=> k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.51  fof(f2645,plain,(
% 0.20/0.51    spl2_44),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f2644])).
% 0.20/0.51  fof(f2644,plain,(
% 0.20/0.51    $false | spl2_44),
% 0.20/0.51    inference(subsumption_resolution,[],[f78,f1024])).
% 0.20/0.51  fof(f1024,plain,(
% 0.20/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | spl2_44),
% 0.20/0.51    inference(avatar_component_clause,[],[f1022])).
% 0.20/0.51  fof(f2638,plain,(
% 0.20/0.51    ~spl2_2 | ~spl2_4 | spl2_97 | ~spl2_115),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f2634])).
% 0.20/0.51  fof(f2634,plain,(
% 0.20/0.51    $false | (~spl2_2 | ~spl2_4 | spl2_97 | ~spl2_115)),
% 0.20/0.51    inference(subsumption_resolution,[],[f1958,f2633])).
% 0.20/0.51  fof(f2633,plain,(
% 0.20/0.51    k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) | (~spl2_2 | ~spl2_4 | ~spl2_115)),
% 0.20/0.51    inference(forward_demodulation,[],[f2604,f147])).
% 0.20/0.51  fof(f147,plain,(
% 0.20/0.51    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = X2) )),
% 0.20/0.51    inference(forward_demodulation,[],[f144,f74])).
% 0.20/0.51  fof(f144,plain,(
% 0.20/0.51    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = k3_subset_1(X2,k1_xboole_0)) )),
% 0.20/0.51    inference(resolution,[],[f141,f76])).
% 0.20/0.51  fof(f141,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.20/0.51    inference(resolution,[],[f58,f62])).
% 0.20/0.51  fof(f2604,plain,(
% 0.20/0.51    k4_xboole_0(k2_struct_0(sK0),k1_xboole_0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) | (~spl2_2 | ~spl2_4 | ~spl2_115)),
% 0.20/0.51    inference(superposition,[],[f758,f2439])).
% 0.20/0.51  fof(f2439,plain,(
% 0.20/0.51    k1_xboole_0 = k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) | (~spl2_2 | ~spl2_4 | ~spl2_115)),
% 0.20/0.51    inference(superposition,[],[f2378,f442])).
% 0.20/0.51  fof(f442,plain,(
% 0.20/0.51    ( ! [X0] : (k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),X0))) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),X0)))) ) | ~spl2_4),
% 0.20/0.51    inference(resolution,[],[f395,f53])).
% 0.20/0.51  fof(f395,plain,(
% 0.20/0.51    ( ! [X0] : (~r1_tarski(X0,k2_struct_0(sK0)) | k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,X0)) = k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,X0))) ) | ~spl2_4),
% 0.20/0.51    inference(resolution,[],[f220,f62])).
% 0.20/0.51  fof(f220,plain,(
% 0.20/0.51    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,X1)) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,X1))) ) | ~spl2_4),
% 0.20/0.51    inference(resolution,[],[f200,f58])).
% 0.20/0.51  fof(f200,plain,(
% 0.20/0.51    ( ! [X0] : (m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) ) | ~spl2_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f199])).
% 0.20/0.51  fof(f199,plain,(
% 0.20/0.51    spl2_4 <=> ! [X0] : (m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.51  fof(f2378,plain,(
% 0.20/0.51    k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) | (~spl2_2 | ~spl2_115)),
% 0.20/0.51    inference(forward_demodulation,[],[f2377,f69])).
% 0.20/0.51  fof(f69,plain,(
% 0.20/0.51    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~spl2_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f68])).
% 0.20/0.51  fof(f758,plain,(
% 0.20/0.51    ( ! [X1] : (k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),X1)) = k4_xboole_0(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),X1))))) ) | ~spl2_4),
% 0.20/0.51    inference(superposition,[],[f447,f143])).
% 0.20/0.51  fof(f143,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_subset_1(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.51    inference(resolution,[],[f141,f53])).
% 0.20/0.51  fof(f447,plain,(
% 0.20/0.51    ( ! [X0] : (k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),X0)) = k3_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),X0))))) ) | ~spl2_4),
% 0.20/0.51    inference(backward_demodulation,[],[f391,f442])).
% 0.20/0.51  fof(f391,plain,(
% 0.20/0.51    ( ! [X0] : (k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),X0)) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),X0))))) ) | ~spl2_4),
% 0.20/0.51    inference(resolution,[],[f387,f53])).
% 0.20/0.51  fof(f387,plain,(
% 0.20/0.51    ( ! [X0] : (~r1_tarski(X0,k2_struct_0(sK0)) | k2_pre_topc(sK0,X0) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,X0)))) ) | ~spl2_4),
% 0.20/0.51    inference(resolution,[],[f219,f62])).
% 0.20/0.51  fof(f219,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,X0)))) ) | ~spl2_4),
% 0.20/0.51    inference(resolution,[],[f200,f59])).
% 0.20/0.51  fof(f1958,plain,(
% 0.20/0.51    k2_struct_0(sK0) != k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) | spl2_97),
% 0.20/0.51    inference(avatar_component_clause,[],[f1956])).
% 0.20/0.51  fof(f1956,plain,(
% 0.20/0.51    spl2_97 <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_97])])).
% 0.20/0.51  fof(f2303,plain,(
% 0.20/0.51    ~spl2_3 | spl2_115),
% 0.20/0.51    inference(avatar_split_clause,[],[f2298,f2301,f195])).
% 0.20/0.51  fof(f195,plain,(
% 0.20/0.51    spl2_3 <=> l1_pre_topc(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.51  fof(f2298,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k1_tops_1(sK0,X0) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) | ~l1_pre_topc(sK0)) )),
% 0.20/0.51    inference(superposition,[],[f48,f77])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~l1_pre_topc(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f15])).
% 0.20/0.51  fof(f15,axiom,(
% 0.20/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).
% 0.20/0.51  fof(f1963,plain,(
% 0.20/0.51    spl2_59),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f1961])).
% 0.20/0.51  fof(f1961,plain,(
% 0.20/0.51    $false | spl2_59),
% 0.20/0.51    inference(resolution,[],[f1960,f53])).
% 0.20/0.51  fof(f1960,plain,(
% 0.20/0.51    ~r1_tarski(k4_xboole_0(k2_struct_0(sK0),sK1),k2_struct_0(sK0)) | spl2_59),
% 0.20/0.51    inference(resolution,[],[f1447,f62])).
% 0.20/0.51  fof(f1447,plain,(
% 0.20/0.51    ~m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | spl2_59),
% 0.20/0.51    inference(avatar_component_clause,[],[f1445])).
% 0.20/0.51  fof(f1445,plain,(
% 0.20/0.51    spl2_59 <=> m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_59])])).
% 0.20/0.51  fof(f1959,plain,(
% 0.20/0.51    ~spl2_3 | ~spl2_97 | ~spl2_59 | spl2_96),
% 0.20/0.51    inference(avatar_split_clause,[],[f1954,f1949,f1445,f1956,f195])).
% 0.20/0.51  fof(f1954,plain,(
% 0.20/0.51    ~m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | k2_struct_0(sK0) != k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) | ~l1_pre_topc(sK0) | spl2_96),
% 0.20/0.51    inference(forward_demodulation,[],[f1953,f77])).
% 0.20/0.51  fof(f1953,plain,(
% 0.20/0.51    k2_struct_0(sK0) != k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)) | ~m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_96),
% 0.20/0.51    inference(resolution,[],[f1951,f50])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f36])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(nnf_transformation,[],[f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,axiom,(
% 0.20/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).
% 0.20/0.51  fof(f1951,plain,(
% 0.20/0.51    ~v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) | spl2_96),
% 0.20/0.51    inference(avatar_component_clause,[],[f1949])).
% 0.20/0.51  fof(f1952,plain,(
% 0.20/0.51    ~spl2_3 | ~spl2_96 | ~spl2_44 | spl2_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f1947,f64,f1022,f1949,f195])).
% 0.20/0.51  fof(f1947,plain,(
% 0.20/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) | ~l1_pre_topc(sK0) | spl2_1),
% 0.20/0.51    inference(forward_demodulation,[],[f1946,f77])).
% 0.20/0.51  fof(f1946,plain,(
% 0.20/0.51    ~v1_tops_1(k4_xboole_0(k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_1),
% 0.20/0.51    inference(forward_demodulation,[],[f1945,f142])).
% 0.20/0.51  fof(f1945,plain,(
% 0.20/0.51    ~v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_1),
% 0.20/0.51    inference(forward_demodulation,[],[f1902,f77])).
% 0.20/0.51  fof(f1902,plain,(
% 0.20/0.51    ~v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_1),
% 0.20/0.51    inference(resolution,[],[f52,f66])).
% 0.20/0.51  fof(f66,plain,(
% 0.20/0.51    ~v2_tops_1(sK1,sK0) | spl2_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f64])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v2_tops_1(X1,X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f37])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(nnf_transformation,[],[f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,axiom,(
% 0.20/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_1)).
% 0.20/0.51  fof(f1421,plain,(
% 0.20/0.51    ~spl2_3 | spl2_57),
% 0.20/0.51    inference(avatar_split_clause,[],[f1413,f1419,f195])).
% 0.20/0.51  fof(f1413,plain,(
% 0.20/0.51    ( ! [X0] : (v1_tops_1(k3_subset_1(k2_struct_0(sK0),X0),sK0) | ~v2_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 0.20/0.51    inference(superposition,[],[f51,f77])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f37])).
% 0.20/0.51  fof(f513,plain,(
% 0.20/0.51    ~spl2_3 | spl2_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f508,f511,f195])).
% 0.20/0.51  fof(f508,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v1_tops_1(X0,sK0) | k2_struct_0(sK0) = k2_pre_topc(sK0,X0) | ~l1_pre_topc(sK0)) )),
% 0.20/0.51    inference(superposition,[],[f49,f77])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_1(X1,X0) | k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~l1_pre_topc(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f36])).
% 0.20/0.51  fof(f203,plain,(
% 0.20/0.51    spl2_3),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f202])).
% 0.20/0.51  fof(f202,plain,(
% 0.20/0.51    $false | spl2_3),
% 0.20/0.51    inference(subsumption_resolution,[],[f39,f197])).
% 0.20/0.51  fof(f197,plain,(
% 0.20/0.51    ~l1_pre_topc(sK0) | spl2_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f195])).
% 0.20/0.51  fof(f201,plain,(
% 0.20/0.51    ~spl2_3 | spl2_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f192,f199,f195])).
% 0.20/0.51  fof(f192,plain,(
% 0.20/0.51    ( ! [X0] : (m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 0.20/0.51    inference(superposition,[],[f60,f77])).
% 0.20/0.51  fof(f60,plain,(
% 0.20/0.51    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(flattening,[],[f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,axiom,(
% 0.20/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.20/0.51  fof(f72,plain,(
% 0.20/0.51    spl2_1 | spl2_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f41,f68,f64])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f35])).
% 0.20/0.51  fof(f71,plain,(
% 0.20/0.51    ~spl2_1 | ~spl2_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f42,f68,f64])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f35])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (15848)------------------------------
% 0.20/0.51  % (15848)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (15848)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (15848)Memory used [KB]: 7675
% 0.20/0.51  % (15848)Time elapsed: 0.093 s
% 0.20/0.51  % (15848)------------------------------
% 0.20/0.51  % (15848)------------------------------
% 0.20/0.51  % (15829)Success in time 0.155 s
%------------------------------------------------------------------------------
