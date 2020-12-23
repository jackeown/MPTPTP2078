%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:22 EST 2020

% Result     : Theorem 1.62s
% Output     : Refutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 500 expanded)
%              Number of leaves         :   32 ( 187 expanded)
%              Depth                    :   12
%              Number of atoms          :  456 (1251 expanded)
%              Number of equality atoms :   81 ( 317 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f699,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f89,f94,f99,f108,f111,f217,f224,f246,f252,f275,f353,f376,f438,f445,f450,f656,f695])).

fof(f695,plain,
    ( ~ spl2_1
    | ~ spl2_3
    | ~ spl2_10
    | ~ spl2_17
    | ~ spl2_18
    | spl2_21 ),
    inference(avatar_contradiction_clause,[],[f694])).

fof(f694,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_10
    | ~ spl2_17
    | ~ spl2_18
    | spl2_21 ),
    inference(subsumption_resolution,[],[f690,f163])).

fof(f163,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    inference(forward_demodulation,[],[f156,f80])).

fof(f80,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f57,f79])).

fof(f79,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f60,f56])).

fof(f56,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f60,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

fof(f57,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f156,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f58,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f58,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f690,plain,
    ( k1_xboole_0 != k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_10
    | ~ spl2_17
    | ~ spl2_18
    | spl2_21 ),
    inference(backward_demodulation,[],[f667,f689])).

fof(f689,plain,
    ( u1_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_10
    | ~ spl2_17
    | ~ spl2_18 ),
    inference(backward_demodulation,[],[f660,f688])).

fof(f688,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_1
    | ~ spl2_10
    | ~ spl2_17
    | ~ spl2_18 ),
    inference(forward_demodulation,[],[f686,f375])).

fof(f375,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f373])).

fof(f373,plain,
    ( spl2_18
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f686,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_1
    | ~ spl2_10
    | ~ spl2_17 ),
    inference(unit_resulting_resolution,[],[f88,f352,f244,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_pre_topc(X0,X1) != k2_struct_0(X0) )
            & ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

fof(f244,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f243])).

fof(f243,plain,
    ( spl2_10
  <=> v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f352,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f350])).

fof(f350,plain,
    ( spl2_17
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f88,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl2_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f660,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_17 ),
    inference(backward_demodulation,[],[f648,f568])).

fof(f568,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(resolution,[],[f194,f98])).

fof(f98,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f194,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) )
    | ~ spl2_1 ),
    inference(resolution,[],[f62,f88])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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

fof(f648,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))))
    | ~ spl2_1
    | ~ spl2_17 ),
    inference(unit_resulting_resolution,[],[f88,f352,f184])).

fof(f184,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | k2_pre_topc(X1,X0) = k3_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0))) ) ),
    inference(resolution,[],[f71,f70])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
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

fof(f667,plain,
    ( k1_xboole_0 != k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_17
    | spl2_21 ),
    inference(forward_demodulation,[],[f436,f660])).

fof(f436,plain,
    ( k1_xboole_0 != k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | spl2_21 ),
    inference(avatar_component_clause,[],[f435])).

fof(f435,plain,
    ( spl2_21
  <=> k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f656,plain,
    ( ~ spl2_1
    | ~ spl2_9
    | spl2_10
    | ~ spl2_11
    | ~ spl2_15
    | ~ spl2_17
    | ~ spl2_21 ),
    inference(avatar_contradiction_clause,[],[f655])).

fof(f655,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_9
    | spl2_10
    | ~ spl2_11
    | ~ spl2_15
    | ~ spl2_17
    | ~ spl2_21 ),
    inference(subsumption_resolution,[],[f654,f369])).

fof(f369,plain,
    ( u1_struct_0(sK0) != k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_1
    | ~ spl2_9
    | spl2_10
    | ~ spl2_11
    | ~ spl2_15
    | ~ spl2_17 ),
    inference(forward_demodulation,[],[f356,f290])).

fof(f290,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl2_1
    | ~ spl2_9
    | ~ spl2_11
    | ~ spl2_15 ),
    inference(forward_demodulation,[],[f289,f80])).

fof(f289,plain,
    ( k2_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0)
    | ~ spl2_1
    | ~ spl2_9
    | ~ spl2_11
    | ~ spl2_15 ),
    inference(forward_demodulation,[],[f282,f269])).

fof(f269,plain,
    ( k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0))
    | ~ spl2_1
    | ~ spl2_9
    | ~ spl2_11 ),
    inference(backward_demodulation,[],[f237,f268])).

fof(f268,plain,
    ( k2_pre_topc(sK0,u1_struct_0(sK0)) = k2_struct_0(sK0)
    | ~ spl2_1
    | ~ spl2_11 ),
    inference(unit_resulting_resolution,[],[f88,f84,f251,f64])).

fof(f251,plain,
    ( v1_tops_1(u1_struct_0(sK0),sK0)
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f249])).

fof(f249,plain,
    ( spl2_11
  <=> v1_tops_1(u1_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f84,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f81,f80])).

fof(f81,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f59,f79])).

fof(f59,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f237,plain,
    ( k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,u1_struct_0(sK0)))
    | ~ spl2_1
    | ~ spl2_9 ),
    inference(backward_demodulation,[],[f196,f230])).

fof(f230,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0)
    | ~ spl2_9 ),
    inference(unit_resulting_resolution,[],[f55,f223,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f223,plain,
    ( r1_tarski(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0)
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f221])).

fof(f221,plain,
    ( spl2_9
  <=> r1_tarski(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f55,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f196,plain,
    ( k1_tops_1(sK0,k1_xboole_0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,u1_struct_0(sK0)))
    | ~ spl2_1 ),
    inference(forward_demodulation,[],[f192,f80])).

fof(f192,plain,
    ( k1_tops_1(sK0,k1_xboole_0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f88,f58,f62])).

fof(f282,plain,
    ( k2_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0)))
    | ~ spl2_15 ),
    inference(unit_resulting_resolution,[],[f274,f70])).

fof(f274,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f272])).

fof(f272,plain,
    ( spl2_15
  <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f356,plain,
    ( k2_struct_0(sK0) != k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_1
    | spl2_10
    | ~ spl2_17 ),
    inference(unit_resulting_resolution,[],[f88,f245,f352,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) != k2_struct_0(X0)
      | v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f245,plain,
    ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | spl2_10 ),
    inference(avatar_component_clause,[],[f243])).

fof(f654,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_1
    | ~ spl2_17
    | ~ spl2_21 ),
    inference(forward_demodulation,[],[f653,f80])).

fof(f653,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0)
    | ~ spl2_1
    | ~ spl2_17
    | ~ spl2_21 ),
    inference(forward_demodulation,[],[f648,f437])).

fof(f437,plain,
    ( k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f435])).

fof(f450,plain,
    ( ~ spl2_4
    | ~ spl2_1
    | ~ spl2_3
    | spl2_10 ),
    inference(avatar_split_clause,[],[f247,f243,f96,f86,f101])).

fof(f101,plain,
    ( spl2_4
  <=> v2_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f247,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ spl2_1
    | ~ spl2_3
    | spl2_10 ),
    inference(unit_resulting_resolution,[],[f88,f98,f245,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
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

fof(f445,plain,
    ( spl2_5
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_21 ),
    inference(avatar_split_clause,[],[f442,f435,f96,f86,f105])).

fof(f105,plain,
    ( spl2_5
  <=> k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f442,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_21 ),
    inference(backward_demodulation,[],[f191,f437])).

fof(f191,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f88,f98,f62])).

fof(f438,plain,
    ( spl2_21
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f197,f105,f96,f86,f435])).

fof(f197,plain,
    ( k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f191,f107])).

fof(f107,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f105])).

fof(f376,plain,
    ( spl2_18
    | ~ spl2_1
    | ~ spl2_9
    | ~ spl2_11
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f290,f272,f249,f221,f86,f373])).

fof(f353,plain,
    ( spl2_17
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f138,f96,f350])).

fof(f138,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f98,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f275,plain,
    ( spl2_15
    | ~ spl2_1
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f270,f249,f86,f272])).

fof(f270,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_1
    | ~ spl2_11 ),
    inference(backward_demodulation,[],[f183,f268])).

fof(f183,plain,
    ( m1_subset_1(k2_pre_topc(sK0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f88,f84,f71])).

fof(f252,plain,
    ( spl2_11
    | ~ spl2_1
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f219,f214,f86,f249])).

fof(f214,plain,
    ( spl2_8
  <=> v2_tops_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f219,plain,
    ( v1_tops_1(u1_struct_0(sK0),sK0)
    | ~ spl2_1
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f218,f80])).

fof(f218,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),sK0)
    | ~ spl2_1
    | ~ spl2_8 ),
    inference(unit_resulting_resolution,[],[f88,f58,f216,f66])).

fof(f216,plain,
    ( v2_tops_1(k1_xboole_0,sK0)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f214])).

fof(f246,plain,
    ( ~ spl2_10
    | ~ spl2_1
    | ~ spl2_3
    | spl2_4 ),
    inference(avatar_split_clause,[],[f189,f101,f96,f86,f243])).

fof(f189,plain,
    ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl2_1
    | ~ spl2_3
    | spl2_4 ),
    inference(unit_resulting_resolution,[],[f88,f102,f98,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f102,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f101])).

fof(f224,plain,
    ( spl2_9
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f169,f86,f221])).

fof(f169,plain,
    ( r1_tarski(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0)
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f88,f58,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f217,plain,
    ( spl2_8
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f174,f91,f86,f214])).

fof(f91,plain,
    ( spl2_2
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f174,plain,
    ( v2_tops_1(k1_xboole_0,sK0)
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f88,f93,f58,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v2_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tops_1)).

fof(f93,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f91])).

fof(f111,plain,
    ( ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f110,f105,f101])).

fof(f110,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ spl2_5 ),
    inference(trivial_inequality_removal,[],[f109])).

fof(f109,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v2_tops_1(sK1,sK0)
    | ~ spl2_5 ),
    inference(backward_demodulation,[],[f53,f107])).

fof(f53,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ( k1_xboole_0 != k1_tops_1(sK0,sK1)
      | ~ v2_tops_1(sK1,sK0) )
    & ( k1_xboole_0 = k1_tops_1(sK0,sK1)
      | v2_tops_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f41,f43,f42])).

fof(f42,plain,
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

fof(f43,plain,
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

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(X0,X1)
            | ~ v2_tops_1(X1,X0) )
          & ( k1_xboole_0 = k1_tops_1(X0,X1)
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(X0,X1)
            | ~ v2_tops_1(X1,X0) )
          & ( k1_xboole_0 = k1_tops_1(X0,X1)
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
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

fof(f108,plain,
    ( spl2_4
    | spl2_5 ),
    inference(avatar_split_clause,[],[f52,f105,f101])).

fof(f52,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f99,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f51,f96])).

fof(f51,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f44])).

fof(f94,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f54,f91])).

fof(f54,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f89,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f50,f86])).

fof(f50,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:49:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (14760)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.50  % (14775)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.51  % (14767)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (14763)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.52  % (14776)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.52  % (14771)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.52  % (14780)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.53  % (14772)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.53  % (14762)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.53  % (14778)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.53  % (14783)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.53  % (14779)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.53  % (14788)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.53  % (14761)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (14769)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.54  % (14784)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.54  % (14764)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.54  % (14768)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.54  % (14770)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.54  % (14785)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.54  % (14786)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.55  % (14790)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.55  % (14777)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.55  % (14782)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.55  % (14773)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.55  % (14774)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.55  % (14790)Refutation not found, incomplete strategy% (14790)------------------------------
% 0.22/0.55  % (14790)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (14790)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (14790)Memory used [KB]: 1663
% 0.22/0.55  % (14790)Time elapsed: 0.102 s
% 0.22/0.55  % (14790)------------------------------
% 0.22/0.55  % (14790)------------------------------
% 0.22/0.55  % (14787)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (14766)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.48/0.56  % (14781)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.48/0.57  % (14789)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.62/0.60  % (14781)Refutation found. Thanks to Tanya!
% 1.62/0.60  % SZS status Theorem for theBenchmark
% 1.62/0.60  % SZS output start Proof for theBenchmark
% 1.62/0.60  fof(f699,plain,(
% 1.62/0.60    $false),
% 1.62/0.60    inference(avatar_sat_refutation,[],[f89,f94,f99,f108,f111,f217,f224,f246,f252,f275,f353,f376,f438,f445,f450,f656,f695])).
% 1.62/0.60  fof(f695,plain,(
% 1.62/0.60    ~spl2_1 | ~spl2_3 | ~spl2_10 | ~spl2_17 | ~spl2_18 | spl2_21),
% 1.62/0.60    inference(avatar_contradiction_clause,[],[f694])).
% 1.62/0.60  fof(f694,plain,(
% 1.62/0.60    $false | (~spl2_1 | ~spl2_3 | ~spl2_10 | ~spl2_17 | ~spl2_18 | spl2_21)),
% 1.62/0.60    inference(subsumption_resolution,[],[f690,f163])).
% 1.62/0.60  fof(f163,plain,(
% 1.62/0.60    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0)) )),
% 1.62/0.60    inference(forward_demodulation,[],[f156,f80])).
% 1.62/0.60  fof(f80,plain,(
% 1.62/0.60    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 1.62/0.60    inference(definition_unfolding,[],[f57,f79])).
% 1.62/0.60  fof(f79,plain,(
% 1.62/0.60    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 1.62/0.60    inference(definition_unfolding,[],[f60,f56])).
% 1.62/0.60  fof(f56,plain,(
% 1.62/0.60    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 1.62/0.60    inference(cnf_transformation,[],[f5])).
% 1.62/0.60  fof(f5,axiom,(
% 1.62/0.60    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 1.62/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 1.62/0.60  fof(f60,plain,(
% 1.62/0.60    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 1.62/0.60    inference(cnf_transformation,[],[f10])).
% 1.62/0.60  fof(f10,axiom,(
% 1.62/0.60    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 1.62/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).
% 1.62/0.60  fof(f57,plain,(
% 1.62/0.60    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.62/0.60    inference(cnf_transformation,[],[f6])).
% 1.62/0.60  fof(f6,axiom,(
% 1.62/0.60    ! [X0] : k2_subset_1(X0) = X0),
% 1.62/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.62/0.60  fof(f156,plain,(
% 1.62/0.60    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0))) )),
% 1.62/0.60    inference(unit_resulting_resolution,[],[f58,f70])).
% 1.62/0.60  fof(f70,plain,(
% 1.62/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 1.62/0.60    inference(cnf_transformation,[],[f33])).
% 1.62/0.60  fof(f33,plain,(
% 1.62/0.60    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.62/0.60    inference(ennf_transformation,[],[f9])).
% 1.62/0.60  fof(f9,axiom,(
% 1.62/0.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.62/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.62/0.60  fof(f58,plain,(
% 1.62/0.60    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.62/0.60    inference(cnf_transformation,[],[f11])).
% 1.62/0.60  fof(f11,axiom,(
% 1.62/0.60    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.62/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 1.62/0.60  fof(f690,plain,(
% 1.62/0.60    k1_xboole_0 != k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) | (~spl2_1 | ~spl2_3 | ~spl2_10 | ~spl2_17 | ~spl2_18 | spl2_21)),
% 1.62/0.60    inference(backward_demodulation,[],[f667,f689])).
% 1.62/0.60  fof(f689,plain,(
% 1.62/0.60    u1_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) | (~spl2_1 | ~spl2_3 | ~spl2_10 | ~spl2_17 | ~spl2_18)),
% 1.62/0.60    inference(backward_demodulation,[],[f660,f688])).
% 1.62/0.60  fof(f688,plain,(
% 1.62/0.60    u1_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | (~spl2_1 | ~spl2_10 | ~spl2_17 | ~spl2_18)),
% 1.62/0.60    inference(forward_demodulation,[],[f686,f375])).
% 1.62/0.60  fof(f375,plain,(
% 1.62/0.60    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl2_18),
% 1.62/0.60    inference(avatar_component_clause,[],[f373])).
% 1.62/0.60  fof(f373,plain,(
% 1.62/0.60    spl2_18 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 1.62/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 1.62/0.60  fof(f686,plain,(
% 1.62/0.60    k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | (~spl2_1 | ~spl2_10 | ~spl2_17)),
% 1.62/0.60    inference(unit_resulting_resolution,[],[f88,f352,f244,f64])).
% 1.62/0.60  fof(f64,plain,(
% 1.62/0.60    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k2_struct_0(X0)) )),
% 1.62/0.60    inference(cnf_transformation,[],[f45])).
% 1.62/0.60  fof(f45,plain,(
% 1.62/0.60    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_pre_topc(X0,X1) != k2_struct_0(X0)) & (k2_pre_topc(X0,X1) = k2_struct_0(X0) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.62/0.60    inference(nnf_transformation,[],[f28])).
% 1.62/0.60  fof(f28,plain,(
% 1.62/0.60    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.62/0.60    inference(ennf_transformation,[],[f17])).
% 1.62/0.60  fof(f17,axiom,(
% 1.62/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0))))),
% 1.62/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).
% 1.62/0.60  fof(f244,plain,(
% 1.62/0.60    v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~spl2_10),
% 1.62/0.60    inference(avatar_component_clause,[],[f243])).
% 1.62/0.60  fof(f243,plain,(
% 1.62/0.60    spl2_10 <=> v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 1.62/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 1.62/0.60  fof(f352,plain,(
% 1.62/0.60    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_17),
% 1.62/0.60    inference(avatar_component_clause,[],[f350])).
% 1.62/0.60  fof(f350,plain,(
% 1.62/0.60    spl2_17 <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.62/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 1.62/0.60  fof(f88,plain,(
% 1.62/0.60    l1_pre_topc(sK0) | ~spl2_1),
% 1.62/0.60    inference(avatar_component_clause,[],[f86])).
% 1.62/0.60  fof(f86,plain,(
% 1.62/0.60    spl2_1 <=> l1_pre_topc(sK0)),
% 1.62/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.62/0.60  fof(f660,plain,(
% 1.62/0.60    k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) | (~spl2_1 | ~spl2_3 | ~spl2_17)),
% 1.62/0.60    inference(backward_demodulation,[],[f648,f568])).
% 1.62/0.60  fof(f568,plain,(
% 1.62/0.60    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | (~spl2_1 | ~spl2_3)),
% 1.62/0.60    inference(resolution,[],[f194,f98])).
% 1.62/0.60  fof(f98,plain,(
% 1.62/0.60    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 1.62/0.60    inference(avatar_component_clause,[],[f96])).
% 1.62/0.60  fof(f96,plain,(
% 1.62/0.60    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.62/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.62/0.60  fof(f194,plain,(
% 1.62/0.60    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)))) ) | ~spl2_1),
% 1.62/0.60    inference(resolution,[],[f62,f88])).
% 1.62/0.60  fof(f62,plain,(
% 1.62/0.60    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))) )),
% 1.62/0.60    inference(cnf_transformation,[],[f25])).
% 1.62/0.60  fof(f25,plain,(
% 1.62/0.60    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.62/0.60    inference(ennf_transformation,[],[f16])).
% 1.62/0.60  fof(f16,axiom,(
% 1.62/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 1.62/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).
% 1.62/0.60  fof(f648,plain,(
% 1.62/0.60    k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) | (~spl2_1 | ~spl2_17)),
% 1.62/0.60    inference(unit_resulting_resolution,[],[f88,f352,f184])).
% 1.62/0.60  fof(f184,plain,(
% 1.62/0.60    ( ! [X0,X1] : (~l1_pre_topc(X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | k2_pre_topc(X1,X0) = k3_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0)))) )),
% 1.62/0.60    inference(resolution,[],[f71,f70])).
% 1.62/0.60  fof(f71,plain,(
% 1.62/0.60    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.62/0.60    inference(cnf_transformation,[],[f35])).
% 1.62/0.60  fof(f35,plain,(
% 1.62/0.60    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.62/0.60    inference(flattening,[],[f34])).
% 1.62/0.60  fof(f34,plain,(
% 1.62/0.60    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.62/0.60    inference(ennf_transformation,[],[f14])).
% 1.62/0.60  fof(f14,axiom,(
% 1.62/0.60    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.62/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 1.62/0.60  fof(f667,plain,(
% 1.62/0.60    k1_xboole_0 != k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) | (~spl2_1 | ~spl2_3 | ~spl2_17 | spl2_21)),
% 1.62/0.60    inference(forward_demodulation,[],[f436,f660])).
% 1.62/0.60  fof(f436,plain,(
% 1.62/0.60    k1_xboole_0 != k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | spl2_21),
% 1.62/0.60    inference(avatar_component_clause,[],[f435])).
% 1.62/0.60  fof(f435,plain,(
% 1.62/0.60    spl2_21 <=> k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),
% 1.62/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 1.62/0.60  fof(f656,plain,(
% 1.62/0.60    ~spl2_1 | ~spl2_9 | spl2_10 | ~spl2_11 | ~spl2_15 | ~spl2_17 | ~spl2_21),
% 1.62/0.60    inference(avatar_contradiction_clause,[],[f655])).
% 1.62/0.60  fof(f655,plain,(
% 1.62/0.60    $false | (~spl2_1 | ~spl2_9 | spl2_10 | ~spl2_11 | ~spl2_15 | ~spl2_17 | ~spl2_21)),
% 1.62/0.60    inference(subsumption_resolution,[],[f654,f369])).
% 1.62/0.60  fof(f369,plain,(
% 1.62/0.60    u1_struct_0(sK0) != k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | (~spl2_1 | ~spl2_9 | spl2_10 | ~spl2_11 | ~spl2_15 | ~spl2_17)),
% 1.62/0.60    inference(forward_demodulation,[],[f356,f290])).
% 1.62/0.60  fof(f290,plain,(
% 1.62/0.60    u1_struct_0(sK0) = k2_struct_0(sK0) | (~spl2_1 | ~spl2_9 | ~spl2_11 | ~spl2_15)),
% 1.62/0.60    inference(forward_demodulation,[],[f289,f80])).
% 1.62/0.60  fof(f289,plain,(
% 1.62/0.60    k2_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0) | (~spl2_1 | ~spl2_9 | ~spl2_11 | ~spl2_15)),
% 1.62/0.60    inference(forward_demodulation,[],[f282,f269])).
% 1.62/0.60  fof(f269,plain,(
% 1.62/0.60    k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0)) | (~spl2_1 | ~spl2_9 | ~spl2_11)),
% 1.62/0.60    inference(backward_demodulation,[],[f237,f268])).
% 1.62/0.60  fof(f268,plain,(
% 1.62/0.60    k2_pre_topc(sK0,u1_struct_0(sK0)) = k2_struct_0(sK0) | (~spl2_1 | ~spl2_11)),
% 1.62/0.60    inference(unit_resulting_resolution,[],[f88,f84,f251,f64])).
% 1.62/0.60  fof(f251,plain,(
% 1.62/0.60    v1_tops_1(u1_struct_0(sK0),sK0) | ~spl2_11),
% 1.62/0.60    inference(avatar_component_clause,[],[f249])).
% 1.62/0.60  fof(f249,plain,(
% 1.62/0.60    spl2_11 <=> v1_tops_1(u1_struct_0(sK0),sK0)),
% 1.62/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 1.62/0.60  fof(f84,plain,(
% 1.62/0.60    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.62/0.60    inference(forward_demodulation,[],[f81,f80])).
% 1.62/0.60  fof(f81,plain,(
% 1.62/0.60    ( ! [X0] : (m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0))) )),
% 1.62/0.60    inference(definition_unfolding,[],[f59,f79])).
% 1.62/0.60  fof(f59,plain,(
% 1.62/0.60    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.62/0.60    inference(cnf_transformation,[],[f7])).
% 1.62/0.60  fof(f7,axiom,(
% 1.62/0.60    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.62/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.62/0.60  fof(f237,plain,(
% 1.62/0.60    k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,u1_struct_0(sK0))) | (~spl2_1 | ~spl2_9)),
% 1.62/0.60    inference(backward_demodulation,[],[f196,f230])).
% 1.62/0.60  fof(f230,plain,(
% 1.62/0.60    k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0) | ~spl2_9),
% 1.62/0.60    inference(unit_resulting_resolution,[],[f55,f223,f74])).
% 1.62/0.60  fof(f74,plain,(
% 1.62/0.60    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.62/0.60    inference(cnf_transformation,[],[f48])).
% 1.62/0.60  fof(f48,plain,(
% 1.62/0.60    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.62/0.60    inference(flattening,[],[f47])).
% 1.62/0.60  fof(f47,plain,(
% 1.62/0.60    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.62/0.60    inference(nnf_transformation,[],[f2])).
% 1.62/0.60  fof(f2,axiom,(
% 1.62/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.62/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.62/0.60  fof(f223,plain,(
% 1.62/0.60    r1_tarski(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0) | ~spl2_9),
% 1.62/0.60    inference(avatar_component_clause,[],[f221])).
% 1.62/0.60  fof(f221,plain,(
% 1.62/0.60    spl2_9 <=> r1_tarski(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0)),
% 1.62/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 1.62/0.60  fof(f55,plain,(
% 1.62/0.60    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.62/0.60    inference(cnf_transformation,[],[f4])).
% 1.62/0.60  fof(f4,axiom,(
% 1.62/0.60    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.62/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.62/0.60  fof(f196,plain,(
% 1.62/0.60    k1_tops_1(sK0,k1_xboole_0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,u1_struct_0(sK0))) | ~spl2_1),
% 1.62/0.60    inference(forward_demodulation,[],[f192,f80])).
% 1.62/0.60  fof(f192,plain,(
% 1.62/0.60    k1_tops_1(sK0,k1_xboole_0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0))) | ~spl2_1),
% 1.62/0.60    inference(unit_resulting_resolution,[],[f88,f58,f62])).
% 1.62/0.60  fof(f282,plain,(
% 1.62/0.60    k2_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0))) | ~spl2_15),
% 1.62/0.60    inference(unit_resulting_resolution,[],[f274,f70])).
% 1.62/0.60  fof(f274,plain,(
% 1.62/0.60    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_15),
% 1.62/0.60    inference(avatar_component_clause,[],[f272])).
% 1.62/0.60  fof(f272,plain,(
% 1.62/0.60    spl2_15 <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.62/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 1.62/0.60  fof(f356,plain,(
% 1.62/0.60    k2_struct_0(sK0) != k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | (~spl2_1 | spl2_10 | ~spl2_17)),
% 1.62/0.60    inference(unit_resulting_resolution,[],[f88,f245,f352,f65])).
% 1.62/0.60  fof(f65,plain,(
% 1.62/0.60    ( ! [X0,X1] : (k2_pre_topc(X0,X1) != k2_struct_0(X0) | v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.62/0.60    inference(cnf_transformation,[],[f45])).
% 1.62/0.60  fof(f245,plain,(
% 1.62/0.60    ~v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | spl2_10),
% 1.62/0.60    inference(avatar_component_clause,[],[f243])).
% 1.62/0.60  fof(f654,plain,(
% 1.62/0.60    u1_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | (~spl2_1 | ~spl2_17 | ~spl2_21)),
% 1.62/0.60    inference(forward_demodulation,[],[f653,f80])).
% 1.62/0.60  fof(f653,plain,(
% 1.62/0.60    k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0) | (~spl2_1 | ~spl2_17 | ~spl2_21)),
% 1.62/0.60    inference(forward_demodulation,[],[f648,f437])).
% 1.62/0.60  fof(f437,plain,(
% 1.62/0.60    k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | ~spl2_21),
% 1.62/0.60    inference(avatar_component_clause,[],[f435])).
% 1.62/0.60  fof(f450,plain,(
% 1.62/0.60    ~spl2_4 | ~spl2_1 | ~spl2_3 | spl2_10),
% 1.62/0.60    inference(avatar_split_clause,[],[f247,f243,f96,f86,f101])).
% 1.62/0.60  fof(f101,plain,(
% 1.62/0.60    spl2_4 <=> v2_tops_1(sK1,sK0)),
% 1.62/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 1.62/0.60  fof(f247,plain,(
% 1.62/0.60    ~v2_tops_1(sK1,sK0) | (~spl2_1 | ~spl2_3 | spl2_10)),
% 1.62/0.60    inference(unit_resulting_resolution,[],[f88,f98,f245,f66])).
% 1.62/0.60  fof(f66,plain,(
% 1.62/0.60    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) )),
% 1.62/0.60    inference(cnf_transformation,[],[f46])).
% 1.62/0.60  fof(f46,plain,(
% 1.62/0.60    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.62/0.60    inference(nnf_transformation,[],[f29])).
% 1.62/0.60  fof(f29,plain,(
% 1.62/0.60    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.62/0.60    inference(ennf_transformation,[],[f18])).
% 1.62/0.60  fof(f18,axiom,(
% 1.62/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 1.62/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_1)).
% 1.62/0.60  fof(f445,plain,(
% 1.62/0.60    spl2_5 | ~spl2_1 | ~spl2_3 | ~spl2_21),
% 1.62/0.60    inference(avatar_split_clause,[],[f442,f435,f96,f86,f105])).
% 1.62/0.60  fof(f105,plain,(
% 1.62/0.60    spl2_5 <=> k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 1.62/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 1.62/0.60  fof(f442,plain,(
% 1.62/0.60    k1_xboole_0 = k1_tops_1(sK0,sK1) | (~spl2_1 | ~spl2_3 | ~spl2_21)),
% 1.62/0.60    inference(backward_demodulation,[],[f191,f437])).
% 1.62/0.60  fof(f191,plain,(
% 1.62/0.60    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | (~spl2_1 | ~spl2_3)),
% 1.62/0.60    inference(unit_resulting_resolution,[],[f88,f98,f62])).
% 1.62/0.60  fof(f438,plain,(
% 1.62/0.60    spl2_21 | ~spl2_1 | ~spl2_3 | ~spl2_5),
% 1.62/0.60    inference(avatar_split_clause,[],[f197,f105,f96,f86,f435])).
% 1.62/0.60  fof(f197,plain,(
% 1.62/0.60    k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | (~spl2_1 | ~spl2_3 | ~spl2_5)),
% 1.62/0.60    inference(forward_demodulation,[],[f191,f107])).
% 1.62/0.60  fof(f107,plain,(
% 1.62/0.60    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~spl2_5),
% 1.62/0.60    inference(avatar_component_clause,[],[f105])).
% 1.62/0.60  fof(f376,plain,(
% 1.62/0.60    spl2_18 | ~spl2_1 | ~spl2_9 | ~spl2_11 | ~spl2_15),
% 1.62/0.60    inference(avatar_split_clause,[],[f290,f272,f249,f221,f86,f373])).
% 1.62/0.60  fof(f353,plain,(
% 1.62/0.60    spl2_17 | ~spl2_3),
% 1.62/0.60    inference(avatar_split_clause,[],[f138,f96,f350])).
% 1.62/0.60  fof(f138,plain,(
% 1.62/0.60    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 1.62/0.60    inference(unit_resulting_resolution,[],[f98,f69])).
% 1.62/0.60  fof(f69,plain,(
% 1.62/0.60    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.62/0.60    inference(cnf_transformation,[],[f32])).
% 1.62/0.60  fof(f32,plain,(
% 1.62/0.60    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.62/0.60    inference(ennf_transformation,[],[f8])).
% 1.62/0.60  fof(f8,axiom,(
% 1.62/0.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.62/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.62/0.60  fof(f275,plain,(
% 1.62/0.60    spl2_15 | ~spl2_1 | ~spl2_11),
% 1.62/0.60    inference(avatar_split_clause,[],[f270,f249,f86,f272])).
% 1.62/0.60  fof(f270,plain,(
% 1.62/0.60    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_1 | ~spl2_11)),
% 1.62/0.60    inference(backward_demodulation,[],[f183,f268])).
% 1.62/0.60  fof(f183,plain,(
% 1.62/0.60    m1_subset_1(k2_pre_topc(sK0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_1),
% 1.62/0.60    inference(unit_resulting_resolution,[],[f88,f84,f71])).
% 1.62/0.60  fof(f252,plain,(
% 1.62/0.60    spl2_11 | ~spl2_1 | ~spl2_8),
% 1.62/0.60    inference(avatar_split_clause,[],[f219,f214,f86,f249])).
% 1.62/0.60  fof(f214,plain,(
% 1.62/0.60    spl2_8 <=> v2_tops_1(k1_xboole_0,sK0)),
% 1.62/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 1.62/0.60  fof(f219,plain,(
% 1.62/0.60    v1_tops_1(u1_struct_0(sK0),sK0) | (~spl2_1 | ~spl2_8)),
% 1.62/0.60    inference(forward_demodulation,[],[f218,f80])).
% 1.62/0.60  fof(f218,plain,(
% 1.62/0.60    v1_tops_1(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),sK0) | (~spl2_1 | ~spl2_8)),
% 1.62/0.60    inference(unit_resulting_resolution,[],[f88,f58,f216,f66])).
% 1.62/0.60  fof(f216,plain,(
% 1.62/0.60    v2_tops_1(k1_xboole_0,sK0) | ~spl2_8),
% 1.62/0.60    inference(avatar_component_clause,[],[f214])).
% 1.62/0.60  fof(f246,plain,(
% 1.62/0.60    ~spl2_10 | ~spl2_1 | ~spl2_3 | spl2_4),
% 1.62/0.60    inference(avatar_split_clause,[],[f189,f101,f96,f86,f243])).
% 1.62/0.60  fof(f189,plain,(
% 1.62/0.60    ~v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | (~spl2_1 | ~spl2_3 | spl2_4)),
% 1.62/0.60    inference(unit_resulting_resolution,[],[f88,f102,f98,f67])).
% 1.62/0.60  fof(f67,plain,(
% 1.62/0.60    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tops_1(X1,X0)) )),
% 1.62/0.60    inference(cnf_transformation,[],[f46])).
% 1.62/0.60  fof(f102,plain,(
% 1.62/0.60    ~v2_tops_1(sK1,sK0) | spl2_4),
% 1.62/0.60    inference(avatar_component_clause,[],[f101])).
% 1.62/0.60  fof(f224,plain,(
% 1.62/0.60    spl2_9 | ~spl2_1),
% 1.62/0.60    inference(avatar_split_clause,[],[f169,f86,f221])).
% 1.62/0.60  fof(f169,plain,(
% 1.62/0.60    r1_tarski(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0) | ~spl2_1),
% 1.62/0.60    inference(unit_resulting_resolution,[],[f88,f58,f61])).
% 1.62/0.60  fof(f61,plain,(
% 1.62/0.60    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 1.62/0.60    inference(cnf_transformation,[],[f24])).
% 1.62/0.60  fof(f24,plain,(
% 1.62/0.60    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.62/0.60    inference(ennf_transformation,[],[f19])).
% 1.62/0.60  fof(f19,axiom,(
% 1.62/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 1.62/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 1.62/0.60  fof(f217,plain,(
% 1.62/0.60    spl2_8 | ~spl2_1 | ~spl2_2),
% 1.62/0.60    inference(avatar_split_clause,[],[f174,f91,f86,f214])).
% 1.62/0.60  fof(f91,plain,(
% 1.62/0.60    spl2_2 <=> v1_xboole_0(k1_xboole_0)),
% 1.62/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.62/0.60  fof(f174,plain,(
% 1.62/0.60    v2_tops_1(k1_xboole_0,sK0) | (~spl2_1 | ~spl2_2)),
% 1.62/0.60    inference(unit_resulting_resolution,[],[f88,f93,f58,f63])).
% 1.62/0.60  fof(f63,plain,(
% 1.62/0.60    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tops_1(X1,X0)) )),
% 1.62/0.60    inference(cnf_transformation,[],[f27])).
% 1.62/0.60  fof(f27,plain,(
% 1.62/0.60    ! [X0] : (! [X1] : (v2_tops_1(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.62/0.60    inference(flattening,[],[f26])).
% 1.62/0.60  fof(f26,plain,(
% 1.62/0.60    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.62/0.60    inference(ennf_transformation,[],[f15])).
% 1.62/0.60  fof(f15,axiom,(
% 1.62/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v2_tops_1(X1,X0))))),
% 1.62/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tops_1)).
% 1.62/0.60  fof(f93,plain,(
% 1.62/0.60    v1_xboole_0(k1_xboole_0) | ~spl2_2),
% 1.62/0.60    inference(avatar_component_clause,[],[f91])).
% 1.62/0.60  fof(f111,plain,(
% 1.62/0.60    ~spl2_4 | ~spl2_5),
% 1.62/0.60    inference(avatar_split_clause,[],[f110,f105,f101])).
% 1.62/0.60  fof(f110,plain,(
% 1.62/0.60    ~v2_tops_1(sK1,sK0) | ~spl2_5),
% 1.62/0.60    inference(trivial_inequality_removal,[],[f109])).
% 1.62/0.60  fof(f109,plain,(
% 1.62/0.60    k1_xboole_0 != k1_xboole_0 | ~v2_tops_1(sK1,sK0) | ~spl2_5),
% 1.62/0.60    inference(backward_demodulation,[],[f53,f107])).
% 1.62/0.60  fof(f53,plain,(
% 1.62/0.60    k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)),
% 1.62/0.60    inference(cnf_transformation,[],[f44])).
% 1.62/0.60  fof(f44,plain,(
% 1.62/0.60    ((k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 1.62/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f41,f43,f42])).
% 1.62/0.60  fof(f42,plain,(
% 1.62/0.60    ? [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((k1_xboole_0 != k1_tops_1(sK0,X1) | ~v2_tops_1(X1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,X1) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 1.62/0.60    introduced(choice_axiom,[])).
% 1.62/0.60  fof(f43,plain,(
% 1.62/0.60    ? [X1] : ((k1_xboole_0 != k1_tops_1(sK0,X1) | ~v2_tops_1(X1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,X1) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.62/0.60    introduced(choice_axiom,[])).
% 1.62/0.60  fof(f41,plain,(
% 1.62/0.60    ? [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.62/0.60    inference(flattening,[],[f40])).
% 1.62/0.60  fof(f40,plain,(
% 1.62/0.60    ? [X0] : (? [X1] : (((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.62/0.60    inference(nnf_transformation,[],[f23])).
% 1.62/0.60  fof(f23,plain,(
% 1.62/0.60    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> k1_xboole_0 = k1_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.62/0.60    inference(ennf_transformation,[],[f22])).
% 1.62/0.60  fof(f22,negated_conjecture,(
% 1.62/0.60    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 1.62/0.60    inference(negated_conjecture,[],[f21])).
% 1.62/0.60  fof(f21,conjecture,(
% 1.62/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 1.62/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).
% 1.62/0.60  fof(f108,plain,(
% 1.62/0.60    spl2_4 | spl2_5),
% 1.62/0.60    inference(avatar_split_clause,[],[f52,f105,f101])).
% 1.62/0.60  fof(f52,plain,(
% 1.62/0.60    k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)),
% 1.62/0.60    inference(cnf_transformation,[],[f44])).
% 1.62/0.60  fof(f99,plain,(
% 1.62/0.60    spl2_3),
% 1.62/0.60    inference(avatar_split_clause,[],[f51,f96])).
% 1.62/0.60  fof(f51,plain,(
% 1.62/0.60    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.62/0.60    inference(cnf_transformation,[],[f44])).
% 1.62/0.60  fof(f94,plain,(
% 1.62/0.60    spl2_2),
% 1.62/0.60    inference(avatar_split_clause,[],[f54,f91])).
% 1.62/0.60  fof(f54,plain,(
% 1.62/0.60    v1_xboole_0(k1_xboole_0)),
% 1.62/0.60    inference(cnf_transformation,[],[f1])).
% 1.62/0.60  fof(f1,axiom,(
% 1.62/0.60    v1_xboole_0(k1_xboole_0)),
% 1.62/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.62/0.60  fof(f89,plain,(
% 1.62/0.60    spl2_1),
% 1.62/0.60    inference(avatar_split_clause,[],[f50,f86])).
% 1.62/0.60  fof(f50,plain,(
% 1.62/0.60    l1_pre_topc(sK0)),
% 1.62/0.60    inference(cnf_transformation,[],[f44])).
% 1.62/0.60  % SZS output end Proof for theBenchmark
% 1.62/0.60  % (14781)------------------------------
% 1.62/0.60  % (14781)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.60  % (14781)Termination reason: Refutation
% 1.62/0.60  
% 1.62/0.60  % (14781)Memory used [KB]: 11129
% 1.62/0.60  % (14781)Time elapsed: 0.183 s
% 1.62/0.62  % (14781)------------------------------
% 1.62/0.62  % (14781)------------------------------
% 1.62/0.62  % (14759)Success in time 0.249 s
%------------------------------------------------------------------------------
