%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:15 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 317 expanded)
%              Number of leaves         :   26 (  83 expanded)
%              Depth                    :   14
%              Number of atoms          :  365 (1397 expanded)
%              Number of equality atoms :   37 (  64 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f473,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f118,f126,f135,f143,f175,f179,f313,f318,f321,f443,f472])).

fof(f472,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f471])).

fof(f471,plain,
    ( $false
    | spl3_4 ),
    inference(resolution,[],[f465,f114])).

fof(f114,plain,
    ( ~ v1_tops_1(sK1,sK0)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl3_4
  <=> v1_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f465,plain,(
    v1_tops_1(sK1,sK0) ),
    inference(global_subsumption,[],[f448])).

fof(f448,plain,(
    v1_tops_1(sK1,sK0) ),
    inference(global_subsumption,[],[f154,f447])).

fof(f447,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(global_subsumption,[],[f446])).

fof(f446,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(global_subsumption,[],[f445])).

fof(f445,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(global_subsumption,[],[f444])).

fof(f444,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(global_subsumption,[],[f36,f41,f42,f43,f146])).

fof(f146,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v4_pre_topc(sK1,sK0)
    | v3_pre_topc(sK1,sK0)
    | ~ v3_tdlat_3(sK0) ),
    inference(resolution,[],[f55,f37])).

fof(f37,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(X0))
          & v3_tex_2(X1,X0)
          & ( v4_pre_topc(X1,X0)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(X0))
          & v3_tex_2(X1,X0)
          & ( v4_pre_topc(X1,X0)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ~ ( v1_subset_1(X1,u1_struct_0(X0))
                & v3_tex_2(X1,X0)
                & ( v4_pre_topc(X1,X0)
                  | v3_pre_topc(X1,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ~ ( v1_subset_1(X1,u1_struct_0(X0))
              & v3_tex_2(X1,X0)
              & ( v4_pre_topc(X1,X0)
                | v3_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_tex_2)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | v3_pre_topc(X1,X0)
      | ~ v3_tdlat_3(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => v3_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tdlat_3)).

fof(f43,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f42,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f41,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f36,plain,
    ( v3_pre_topc(sK1,sK0)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f154,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | v1_tops_1(sK1,sK0) ),
    inference(global_subsumption,[],[f40,f41,f43,f38,f151])).

fof(f151,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ v3_tex_2(sK1,sK0)
    | v1_tops_1(sK1,sK0) ),
    inference(resolution,[],[f54,f37])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ v3_tex_2(X1,X0)
      | v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v3_tex_2(X1,X0)
              & v3_pre_topc(X1,X0) )
           => v1_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_tex_2)).

fof(f38,plain,(
    v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f40,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f443,plain,(
    ~ spl3_12 ),
    inference(avatar_contradiction_clause,[],[f442])).

fof(f442,plain,
    ( $false
    | ~ spl3_12 ),
    inference(resolution,[],[f326,f206])).

fof(f206,plain,(
    ! [X1] : ~ v1_subset_1(X1,X1) ),
    inference(global_subsumption,[],[f44,f72,f195])).

fof(f195,plain,(
    ! [X1] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_subset_1(X1,X1)
      | ~ r1_tarski(X1,X1) ) ),
    inference(superposition,[],[f87,f105])).

fof(f105,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    inference(forward_demodulation,[],[f82,f80])).

fof(f80,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f78,f46])).

fof(f46,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f78,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(resolution,[],[f60,f45])).

fof(f45,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f82,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) ),
    inference(resolution,[],[f61,f45])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f87,plain,(
    ! [X2,X1] :
      ( ~ v1_xboole_0(k3_subset_1(X2,X1))
      | ~ v1_subset_1(X1,X2)
      | ~ r1_tarski(X1,X2) ) ),
    inference(resolution,[],[f71,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_subset_1(X1,X0)
      | ~ v1_xboole_0(k3_subset_1(X0,X1)) ) ),
    inference(global_subsumption,[],[f53,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(k3_subset_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X0))
        & v1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tex_2)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0)
      | ~ v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ~ v1_subset_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_subset_1)).

fof(f72,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f59,f46])).

fof(f59,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f44,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f326,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f39,f320])).

fof(f320,plain,
    ( sK1 = u1_struct_0(sK0)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl3_12
  <=> sK1 = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f39,plain,(
    v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f321,plain,
    ( ~ spl3_9
    | ~ spl3_1
    | spl3_12
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f319,f116,f171,f65,f162])).

fof(f162,plain,
    ( spl3_9
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f65,plain,
    ( spl3_1
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f116,plain,
    ( spl3_5
  <=> u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f319,plain,
    ( sK1 = u1_struct_0(sK0)
    | ~ v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f234,f117])).

fof(f117,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f116])).

fof(f234,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | sK1 = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f230,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,u1_struct_0(X0))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f48,f63])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f230,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(superposition,[],[f59,f218])).

fof(f218,plain,(
    sK1 = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(superposition,[],[f185,f84])).

fof(f84,plain,(
    sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(forward_demodulation,[],[f81,f77])).

fof(f77,plain,(
    k4_xboole_0(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),sK1) ),
    inference(resolution,[],[f60,f37])).

fof(f81,plain,(
    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f61,f37])).

fof(f185,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_subset_1(X0,k4_xboole_0(X0,X1)) ),
    inference(resolution,[],[f79,f59])).

fof(f79,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X2,X1)
      | k4_xboole_0(X1,X2) = k3_subset_1(X1,X2) ) ),
    inference(resolution,[],[f60,f63])).

fof(f318,plain,(
    spl3_16 ),
    inference(avatar_contradiction_clause,[],[f314])).

fof(f314,plain,
    ( $false
    | spl3_16 ),
    inference(resolution,[],[f311,f42])).

fof(f311,plain,
    ( ~ v3_tdlat_3(sK0)
    | spl3_16 ),
    inference(avatar_component_clause,[],[f310])).

fof(f310,plain,
    ( spl3_16
  <=> v3_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f313,plain,
    ( ~ spl3_9
    | ~ spl3_16
    | ~ spl3_10
    | ~ spl3_7
    | spl3_6 ),
    inference(avatar_split_clause,[],[f304,f124,f129,f165,f310,f162])).

fof(f165,plain,
    ( spl3_10
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f129,plain,
    ( spl3_7
  <=> v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f124,plain,
    ( spl3_6
  <=> v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f304,plain,
    ( ~ v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v3_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | spl3_6 ),
    inference(resolution,[],[f239,f125])).

fof(f125,plain,
    ( ~ v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f124])).

fof(f239,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k4_xboole_0(u1_struct_0(X0),X1),X0)
      | ~ v4_pre_topc(k4_xboole_0(u1_struct_0(X0),X1),X0)
      | ~ v2_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f144,f59])).

fof(f144,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | v3_pre_topc(X1,X0)
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f55,f63])).

fof(f179,plain,(
    spl3_10 ),
    inference(avatar_contradiction_clause,[],[f178])).

fof(f178,plain,
    ( $false
    | spl3_10 ),
    inference(resolution,[],[f166,f41])).

fof(f166,plain,
    ( ~ v2_pre_topc(sK0)
    | spl3_10 ),
    inference(avatar_component_clause,[],[f165])).

fof(f175,plain,(
    spl3_9 ),
    inference(avatar_contradiction_clause,[],[f174])).

fof(f174,plain,
    ( $false
    | spl3_9 ),
    inference(resolution,[],[f163,f43])).

fof(f163,plain,
    ( ~ l1_pre_topc(sK0)
    | spl3_9 ),
    inference(avatar_component_clause,[],[f162])).

fof(f143,plain,(
    spl3_8 ),
    inference(avatar_contradiction_clause,[],[f142])).

fof(f142,plain,
    ( $false
    | spl3_8 ),
    inference(resolution,[],[f141,f59])).

fof(f141,plain,
    ( ~ r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | spl3_8 ),
    inference(resolution,[],[f133,f63])).

fof(f133,plain,
    ( ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_8 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl3_8
  <=> m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f135,plain,
    ( spl3_7
    | ~ spl3_8
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f127,f68,f132,f129])).

fof(f68,plain,
    ( spl3_2
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f127,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) ),
    inference(global_subsumption,[],[f43,f120])).

fof(f120,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) ),
    inference(superposition,[],[f51,f84])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

fof(f126,plain,
    ( spl3_1
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f122,f124,f65])).

fof(f122,plain,
    ( ~ v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | v4_pre_topc(sK1,sK0) ),
    inference(global_subsumption,[],[f43,f37,f119])).

fof(f119,plain,
    ( ~ v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v4_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f51,f77])).

fof(f118,plain,
    ( ~ spl3_4
    | spl3_5 ),
    inference(avatar_split_clause,[],[f111,f116,f113])).

fof(f111,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ v1_tops_1(sK1,sK0) ),
    inference(global_subsumption,[],[f43,f108])).

fof(f108,plain,
    ( ~ l1_pre_topc(sK0)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ v1_tops_1(sK1,sK0) ),
    inference(resolution,[],[f50,f37])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | u1_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).

fof(f70,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f36,f68,f65])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:45:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.44  % (27946)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.46  % (27953)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.47  % (27961)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.47  % (27961)Refutation not found, incomplete strategy% (27961)------------------------------
% 0.22/0.47  % (27961)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (27953)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % (27961)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (27961)Memory used [KB]: 6140
% 0.22/0.48  % (27961)Time elapsed: 0.049 s
% 0.22/0.48  % (27961)------------------------------
% 0.22/0.48  % (27961)------------------------------
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f473,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f70,f118,f126,f135,f143,f175,f179,f313,f318,f321,f443,f472])).
% 0.22/0.48  fof(f472,plain,(
% 0.22/0.48    spl3_4),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f471])).
% 0.22/0.48  fof(f471,plain,(
% 0.22/0.48    $false | spl3_4),
% 0.22/0.48    inference(resolution,[],[f465,f114])).
% 0.22/0.48  fof(f114,plain,(
% 0.22/0.48    ~v1_tops_1(sK1,sK0) | spl3_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f113])).
% 0.22/0.48  fof(f113,plain,(
% 0.22/0.48    spl3_4 <=> v1_tops_1(sK1,sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.48  fof(f465,plain,(
% 0.22/0.48    v1_tops_1(sK1,sK0)),
% 0.22/0.48    inference(global_subsumption,[],[f448])).
% 0.22/0.48  fof(f448,plain,(
% 0.22/0.48    v1_tops_1(sK1,sK0)),
% 0.22/0.48    inference(global_subsumption,[],[f154,f447])).
% 0.22/0.48  fof(f447,plain,(
% 0.22/0.48    v3_pre_topc(sK1,sK0)),
% 0.22/0.48    inference(global_subsumption,[],[f446])).
% 0.22/0.48  fof(f446,plain,(
% 0.22/0.48    v3_pre_topc(sK1,sK0)),
% 0.22/0.48    inference(global_subsumption,[],[f445])).
% 0.22/0.48  fof(f445,plain,(
% 0.22/0.48    v3_pre_topc(sK1,sK0)),
% 0.22/0.48    inference(global_subsumption,[],[f444])).
% 0.22/0.48  fof(f444,plain,(
% 0.22/0.48    v3_pre_topc(sK1,sK0)),
% 0.22/0.48    inference(global_subsumption,[],[f36,f41,f42,f43,f146])).
% 0.22/0.48  fof(f146,plain,(
% 0.22/0.48    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~v4_pre_topc(sK1,sK0) | v3_pre_topc(sK1,sK0) | ~v3_tdlat_3(sK0)),
% 0.22/0.48    inference(resolution,[],[f55,f37])).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.48    inference(cnf_transformation,[],[f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f17])).
% 0.22/0.48  fof(f17,negated_conjecture,(
% 0.22/0.48    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)))))),
% 0.22/0.48    inference(negated_conjecture,[],[f16])).
% 0.22/0.48  fof(f16,conjecture,(
% 0.22/0.48    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_tex_2)).
% 0.22/0.48  fof(f55,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0) | ~v3_tdlat_3(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f30])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.48    inference(flattening,[],[f29])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : ((v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f14])).
% 0.22/0.48  fof(f14,axiom,(
% 0.22/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v3_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => v3_pre_topc(X1,X0)))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tdlat_3)).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    l1_pre_topc(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f21])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    v3_tdlat_3(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f21])).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    v2_pre_topc(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f21])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    v3_pre_topc(sK1,sK0) | v4_pre_topc(sK1,sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f21])).
% 0.22/0.48  fof(f154,plain,(
% 0.22/0.48    ~v3_pre_topc(sK1,sK0) | v1_tops_1(sK1,sK0)),
% 0.22/0.48    inference(global_subsumption,[],[f40,f41,f43,f38,f151])).
% 0.22/0.48  fof(f151,plain,(
% 0.22/0.48    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v3_pre_topc(sK1,sK0) | ~v3_tex_2(sK1,sK0) | v1_tops_1(sK1,sK0)),
% 0.22/0.48    inference(resolution,[],[f54,f37])).
% 0.22/0.48  fof(f54,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v3_pre_topc(X1,X0) | ~v3_tex_2(X1,X0) | v1_tops_1(X1,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f28])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f27])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) | (~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f15])).
% 0.22/0.48  fof(f15,axiom,(
% 0.22/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tex_2(X1,X0) & v3_pre_topc(X1,X0)) => v1_tops_1(X1,X0))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_tex_2)).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    v3_tex_2(sK1,sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f21])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    ~v2_struct_0(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f21])).
% 0.22/0.48  fof(f443,plain,(
% 0.22/0.48    ~spl3_12),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f442])).
% 0.22/0.48  fof(f442,plain,(
% 0.22/0.48    $false | ~spl3_12),
% 0.22/0.48    inference(resolution,[],[f326,f206])).
% 0.22/0.48  fof(f206,plain,(
% 0.22/0.48    ( ! [X1] : (~v1_subset_1(X1,X1)) )),
% 0.22/0.48    inference(global_subsumption,[],[f44,f72,f195])).
% 0.22/0.48  fof(f195,plain,(
% 0.22/0.48    ( ! [X1] : (~v1_xboole_0(k1_xboole_0) | ~v1_subset_1(X1,X1) | ~r1_tarski(X1,X1)) )),
% 0.22/0.48    inference(superposition,[],[f87,f105])).
% 0.22/0.48  fof(f105,plain,(
% 0.22/0.48    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0)) )),
% 0.22/0.48    inference(forward_demodulation,[],[f82,f80])).
% 0.22/0.48  fof(f80,plain,(
% 0.22/0.48    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 0.22/0.48    inference(forward_demodulation,[],[f78,f46])).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.48  fof(f78,plain,(
% 0.22/0.48    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0)) )),
% 0.22/0.48    inference(resolution,[],[f60,f45])).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.48  fof(f60,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f31])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.22/0.48  fof(f82,plain,(
% 0.22/0.48    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0))) )),
% 0.22/0.48    inference(resolution,[],[f61,f45])).
% 0.22/0.48  fof(f61,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.22/0.48    inference(cnf_transformation,[],[f32])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.22/0.48  fof(f87,plain,(
% 0.22/0.48    ( ! [X2,X1] : (~v1_xboole_0(k3_subset_1(X2,X1)) | ~v1_subset_1(X1,X2) | ~r1_tarski(X1,X2)) )),
% 0.22/0.48    inference(resolution,[],[f71,f63])).
% 0.22/0.48  fof(f63,plain,(
% 0.22/0.48    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f35])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.22/0.48    inference(unused_predicate_definition_removal,[],[f8])).
% 0.22/0.48  fof(f8,axiom,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.48  fof(f71,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_subset_1(X1,X0) | ~v1_xboole_0(k3_subset_1(X0,X1))) )),
% 0.22/0.48    inference(global_subsumption,[],[f53,f62])).
% 0.22/0.48  fof(f62,plain,(
% 0.22/0.48    ( ! [X0,X1] : (v1_xboole_0(X0) | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(k3_subset_1(X0,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f34])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ! [X0,X1] : (~v1_xboole_0(k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.48    inference(flattening,[],[f33])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    ! [X0,X1] : (~v1_xboole_0(k3_subset_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f13])).
% 0.22/0.48  fof(f13,axiom,(
% 0.22/0.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(X0)) & v1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k3_subset_1(X0,X1)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tex_2)).
% 0.22/0.48  fof(f53,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0) | ~v1_subset_1(X1,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f26])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~v1_subset_1(X1,X0)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_subset_1)).
% 0.22/0.48  fof(f72,plain,(
% 0.22/0.48    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.22/0.48    inference(superposition,[],[f59,f46])).
% 0.22/0.48  fof(f59,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    v1_xboole_0(k1_xboole_0)),
% 0.22/0.48    inference(cnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    v1_xboole_0(k1_xboole_0)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.48  fof(f326,plain,(
% 0.22/0.48    v1_subset_1(sK1,sK1) | ~spl3_12),
% 0.22/0.48    inference(backward_demodulation,[],[f39,f320])).
% 0.22/0.48  fof(f320,plain,(
% 0.22/0.48    sK1 = u1_struct_0(sK0) | ~spl3_12),
% 0.22/0.48    inference(avatar_component_clause,[],[f171])).
% 0.22/0.48  fof(f171,plain,(
% 0.22/0.48    spl3_12 <=> sK1 = u1_struct_0(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.48    inference(cnf_transformation,[],[f21])).
% 0.22/0.48  fof(f321,plain,(
% 0.22/0.48    ~spl3_9 | ~spl3_1 | spl3_12 | ~spl3_5),
% 0.22/0.48    inference(avatar_split_clause,[],[f319,f116,f171,f65,f162])).
% 0.22/0.48  fof(f162,plain,(
% 0.22/0.48    spl3_9 <=> l1_pre_topc(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.48  fof(f65,plain,(
% 0.22/0.48    spl3_1 <=> v4_pre_topc(sK1,sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.48  fof(f116,plain,(
% 0.22/0.48    spl3_5 <=> u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.48  fof(f319,plain,(
% 0.22/0.48    sK1 = u1_struct_0(sK0) | ~v4_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~spl3_5),
% 0.22/0.48    inference(forward_demodulation,[],[f234,f117])).
% 0.22/0.48  fof(f117,plain,(
% 0.22/0.48    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~spl3_5),
% 0.22/0.48    inference(avatar_component_clause,[],[f116])).
% 0.22/0.48  fof(f234,plain,(
% 0.22/0.48    ~v4_pre_topc(sK1,sK0) | sK1 = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0)),
% 0.22/0.48    inference(resolution,[],[f230,f94])).
% 0.22/0.48  fof(f94,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r1_tarski(X1,u1_struct_0(X0)) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~l1_pre_topc(X0)) )),
% 0.22/0.48    inference(resolution,[],[f48,f63])).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1) )),
% 0.22/0.48    inference(cnf_transformation,[],[f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.48    inference(flattening,[],[f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,axiom,(
% 0.22/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.22/0.48  fof(f230,plain,(
% 0.22/0.48    r1_tarski(sK1,u1_struct_0(sK0))),
% 0.22/0.48    inference(superposition,[],[f59,f218])).
% 0.22/0.48  fof(f218,plain,(
% 0.22/0.48    sK1 = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))),
% 0.22/0.48    inference(superposition,[],[f185,f84])).
% 0.22/0.48  fof(f84,plain,(
% 0.22/0.48    sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))),
% 0.22/0.48    inference(forward_demodulation,[],[f81,f77])).
% 0.22/0.48  fof(f77,plain,(
% 0.22/0.48    k4_xboole_0(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),sK1)),
% 0.22/0.48    inference(resolution,[],[f60,f37])).
% 0.22/0.48  fof(f81,plain,(
% 0.22/0.48    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.22/0.48    inference(resolution,[],[f61,f37])).
% 0.22/0.48  fof(f185,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_subset_1(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.48    inference(resolution,[],[f79,f59])).
% 0.22/0.48  fof(f79,plain,(
% 0.22/0.48    ( ! [X2,X1] : (~r1_tarski(X2,X1) | k4_xboole_0(X1,X2) = k3_subset_1(X1,X2)) )),
% 0.22/0.48    inference(resolution,[],[f60,f63])).
% 0.22/0.48  fof(f318,plain,(
% 0.22/0.48    spl3_16),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f314])).
% 0.22/0.48  fof(f314,plain,(
% 0.22/0.48    $false | spl3_16),
% 0.22/0.48    inference(resolution,[],[f311,f42])).
% 0.22/0.48  fof(f311,plain,(
% 0.22/0.48    ~v3_tdlat_3(sK0) | spl3_16),
% 0.22/0.48    inference(avatar_component_clause,[],[f310])).
% 0.22/0.48  fof(f310,plain,(
% 0.22/0.48    spl3_16 <=> v3_tdlat_3(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.22/0.48  fof(f313,plain,(
% 0.22/0.48    ~spl3_9 | ~spl3_16 | ~spl3_10 | ~spl3_7 | spl3_6),
% 0.22/0.48    inference(avatar_split_clause,[],[f304,f124,f129,f165,f310,f162])).
% 0.22/0.48  fof(f165,plain,(
% 0.22/0.48    spl3_10 <=> v2_pre_topc(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.48  fof(f129,plain,(
% 0.22/0.48    spl3_7 <=> v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.48  fof(f124,plain,(
% 0.22/0.48    spl3_6 <=> v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.48  fof(f304,plain,(
% 0.22/0.48    ~v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | ~v2_pre_topc(sK0) | ~v3_tdlat_3(sK0) | ~l1_pre_topc(sK0) | spl3_6),
% 0.22/0.48    inference(resolution,[],[f239,f125])).
% 0.22/0.48  fof(f125,plain,(
% 0.22/0.48    ~v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | spl3_6),
% 0.22/0.48    inference(avatar_component_clause,[],[f124])).
% 0.22/0.48  fof(f239,plain,(
% 0.22/0.48    ( ! [X0,X1] : (v3_pre_topc(k4_xboole_0(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(k4_xboole_0(u1_struct_0(X0),X1),X0) | ~v2_pre_topc(X0) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.48    inference(resolution,[],[f144,f59])).
% 0.22/0.48  fof(f144,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r1_tarski(X1,u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.48    inference(resolution,[],[f55,f63])).
% 0.22/0.48  fof(f179,plain,(
% 0.22/0.48    spl3_10),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f178])).
% 0.22/0.48  fof(f178,plain,(
% 0.22/0.48    $false | spl3_10),
% 0.22/0.48    inference(resolution,[],[f166,f41])).
% 0.22/0.48  fof(f166,plain,(
% 0.22/0.48    ~v2_pre_topc(sK0) | spl3_10),
% 0.22/0.48    inference(avatar_component_clause,[],[f165])).
% 0.22/0.48  fof(f175,plain,(
% 0.22/0.48    spl3_9),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f174])).
% 0.22/0.48  fof(f174,plain,(
% 0.22/0.48    $false | spl3_9),
% 0.22/0.48    inference(resolution,[],[f163,f43])).
% 0.22/0.48  fof(f163,plain,(
% 0.22/0.48    ~l1_pre_topc(sK0) | spl3_9),
% 0.22/0.48    inference(avatar_component_clause,[],[f162])).
% 0.22/0.48  fof(f143,plain,(
% 0.22/0.48    spl3_8),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f142])).
% 0.22/0.48  fof(f142,plain,(
% 0.22/0.48    $false | spl3_8),
% 0.22/0.48    inference(resolution,[],[f141,f59])).
% 0.22/0.48  fof(f141,plain,(
% 0.22/0.48    ~r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | spl3_8),
% 0.22/0.48    inference(resolution,[],[f133,f63])).
% 0.22/0.48  fof(f133,plain,(
% 0.22/0.48    ~m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_8),
% 0.22/0.48    inference(avatar_component_clause,[],[f132])).
% 0.22/0.48  fof(f132,plain,(
% 0.22/0.48    spl3_8 <=> m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.48  fof(f135,plain,(
% 0.22/0.48    spl3_7 | ~spl3_8 | ~spl3_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f127,f68,f132,f129])).
% 0.22/0.48  fof(f68,plain,(
% 0.22/0.48    spl3_2 <=> v3_pre_topc(sK1,sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.48  fof(f127,plain,(
% 0.22/0.48    ~v3_pre_topc(sK1,sK0) | ~m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)),
% 0.22/0.48    inference(global_subsumption,[],[f43,f120])).
% 0.22/0.48  fof(f120,plain,(
% 0.22/0.48    ~v3_pre_topc(sK1,sK0) | ~m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)),
% 0.22/0.48    inference(superposition,[],[f51,f84])).
% 0.22/0.48  fof(f51,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v4_pre_topc(X1,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f25])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,axiom,(
% 0.22/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).
% 0.22/0.48  fof(f126,plain,(
% 0.22/0.48    spl3_1 | ~spl3_6),
% 0.22/0.48    inference(avatar_split_clause,[],[f122,f124,f65])).
% 0.22/0.48  fof(f122,plain,(
% 0.22/0.48    ~v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | v4_pre_topc(sK1,sK0)),
% 0.22/0.48    inference(global_subsumption,[],[f43,f37,f119])).
% 0.22/0.48  fof(f119,plain,(
% 0.22/0.48    ~v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v4_pre_topc(sK1,sK0)),
% 0.22/0.48    inference(superposition,[],[f51,f77])).
% 0.22/0.48  fof(f118,plain,(
% 0.22/0.48    ~spl3_4 | spl3_5),
% 0.22/0.48    inference(avatar_split_clause,[],[f111,f116,f113])).
% 0.22/0.48  fof(f111,plain,(
% 0.22/0.48    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~v1_tops_1(sK1,sK0)),
% 0.22/0.48    inference(global_subsumption,[],[f43,f108])).
% 0.22/0.48  fof(f108,plain,(
% 0.22/0.48    ~l1_pre_topc(sK0) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~v1_tops_1(sK1,sK0)),
% 0.22/0.48    inference(resolution,[],[f50,f37])).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f24])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f12])).
% 0.22/0.48  fof(f12,axiom,(
% 0.22/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).
% 0.22/0.48  fof(f70,plain,(
% 0.22/0.48    spl3_1 | spl3_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f36,f68,f65])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (27953)------------------------------
% 0.22/0.48  % (27953)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (27953)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (27953)Memory used [KB]: 11001
% 0.22/0.48  % (27953)Time elapsed: 0.071 s
% 0.22/0.48  % (27953)------------------------------
% 0.22/0.48  % (27953)------------------------------
% 0.22/0.48  % (27957)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.22/0.49  % (27940)Success in time 0.119 s
%------------------------------------------------------------------------------
