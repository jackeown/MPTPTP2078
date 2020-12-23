%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:52 EST 2020

% Result     : Theorem 1.73s
% Output     : Refutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :  246 (28594 expanded)
%              Number of leaves         :   26 (6089 expanded)
%              Depth                    :   53
%              Number of atoms          :  866 (121778 expanded)
%              Number of equality atoms :  131 (10776 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1017,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1016,f962])).

fof(f962,plain,(
    ~ v3_tex_2(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f893,f173])).

fof(f173,plain,(
    ! [X1] : ~ v1_subset_1(X1,X1) ),
    inference(subsumption_resolution,[],[f163,f166])).

fof(f166,plain,(
    ! [X0] : m1_subset_1(X0,k9_setfam_1(X0)) ),
    inference(forward_demodulation,[],[f132,f130])).

fof(f130,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f84,f128])).

fof(f128,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f88,f83])).

fof(f83,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f88,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

fof(f84,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f132,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,k1_xboole_0),k9_setfam_1(X0)) ),
    inference(definition_unfolding,[],[f87,f128,f85])).

fof(f85,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(f87,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f163,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k9_setfam_1(X1))
      | ~ v1_subset_1(X1,X1) ) ),
    inference(equality_resolution,[],[f154])).

fof(f154,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k9_setfam_1(X0))
      | X0 != X1
      | ~ v1_subset_1(X1,X0) ) ),
    inference(definition_unfolding,[],[f122,f85])).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 != X1
      | ~ v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f893,plain,
    ( v1_subset_1(k1_xboole_0,k1_xboole_0)
    | ~ v3_tex_2(k1_xboole_0,sK0) ),
    inference(backward_demodulation,[],[f850,f861])).

fof(f861,plain,(
    k1_xboole_0 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f860,f178])).

fof(f178,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f177,f82])).

fof(f82,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f177,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f119,f81])).

fof(f81,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f860,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = u1_struct_0(sK0) ),
    inference(forward_demodulation,[],[f785,f775])).

fof(f775,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f772,f173])).

fof(f772,plain,
    ( v1_subset_1(sK1,sK1)
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f771])).

fof(f771,plain,
    ( v1_subset_1(sK1,sK1)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f720,f692])).

fof(f692,plain,
    ( sK1 = u1_struct_0(sK0)
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f686])).

fof(f686,plain,
    ( sK1 = u1_struct_0(sK0)
    | k1_xboole_0 = sK1
    | sK1 = u1_struct_0(sK0) ),
    inference(superposition,[],[f683,f435])).

fof(f435,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | sK1 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f434,f181])).

fof(f181,plain,(
    m1_subset_1(sK1,u1_pre_topc(sK0)) ),
    inference(backward_demodulation,[],[f129,f180])).

fof(f180,plain,(
    k9_setfam_1(u1_struct_0(sK0)) = u1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f179,f80])).

fof(f80,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_tex_2(X1,X0)
            <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f32])).

fof(f32,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tex_2)).

fof(f179,plain,
    ( k9_setfam_1(u1_struct_0(sK0)) = u1_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f93,f79])).

fof(f79,plain,(
    v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f93,plain,(
    ! [X0] :
      ( ~ v1_tdlat_3(X0)
      | u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
      <=> u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tdlat_3)).

fof(f129,plain,(
    m1_subset_1(sK1,k9_setfam_1(u1_struct_0(sK0))) ),
    inference(definition_unfolding,[],[f76,f85])).

fof(f76,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f434,plain,
    ( ~ m1_subset_1(sK1,u1_pre_topc(sK0))
    | sK1 = u1_struct_0(sK0)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(forward_demodulation,[],[f433,f180])).

fof(f433,plain,
    ( sK1 = u1_struct_0(sK0)
    | ~ m1_subset_1(sK1,k9_setfam_1(u1_struct_0(sK0)))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f432,f80])).

fof(f432,plain,
    ( sK1 = u1_struct_0(sK0)
    | ~ m1_subset_1(sK1,k9_setfam_1(u1_struct_0(sK0)))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f431,f137])).

fof(f137,plain,(
    ! [X0,X1] :
      ( ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | u1_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f99,f85])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).

fof(f431,plain,
    ( v1_tops_1(sK1,sK0)
    | sK1 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f430,f181])).

fof(f430,plain,
    ( ~ m1_subset_1(sK1,u1_pre_topc(sK0))
    | v1_tops_1(sK1,sK0)
    | sK1 = u1_struct_0(sK0) ),
    inference(forward_demodulation,[],[f429,f180])).

fof(f429,plain,
    ( ~ m1_subset_1(sK1,k9_setfam_1(u1_struct_0(sK0)))
    | v1_tops_1(sK1,sK0)
    | sK1 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f428,f77])).

fof(f77,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f428,plain,
    ( ~ m1_subset_1(sK1,k9_setfam_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | v1_tops_1(sK1,sK0)
    | sK1 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f427,f237])).

fof(f237,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f234,f181])).

fof(f234,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_pre_topc(sK0))
      | v3_pre_topc(X0,sK0) ) ),
    inference(forward_demodulation,[],[f233,f180])).

fof(f233,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(sK0)))
      | v3_pre_topc(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f232,f80])).

fof(f232,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(sK0)))
      | v3_pre_topc(X0,sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f170,f79])).

fof(f170,plain,(
    ! [X0,X1] :
      ( ~ v1_tdlat_3(X0)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f150,f91])).

fof(f91,plain,(
    ! [X0] :
      ( ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tdlat_3)).

fof(f150,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | v3_pre_topc(X1,X0)
      | ~ v1_tdlat_3(X0) ) ),
    inference(definition_unfolding,[],[f114,f85])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(X1,X0)
      | ~ v1_tdlat_3(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tdlat_3)).

fof(f427,plain,
    ( ~ m1_subset_1(sK1,k9_setfam_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | v1_tops_1(sK1,sK0)
    | sK1 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f426,f80])).

fof(f426,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k9_setfam_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | v1_tops_1(sK1,sK0)
    | sK1 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f425,f78])).

fof(f78,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f425,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k9_setfam_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | v1_tops_1(sK1,sK0)
    | sK1 = u1_struct_0(sK0) ),
    inference(resolution,[],[f141,f201])).

fof(f201,plain,
    ( v3_tex_2(sK1,sK0)
    | sK1 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f198,f181])).

fof(f198,plain,
    ( sK1 = u1_struct_0(sK0)
    | ~ m1_subset_1(sK1,u1_pre_topc(sK0))
    | v3_tex_2(sK1,sK0) ),
    inference(resolution,[],[f191,f74])).

fof(f74,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f191,plain,(
    ! [X0] :
      ( v1_subset_1(X0,u1_struct_0(sK0))
      | u1_struct_0(sK0) = X0
      | ~ m1_subset_1(X0,u1_pre_topc(sK0)) ) ),
    inference(superposition,[],[f155,f180])).

fof(f155,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k9_setfam_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(definition_unfolding,[],[f121,f85])).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f141,plain,(
    ! [X0,X1] :
      ( ~ v3_tex_2(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | v2_struct_0(X0)
      | v1_tops_1(X1,X0) ) ),
    inference(definition_unfolding,[],[f104,f85])).

fof(f104,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ v3_tex_2(X1,X0)
      | v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
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

fof(f683,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f682,f181])).

fof(f682,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_subset_1(sK1,u1_pre_topc(sK0))
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f681,f258])).

fof(f258,plain,(
    ! [X0] :
      ( ~ v4_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,u1_pre_topc(sK0))
      | k2_pre_topc(sK0,X0) = X0 ) ),
    inference(forward_demodulation,[],[f257,f180])).

fof(f257,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(sK0)))
      | ~ v4_pre_topc(X0,sK0)
      | k2_pre_topc(sK0,X0) = X0 ) ),
    inference(resolution,[],[f135,f80])).

fof(f135,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(definition_unfolding,[],[f97,f85])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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

fof(f681,plain,
    ( v4_pre_topc(sK1,sK0)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f677,f194])).

fof(f194,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f193,f131])).

fof(f131,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k9_setfam_1(X0)) ),
    inference(definition_unfolding,[],[f86,f83,f85])).

fof(f86,plain,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_subset_1)).

fof(f193,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k9_setfam_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f190,f139])).

fof(f139,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k9_setfam_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f100,f85])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ~ v1_subset_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_subset_1)).

fof(f190,plain,(
    ! [X1] :
      ( v1_subset_1(k1_xboole_0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f155,f131])).

fof(f677,plain,
    ( v4_pre_topc(sK1,sK0)
    | v1_xboole_0(sK1)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f670,f358])).

fof(f358,plain,
    ( sK1 = u1_struct_0(sK3(sK0,sK1))
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f354,f194])).

fof(f354,plain,
    ( v1_xboole_0(sK1)
    | sK1 = u1_struct_0(sK3(sK0,sK1)) ),
    inference(resolution,[],[f350,f181])).

fof(f350,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_pre_topc(sK0))
      | v1_xboole_0(X0)
      | u1_struct_0(sK3(sK0,X0)) = X0 ) ),
    inference(forward_demodulation,[],[f349,f180])).

fof(f349,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(sK0)))
      | u1_struct_0(sK3(sK0,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f347,f77])).

fof(f347,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(sK0)))
      | u1_struct_0(sK3(sK0,X0)) = X0 ) ),
    inference(resolution,[],[f145,f80])).

fof(f145,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | u1_struct_0(sK3(X0,X1)) = X1 ) ),
    inference(definition_unfolding,[],[f113,f85])).

fof(f113,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(sK3(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tsep_1)).

fof(f670,plain,
    ( v4_pre_topc(u1_struct_0(sK3(sK0,sK1)),sK0)
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f665,f181])).

fof(f665,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_pre_topc(sK0))
      | v4_pre_topc(u1_struct_0(sK3(sK0,X0)),sK0)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f664,f281])).

fof(f281,plain,(
    ! [X0] :
      ( m1_pre_topc(sK3(sK0,X0),sK0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,u1_pre_topc(sK0)) ) ),
    inference(forward_demodulation,[],[f280,f180])).

fof(f280,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(sK0)))
      | m1_pre_topc(sK3(sK0,X0),sK0) ) ),
    inference(subsumption_resolution,[],[f279,f77])).

fof(f279,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(sK0)))
      | m1_pre_topc(sK3(sK0,X0),sK0) ) ),
    inference(resolution,[],[f146,f80])).

fof(f146,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | m1_pre_topc(sK3(X0,X1),X0) ) ),
    inference(definition_unfolding,[],[f112,f85])).

fof(f112,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_pre_topc(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f664,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_pre_topc(sK0))
      | v4_pre_topc(u1_struct_0(sK3(sK0,X0)),sK0)
      | v1_xboole_0(X0)
      | ~ m1_pre_topc(sK3(sK0,X0),sK0) ) ),
    inference(subsumption_resolution,[],[f663,f77])).

fof(f663,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_pre_topc(sK0))
      | v4_pre_topc(u1_struct_0(sK3(sK0,X0)),sK0)
      | v1_xboole_0(X0)
      | ~ m1_pre_topc(sK3(sK0,X0),sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f662,f80])).

fof(f662,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_pre_topc(sK0))
      | v4_pre_topc(u1_struct_0(sK3(sK0,X0)),sK0)
      | v1_xboole_0(X0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(sK3(sK0,X0),sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f661,f79])).

fof(f661,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_pre_topc(sK0))
      | v4_pre_topc(u1_struct_0(sK3(sK0,X0)),sK0)
      | v1_xboole_0(X0)
      | ~ v1_tdlat_3(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(sK3(sK0,X0),sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f290,f168])).

fof(f168,plain,(
    ! [X0,X1] :
      ( v1_borsuk_1(X1,X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f101,f91])).

fof(f101,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v1_borsuk_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tdlat_3(X1)
            & v1_borsuk_1(X1,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tdlat_3(X1)
            & v1_borsuk_1(X1,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tdlat_3(X1)
            & v1_borsuk_1(X1,X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tdlat_3(X1)
            & v1_tsep_1(X1,X0)
            & v1_borsuk_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_tdlat_3)).

fof(f290,plain,(
    ! [X0] :
      ( ~ v1_borsuk_1(sK3(sK0,X0),sK0)
      | ~ m1_subset_1(X0,u1_pre_topc(sK0))
      | v4_pre_topc(u1_struct_0(sK3(sK0,X0)),sK0)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f289,f78])).

fof(f289,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X0,u1_pre_topc(sK0))
      | v4_pre_topc(u1_struct_0(sK3(sK0,X0)),sK0)
      | ~ v1_borsuk_1(sK3(sK0,X0),sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f285,f80])).

fof(f285,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X0,u1_pre_topc(sK0))
      | ~ l1_pre_topc(sK0)
      | v4_pre_topc(u1_struct_0(sK3(sK0,X0)),sK0)
      | ~ v1_borsuk_1(sK3(sK0,X0),sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f281,f172])).

fof(f172,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(u1_struct_0(X1),X0)
      | ~ v1_borsuk_1(X1,X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f162,f134])).

fof(f134,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(u1_struct_0(X1),k9_setfam_1(u1_struct_0(X0))) ) ),
    inference(definition_unfolding,[],[f95,f85])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f162,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(u1_struct_0(X1),k9_setfam_1(u1_struct_0(X0)))
      | v4_pre_topc(u1_struct_0(X1),X0)
      | ~ v1_borsuk_1(X1,X0)
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(equality_resolution,[],[f152])).

fof(f152,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k9_setfam_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | v4_pre_topc(X2,X0)
      | ~ v1_borsuk_1(X1,X0)
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(definition_unfolding,[],[f117,f85])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | v4_pre_topc(X2,X0)
      | ~ v1_borsuk_1(X1,X0)
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) )
              <=> v4_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) )
              <=> v4_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_borsuk_1(X1,X0) )
                <=> v4_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tsep_1)).

fof(f720,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f704,f75])).

fof(f75,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f36])).

fof(f704,plain,
    ( v3_tex_2(sK1,sK0)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f703,f181])).

fof(f703,plain,
    ( ~ m1_subset_1(sK1,u1_pre_topc(sK0))
    | k1_xboole_0 = sK1
    | v3_tex_2(sK1,sK0) ),
    inference(forward_demodulation,[],[f702,f180])).

fof(f702,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_subset_1(sK1,k9_setfam_1(u1_struct_0(sK0)))
    | v3_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f701,f255])).

fof(f255,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(resolution,[],[f252,f181])).

fof(f252,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_pre_topc(sK0))
      | v2_tex_2(X0,sK0) ) ),
    inference(forward_demodulation,[],[f251,f180])).

fof(f251,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(sK0)))
      | v2_tex_2(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f250,f80])).

fof(f250,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(sK0)))
      | v2_tex_2(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f249,f77])).

fof(f249,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(sK0)))
      | v2_tex_2(X0,sK0) ) ),
    inference(resolution,[],[f169,f79])).

fof(f169,plain,(
    ! [X0,X1] :
      ( ~ v1_tdlat_3(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | v2_tex_2(X1,X0) ) ),
    inference(subsumption_resolution,[],[f140,f91])).

fof(f140,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | v2_tex_2(X1,X0) ) ),
    inference(definition_unfolding,[],[f103,f85])).

fof(f103,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

fof(f701,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_subset_1(sK1,k9_setfam_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | v3_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f700,f77])).

fof(f700,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_subset_1(sK1,k9_setfam_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ v2_tex_2(sK1,sK0)
    | v3_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f699,f80])).

fof(f699,plain,
    ( k1_xboole_0 = sK1
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k9_setfam_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ v2_tex_2(sK1,sK0)
    | v3_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f697,f78])).

fof(f697,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k9_setfam_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ v2_tex_2(sK1,sK0)
    | v3_tex_2(sK1,sK0) ),
    inference(resolution,[],[f696,f142])).

fof(f142,plain,(
    ! [X0,X1] :
      ( ~ v1_tops_1(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | v2_struct_0(X0)
      | ~ v2_tex_2(X1,X0)
      | v3_tex_2(X1,X0) ) ),
    inference(definition_unfolding,[],[f105,f85])).

fof(f105,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_1(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_tex_2(X1,X0)
              & v1_tops_1(X1,X0) )
           => v3_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tex_2)).

fof(f696,plain,
    ( v1_tops_1(sK1,sK0)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f695,f181])).

fof(f695,plain,
    ( ~ m1_subset_1(sK1,u1_pre_topc(sK0))
    | v1_tops_1(sK1,sK0)
    | k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f694,f180])).

fof(f694,plain,
    ( ~ m1_subset_1(sK1,k9_setfam_1(u1_struct_0(sK0)))
    | v1_tops_1(sK1,sK0)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f693,f692])).

fof(f693,plain,
    ( sK1 != u1_struct_0(sK0)
    | ~ m1_subset_1(sK1,k9_setfam_1(u1_struct_0(sK0)))
    | v1_tops_1(sK1,sK0)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f689,f80])).

fof(f689,plain,
    ( sK1 != u1_struct_0(sK0)
    | ~ m1_subset_1(sK1,k9_setfam_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v1_tops_1(sK1,sK0)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f138,f683])).

fof(f138,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) != k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v1_tops_1(X1,X0) ) ),
    inference(definition_unfolding,[],[f98,f85])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X0) != k2_pre_topc(X0,X1)
      | v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f785,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | ~ v1_xboole_0(sK1) ),
    inference(backward_demodulation,[],[f278,f775])).

fof(f278,plain,
    ( ~ v1_xboole_0(sK1)
    | sK1 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f277,f181])).

fof(f277,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,u1_pre_topc(sK0))
    | sK1 = u1_struct_0(sK0) ),
    inference(resolution,[],[f276,f201])).

fof(f276,plain,(
    ! [X0] :
      ( ~ v3_tex_2(X0,sK0)
      | ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X0,u1_pre_topc(sK0)) ) ),
    inference(forward_demodulation,[],[f275,f180])).

fof(f275,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(sK0)))
      | ~ v3_tex_2(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f274,f80])).

fof(f274,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(sK0)))
      | ~ v3_tex_2(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f273,f77])).

fof(f273,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(sK0)))
      | ~ v3_tex_2(X0,sK0) ) ),
    inference(resolution,[],[f143,f78])).

fof(f143,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ v3_tex_2(X1,X0) ) ),
    inference(definition_unfolding,[],[f106,f85])).

fof(f106,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => ~ v3_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).

fof(f850,plain,
    ( ~ v3_tex_2(k1_xboole_0,sK0)
    | v1_subset_1(k1_xboole_0,u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f777,f775])).

fof(f777,plain,
    ( v1_subset_1(k1_xboole_0,u1_struct_0(sK0))
    | ~ v3_tex_2(sK1,sK0) ),
    inference(backward_demodulation,[],[f75,f775])).

fof(f1016,plain,(
    v3_tex_2(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f1015,f253])).

fof(f253,plain,(
    v2_tex_2(k1_xboole_0,sK0) ),
    inference(resolution,[],[f252,f186])).

fof(f186,plain,(
    m1_subset_1(k1_xboole_0,u1_pre_topc(sK0)) ),
    inference(superposition,[],[f131,f180])).

fof(f1015,plain,
    ( ~ v2_tex_2(k1_xboole_0,sK0)
    | v3_tex_2(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f1014,f77])).

fof(f1014,plain,
    ( v2_struct_0(sK0)
    | ~ v2_tex_2(k1_xboole_0,sK0)
    | v3_tex_2(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f1013,f131])).

fof(f1013,plain,
    ( ~ m1_subset_1(k1_xboole_0,k9_setfam_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ v2_tex_2(k1_xboole_0,sK0)
    | v3_tex_2(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f1012,f80])).

fof(f1012,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(k1_xboole_0,k9_setfam_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ v2_tex_2(k1_xboole_0,sK0)
    | v3_tex_2(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f1010,f78])).

fof(f1010,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(k1_xboole_0,k9_setfam_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ v2_tex_2(k1_xboole_0,sK0)
    | v3_tex_2(k1_xboole_0,sK0) ),
    inference(resolution,[],[f1005,f142])).

fof(f1005,plain,(
    v1_tops_1(k1_xboole_0,sK0) ),
    inference(trivial_inequality_removal,[],[f1004])).

fof(f1004,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v1_tops_1(k1_xboole_0,sK0) ),
    inference(backward_demodulation,[],[f941,f992])).

fof(f992,plain,(
    k1_xboole_0 = sK2(sK0) ),
    inference(resolution,[],[f934,f895])).

fof(f895,plain,(
    m1_subset_1(sK2(sK0),k9_setfam_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f227,f862])).

fof(f862,plain,(
    u1_pre_topc(sK0) = k9_setfam_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f180,f861])).

fof(f227,plain,(
    m1_subset_1(sK2(sK0),u1_pre_topc(sK0)) ),
    inference(forward_demodulation,[],[f226,f180])).

fof(f226,plain,(
    m1_subset_1(sK2(sK0),k9_setfam_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f225,f80])).

fof(f225,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(sK2(sK0),k9_setfam_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f224,f77])).

fof(f224,plain,
    ( v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | m1_subset_1(sK2(sK0),k9_setfam_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f144,f78])).

fof(f144,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(sK2(X0),k9_setfam_1(u1_struct_0(X0))) ) ),
    inference(definition_unfolding,[],[f107,f85])).

fof(f107,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v4_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc7_pre_topc)).

fof(f934,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k9_setfam_1(k1_xboole_0))
      | k1_xboole_0 = X0 ) ),
    inference(forward_demodulation,[],[f933,f862])).

fof(f933,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ m1_subset_1(X0,u1_pre_topc(sK0)) ) ),
    inference(subsumption_resolution,[],[f932,f178])).

fof(f932,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X0,u1_pre_topc(sK0)) ) ),
    inference(forward_demodulation,[],[f867,f861])).

fof(f867,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_pre_topc(sK0)) ) ),
    inference(backward_demodulation,[],[f200,f861])).

fof(f200,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(sK0))
      | u1_struct_0(sK0) = X0
      | ~ m1_subset_1(X0,u1_pre_topc(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f199])).

fof(f199,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_pre_topc(sK0))
      | u1_struct_0(sK0) = X0
      | ~ m1_subset_1(X0,u1_pre_topc(sK0))
      | ~ v1_xboole_0(u1_struct_0(sK0)) ) ),
    inference(forward_demodulation,[],[f197,f180])).

fof(f197,plain,(
    ! [X0] :
      ( u1_struct_0(sK0) = X0
      | ~ m1_subset_1(X0,u1_pre_topc(sK0))
      | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(sK0)))
      | ~ v1_xboole_0(u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f191,f139])).

fof(f941,plain,
    ( v1_tops_1(k1_xboole_0,sK0)
    | k1_xboole_0 != sK2(sK0) ),
    inference(forward_demodulation,[],[f874,f861])).

fof(f874,plain,
    ( k1_xboole_0 != sK2(sK0)
    | v1_tops_1(u1_struct_0(sK0),sK0) ),
    inference(backward_demodulation,[],[f272,f861])).

fof(f272,plain,
    ( u1_struct_0(sK0) != sK2(sK0)
    | v1_tops_1(u1_struct_0(sK0),sK0) ),
    inference(inner_rewriting,[],[f271])).

fof(f271,plain,
    ( u1_struct_0(sK0) != sK2(sK0)
    | v1_tops_1(sK2(sK0),sK0) ),
    inference(subsumption_resolution,[],[f270,f227])).

fof(f270,plain,
    ( ~ m1_subset_1(sK2(sK0),u1_pre_topc(sK0))
    | u1_struct_0(sK0) != sK2(sK0)
    | v1_tops_1(sK2(sK0),sK0) ),
    inference(forward_demodulation,[],[f269,f180])).

fof(f269,plain,
    ( u1_struct_0(sK0) != sK2(sK0)
    | ~ m1_subset_1(sK2(sK0),k9_setfam_1(u1_struct_0(sK0)))
    | v1_tops_1(sK2(sK0),sK0) ),
    inference(subsumption_resolution,[],[f268,f80])).

fof(f268,plain,
    ( u1_struct_0(sK0) != sK2(sK0)
    | ~ m1_subset_1(sK2(sK0),k9_setfam_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v1_tops_1(sK2(sK0),sK0) ),
    inference(superposition,[],[f138,f263])).

fof(f263,plain,(
    sK2(sK0) = k2_pre_topc(sK0,sK2(sK0)) ),
    inference(subsumption_resolution,[],[f262,f77])).

fof(f262,plain,
    ( sK2(sK0) = k2_pre_topc(sK0,sK2(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f261,f80])).

fof(f261,plain,
    ( sK2(sK0) = k2_pre_topc(sK0,sK2(sK0))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f260,f78])).

fof(f260,plain,
    ( sK2(sK0) = k2_pre_topc(sK0,sK2(sK0))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f259,f227])).

fof(f259,plain,
    ( ~ m1_subset_1(sK2(sK0),u1_pre_topc(sK0))
    | sK2(sK0) = k2_pre_topc(sK0,sK2(sK0))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f258,f109])).

fof(f109,plain,(
    ! [X0] :
      ( v4_pre_topc(sK2(X0),X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:48:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (15576)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (15553)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (15554)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (15556)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (15559)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (15568)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (15557)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (15581)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.52  % (15561)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (15574)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (15566)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (15563)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (15577)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (15567)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (15571)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.53  % (15563)Refutation not found, incomplete strategy% (15563)------------------------------
% 0.21/0.53  % (15563)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (15563)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (15563)Memory used [KB]: 10618
% 0.21/0.53  % (15563)Time elapsed: 0.122 s
% 0.21/0.53  % (15563)------------------------------
% 0.21/0.53  % (15563)------------------------------
% 0.21/0.53  % (15553)Refutation not found, incomplete strategy% (15553)------------------------------
% 0.21/0.53  % (15553)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (15553)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (15553)Memory used [KB]: 1663
% 0.21/0.53  % (15553)Time elapsed: 0.120 s
% 0.21/0.53  % (15553)------------------------------
% 0.21/0.53  % (15553)------------------------------
% 0.21/0.53  % (15560)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (15572)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (15575)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (15573)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (15555)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (15570)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (15558)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (15570)Refutation not found, incomplete strategy% (15570)------------------------------
% 0.21/0.54  % (15570)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (15570)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (15570)Memory used [KB]: 10618
% 0.21/0.54  % (15570)Time elapsed: 0.132 s
% 0.21/0.54  % (15570)------------------------------
% 0.21/0.54  % (15570)------------------------------
% 0.21/0.54  % (15580)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (15557)Refutation not found, incomplete strategy% (15557)------------------------------
% 0.21/0.54  % (15557)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (15557)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (15557)Memory used [KB]: 6268
% 0.21/0.54  % (15557)Time elapsed: 0.119 s
% 0.21/0.54  % (15557)------------------------------
% 0.21/0.54  % (15557)------------------------------
% 0.21/0.55  % (15579)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (15578)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (15565)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (15564)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (15582)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (15562)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.50/0.57  % (15569)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.50/0.58  % (15575)Refutation not found, incomplete strategy% (15575)------------------------------
% 1.50/0.58  % (15575)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.58  % (15575)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.58  
% 1.50/0.58  % (15575)Memory used [KB]: 11129
% 1.50/0.58  % (15575)Time elapsed: 0.182 s
% 1.50/0.58  % (15575)------------------------------
% 1.50/0.58  % (15575)------------------------------
% 1.73/0.58  % (15559)Refutation found. Thanks to Tanya!
% 1.73/0.58  % SZS status Theorem for theBenchmark
% 1.73/0.58  % SZS output start Proof for theBenchmark
% 1.73/0.58  fof(f1017,plain,(
% 1.73/0.58    $false),
% 1.73/0.58    inference(subsumption_resolution,[],[f1016,f962])).
% 1.73/0.58  fof(f962,plain,(
% 1.73/0.58    ~v3_tex_2(k1_xboole_0,sK0)),
% 1.73/0.58    inference(subsumption_resolution,[],[f893,f173])).
% 1.73/0.58  fof(f173,plain,(
% 1.73/0.58    ( ! [X1] : (~v1_subset_1(X1,X1)) )),
% 1.73/0.58    inference(subsumption_resolution,[],[f163,f166])).
% 1.73/0.58  fof(f166,plain,(
% 1.73/0.58    ( ! [X0] : (m1_subset_1(X0,k9_setfam_1(X0))) )),
% 1.73/0.58    inference(forward_demodulation,[],[f132,f130])).
% 1.73/0.58  fof(f130,plain,(
% 1.73/0.58    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 1.73/0.58    inference(definition_unfolding,[],[f84,f128])).
% 1.73/0.58  fof(f128,plain,(
% 1.73/0.58    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 1.73/0.58    inference(definition_unfolding,[],[f88,f83])).
% 1.73/0.58  fof(f83,plain,(
% 1.73/0.58    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 1.73/0.58    inference(cnf_transformation,[],[f5])).
% 1.73/0.58  fof(f5,axiom,(
% 1.73/0.58    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 1.73/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 1.73/0.58  fof(f88,plain,(
% 1.73/0.58    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 1.73/0.58    inference(cnf_transformation,[],[f10])).
% 1.73/0.58  fof(f10,axiom,(
% 1.73/0.58    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 1.73/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).
% 1.73/0.58  fof(f84,plain,(
% 1.73/0.58    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.73/0.58    inference(cnf_transformation,[],[f6])).
% 1.73/0.58  fof(f6,axiom,(
% 1.73/0.58    ! [X0] : k2_subset_1(X0) = X0),
% 1.73/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.73/0.58  fof(f132,plain,(
% 1.73/0.58    ( ! [X0] : (m1_subset_1(k3_subset_1(X0,k1_xboole_0),k9_setfam_1(X0))) )),
% 1.73/0.58    inference(definition_unfolding,[],[f87,f128,f85])).
% 1.73/0.58  fof(f85,plain,(
% 1.73/0.58    ( ! [X0] : (k1_zfmisc_1(X0) = k9_setfam_1(X0)) )),
% 1.73/0.58    inference(cnf_transformation,[],[f13])).
% 1.73/0.58  fof(f13,axiom,(
% 1.73/0.58    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0)),
% 1.73/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).
% 1.73/0.58  fof(f87,plain,(
% 1.73/0.58    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.73/0.58    inference(cnf_transformation,[],[f8])).
% 1.73/0.58  fof(f8,axiom,(
% 1.73/0.58    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.73/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.73/0.58  fof(f163,plain,(
% 1.73/0.58    ( ! [X1] : (~m1_subset_1(X1,k9_setfam_1(X1)) | ~v1_subset_1(X1,X1)) )),
% 1.73/0.58    inference(equality_resolution,[],[f154])).
% 1.73/0.58  fof(f154,plain,(
% 1.73/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k9_setfam_1(X0)) | X0 != X1 | ~v1_subset_1(X1,X0)) )),
% 1.73/0.58    inference(definition_unfolding,[],[f122,f85])).
% 1.73/0.58  fof(f122,plain,(
% 1.73/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 != X1 | ~v1_subset_1(X1,X0)) )),
% 1.73/0.58    inference(cnf_transformation,[],[f71])).
% 1.73/0.58  fof(f71,plain,(
% 1.73/0.58    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.73/0.58    inference(ennf_transformation,[],[f24])).
% 1.73/0.58  fof(f24,axiom,(
% 1.73/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 1.73/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 1.73/0.58  fof(f893,plain,(
% 1.73/0.58    v1_subset_1(k1_xboole_0,k1_xboole_0) | ~v3_tex_2(k1_xboole_0,sK0)),
% 1.73/0.58    inference(backward_demodulation,[],[f850,f861])).
% 1.73/0.58  fof(f861,plain,(
% 1.73/0.58    k1_xboole_0 = u1_struct_0(sK0)),
% 1.73/0.58    inference(subsumption_resolution,[],[f860,f178])).
% 1.73/0.58  fof(f178,plain,(
% 1.73/0.58    v1_xboole_0(k1_xboole_0)),
% 1.73/0.58    inference(resolution,[],[f177,f82])).
% 1.73/0.58  fof(f82,plain,(
% 1.73/0.58    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.73/0.58    inference(cnf_transformation,[],[f1])).
% 1.73/0.58  fof(f1,axiom,(
% 1.73/0.58    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.73/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.73/0.58  fof(f177,plain,(
% 1.73/0.58    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | v1_xboole_0(X0)) )),
% 1.73/0.58    inference(resolution,[],[f119,f81])).
% 1.73/0.58  fof(f81,plain,(
% 1.73/0.58    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.73/0.58    inference(cnf_transformation,[],[f2])).
% 1.73/0.58  fof(f2,axiom,(
% 1.73/0.58    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.73/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.73/0.58  fof(f119,plain,(
% 1.73/0.58    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 1.73/0.58    inference(cnf_transformation,[],[f69])).
% 1.73/0.58  fof(f69,plain,(
% 1.73/0.58    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 1.73/0.58    inference(flattening,[],[f68])).
% 1.73/0.58  fof(f68,plain,(
% 1.73/0.58    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 1.73/0.58    inference(ennf_transformation,[],[f3])).
% 1.73/0.58  fof(f3,axiom,(
% 1.73/0.58    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 1.73/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).
% 1.73/0.58  fof(f860,plain,(
% 1.73/0.58    ~v1_xboole_0(k1_xboole_0) | k1_xboole_0 = u1_struct_0(sK0)),
% 1.73/0.58    inference(forward_demodulation,[],[f785,f775])).
% 1.73/0.58  fof(f775,plain,(
% 1.73/0.58    k1_xboole_0 = sK1),
% 1.73/0.58    inference(subsumption_resolution,[],[f772,f173])).
% 1.73/0.58  fof(f772,plain,(
% 1.73/0.58    v1_subset_1(sK1,sK1) | k1_xboole_0 = sK1),
% 1.73/0.58    inference(duplicate_literal_removal,[],[f771])).
% 1.73/0.58  fof(f771,plain,(
% 1.73/0.58    v1_subset_1(sK1,sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 1.73/0.58    inference(superposition,[],[f720,f692])).
% 1.73/0.58  fof(f692,plain,(
% 1.73/0.58    sK1 = u1_struct_0(sK0) | k1_xboole_0 = sK1),
% 1.73/0.58    inference(duplicate_literal_removal,[],[f686])).
% 1.73/0.58  fof(f686,plain,(
% 1.73/0.58    sK1 = u1_struct_0(sK0) | k1_xboole_0 = sK1 | sK1 = u1_struct_0(sK0)),
% 1.73/0.58    inference(superposition,[],[f683,f435])).
% 1.73/0.58  fof(f435,plain,(
% 1.73/0.58    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | sK1 = u1_struct_0(sK0)),
% 1.73/0.58    inference(subsumption_resolution,[],[f434,f181])).
% 1.73/0.58  fof(f181,plain,(
% 1.73/0.58    m1_subset_1(sK1,u1_pre_topc(sK0))),
% 1.73/0.58    inference(backward_demodulation,[],[f129,f180])).
% 1.73/0.58  fof(f180,plain,(
% 1.73/0.58    k9_setfam_1(u1_struct_0(sK0)) = u1_pre_topc(sK0)),
% 1.73/0.58    inference(subsumption_resolution,[],[f179,f80])).
% 1.73/0.58  fof(f80,plain,(
% 1.73/0.58    l1_pre_topc(sK0)),
% 1.73/0.58    inference(cnf_transformation,[],[f36])).
% 1.73/0.58  fof(f36,plain,(
% 1.73/0.58    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.73/0.58    inference(flattening,[],[f35])).
% 1.73/0.58  fof(f35,plain,(
% 1.73/0.58    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.73/0.58    inference(ennf_transformation,[],[f33])).
% 1.73/0.58  fof(f33,negated_conjecture,(
% 1.73/0.58    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 1.73/0.58    inference(negated_conjecture,[],[f32])).
% 1.73/0.58  fof(f32,conjecture,(
% 1.73/0.58    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 1.73/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tex_2)).
% 1.73/0.58  fof(f179,plain,(
% 1.73/0.58    k9_setfam_1(u1_struct_0(sK0)) = u1_pre_topc(sK0) | ~l1_pre_topc(sK0)),
% 1.73/0.58    inference(resolution,[],[f93,f79])).
% 1.73/0.58  fof(f79,plain,(
% 1.73/0.58    v1_tdlat_3(sK0)),
% 1.73/0.58    inference(cnf_transformation,[],[f36])).
% 1.73/0.58  fof(f93,plain,(
% 1.73/0.58    ( ! [X0] : (~v1_tdlat_3(X0) | u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0)) | ~l1_pre_topc(X0)) )),
% 1.73/0.58    inference(cnf_transformation,[],[f43])).
% 1.73/0.58  fof(f43,plain,(
% 1.73/0.58    ! [X0] : ((v1_tdlat_3(X0) <=> u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.73/0.58    inference(ennf_transformation,[],[f22])).
% 1.73/0.58  fof(f22,axiom,(
% 1.73/0.58    ! [X0] : (l1_pre_topc(X0) => (v1_tdlat_3(X0) <=> u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0))))),
% 1.73/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tdlat_3)).
% 1.73/0.58  fof(f129,plain,(
% 1.73/0.58    m1_subset_1(sK1,k9_setfam_1(u1_struct_0(sK0)))),
% 1.73/0.58    inference(definition_unfolding,[],[f76,f85])).
% 1.73/0.58  fof(f76,plain,(
% 1.73/0.58    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.73/0.58    inference(cnf_transformation,[],[f36])).
% 1.73/0.58  fof(f434,plain,(
% 1.73/0.58    ~m1_subset_1(sK1,u1_pre_topc(sK0)) | sK1 = u1_struct_0(sK0) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 1.73/0.58    inference(forward_demodulation,[],[f433,f180])).
% 1.73/0.58  fof(f433,plain,(
% 1.73/0.58    sK1 = u1_struct_0(sK0) | ~m1_subset_1(sK1,k9_setfam_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 1.73/0.58    inference(subsumption_resolution,[],[f432,f80])).
% 1.73/0.58  fof(f432,plain,(
% 1.73/0.58    sK1 = u1_struct_0(sK0) | ~m1_subset_1(sK1,k9_setfam_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0)),
% 1.73/0.58    inference(resolution,[],[f431,f137])).
% 1.73/0.58  fof(f137,plain,(
% 1.73/0.58    ( ! [X0,X1] : (~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0))) | u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~l1_pre_topc(X0)) )),
% 1.73/0.58    inference(definition_unfolding,[],[f99,f85])).
% 1.73/0.58  fof(f99,plain,(
% 1.73/0.58    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0)) )),
% 1.73/0.58    inference(cnf_transformation,[],[f48])).
% 1.73/0.58  fof(f48,plain,(
% 1.73/0.58    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.73/0.58    inference(ennf_transformation,[],[f23])).
% 1.73/0.58  fof(f23,axiom,(
% 1.73/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 1.73/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).
% 1.73/0.58  fof(f431,plain,(
% 1.73/0.58    v1_tops_1(sK1,sK0) | sK1 = u1_struct_0(sK0)),
% 1.73/0.58    inference(subsumption_resolution,[],[f430,f181])).
% 1.73/0.58  fof(f430,plain,(
% 1.73/0.58    ~m1_subset_1(sK1,u1_pre_topc(sK0)) | v1_tops_1(sK1,sK0) | sK1 = u1_struct_0(sK0)),
% 1.73/0.58    inference(forward_demodulation,[],[f429,f180])).
% 1.73/0.58  fof(f429,plain,(
% 1.73/0.58    ~m1_subset_1(sK1,k9_setfam_1(u1_struct_0(sK0))) | v1_tops_1(sK1,sK0) | sK1 = u1_struct_0(sK0)),
% 1.73/0.58    inference(subsumption_resolution,[],[f428,f77])).
% 1.73/0.58  fof(f77,plain,(
% 1.73/0.58    ~v2_struct_0(sK0)),
% 1.73/0.58    inference(cnf_transformation,[],[f36])).
% 1.73/0.58  fof(f428,plain,(
% 1.73/0.58    ~m1_subset_1(sK1,k9_setfam_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | v1_tops_1(sK1,sK0) | sK1 = u1_struct_0(sK0)),
% 1.73/0.58    inference(subsumption_resolution,[],[f427,f237])).
% 1.73/0.58  fof(f237,plain,(
% 1.73/0.58    v3_pre_topc(sK1,sK0)),
% 1.73/0.58    inference(resolution,[],[f234,f181])).
% 1.73/0.58  fof(f234,plain,(
% 1.73/0.58    ( ! [X0] : (~m1_subset_1(X0,u1_pre_topc(sK0)) | v3_pre_topc(X0,sK0)) )),
% 1.73/0.58    inference(forward_demodulation,[],[f233,f180])).
% 1.73/0.59  fof(f233,plain,(
% 1.73/0.59    ( ! [X0] : (~m1_subset_1(X0,k9_setfam_1(u1_struct_0(sK0))) | v3_pre_topc(X0,sK0)) )),
% 1.73/0.59    inference(subsumption_resolution,[],[f232,f80])).
% 1.73/0.59  fof(f232,plain,(
% 1.73/0.59    ( ! [X0] : (~m1_subset_1(X0,k9_setfam_1(u1_struct_0(sK0))) | v3_pre_topc(X0,sK0) | ~l1_pre_topc(sK0)) )),
% 1.73/0.59    inference(resolution,[],[f170,f79])).
% 1.73/0.59  fof(f170,plain,(
% 1.73/0.59    ( ! [X0,X1] : (~v1_tdlat_3(X0) | ~m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0))) | v3_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.73/0.59    inference(subsumption_resolution,[],[f150,f91])).
% 1.73/0.59  fof(f91,plain,(
% 1.73/0.59    ( ! [X0] : (~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_pre_topc(X0)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f42])).
% 1.73/0.59  fof(f42,plain,(
% 1.73/0.59    ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 1.73/0.59    inference(flattening,[],[f41])).
% 1.73/0.59  fof(f41,plain,(
% 1.73/0.59    ! [X0] : ((v2_pre_topc(X0) | ~v1_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 1.73/0.59    inference(ennf_transformation,[],[f20])).
% 1.73/0.59  fof(f20,axiom,(
% 1.73/0.59    ! [X0] : (l1_pre_topc(X0) => (v1_tdlat_3(X0) => v2_pre_topc(X0)))),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tdlat_3)).
% 1.73/0.59  fof(f150,plain,(
% 1.73/0.59    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0))) | v3_pre_topc(X1,X0) | ~v1_tdlat_3(X0)) )),
% 1.73/0.59    inference(definition_unfolding,[],[f114,f85])).
% 1.73/0.59  fof(f114,plain,(
% 1.73/0.59    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(X1,X0) | ~v1_tdlat_3(X0)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f65])).
% 1.73/0.59  fof(f65,plain,(
% 1.73/0.59    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.73/0.59    inference(flattening,[],[f64])).
% 1.73/0.59  fof(f64,plain,(
% 1.73/0.59    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.73/0.59    inference(ennf_transformation,[],[f27])).
% 1.73/0.59  fof(f27,axiom,(
% 1.73/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v1_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v3_pre_topc(X1,X0))))),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tdlat_3)).
% 1.73/0.59  fof(f427,plain,(
% 1.73/0.59    ~m1_subset_1(sK1,k9_setfam_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK1,sK0) | v2_struct_0(sK0) | v1_tops_1(sK1,sK0) | sK1 = u1_struct_0(sK0)),
% 1.73/0.59    inference(subsumption_resolution,[],[f426,f80])).
% 1.73/0.59  fof(f426,plain,(
% 1.73/0.59    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k9_setfam_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK1,sK0) | v2_struct_0(sK0) | v1_tops_1(sK1,sK0) | sK1 = u1_struct_0(sK0)),
% 1.73/0.59    inference(subsumption_resolution,[],[f425,f78])).
% 1.73/0.59  fof(f78,plain,(
% 1.73/0.59    v2_pre_topc(sK0)),
% 1.73/0.59    inference(cnf_transformation,[],[f36])).
% 1.73/0.59  fof(f425,plain,(
% 1.73/0.59    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k9_setfam_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK1,sK0) | v2_struct_0(sK0) | v1_tops_1(sK1,sK0) | sK1 = u1_struct_0(sK0)),
% 1.73/0.59    inference(resolution,[],[f141,f201])).
% 1.73/0.59  fof(f201,plain,(
% 1.73/0.59    v3_tex_2(sK1,sK0) | sK1 = u1_struct_0(sK0)),
% 1.73/0.59    inference(subsumption_resolution,[],[f198,f181])).
% 1.73/0.59  fof(f198,plain,(
% 1.73/0.59    sK1 = u1_struct_0(sK0) | ~m1_subset_1(sK1,u1_pre_topc(sK0)) | v3_tex_2(sK1,sK0)),
% 1.73/0.59    inference(resolution,[],[f191,f74])).
% 1.73/0.59  fof(f74,plain,(
% 1.73/0.59    ~v1_subset_1(sK1,u1_struct_0(sK0)) | v3_tex_2(sK1,sK0)),
% 1.73/0.59    inference(cnf_transformation,[],[f36])).
% 1.73/0.59  fof(f191,plain,(
% 1.73/0.59    ( ! [X0] : (v1_subset_1(X0,u1_struct_0(sK0)) | u1_struct_0(sK0) = X0 | ~m1_subset_1(X0,u1_pre_topc(sK0))) )),
% 1.73/0.59    inference(superposition,[],[f155,f180])).
% 1.73/0.59  fof(f155,plain,(
% 1.73/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,k9_setfam_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 1.73/0.59    inference(definition_unfolding,[],[f121,f85])).
% 1.73/0.59  fof(f121,plain,(
% 1.73/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f71])).
% 1.73/0.59  fof(f141,plain,(
% 1.73/0.59    ( ! [X0,X1] : (~v3_tex_2(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | v2_struct_0(X0) | v1_tops_1(X1,X0)) )),
% 1.73/0.59    inference(definition_unfolding,[],[f104,f85])).
% 1.73/0.59  fof(f104,plain,(
% 1.73/0.59    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~v3_tex_2(X1,X0) | v1_tops_1(X1,X0)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f55])).
% 1.73/0.59  fof(f55,plain,(
% 1.73/0.59    ! [X0] : (! [X1] : (v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.73/0.59    inference(flattening,[],[f54])).
% 1.73/0.59  fof(f54,plain,(
% 1.73/0.59    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) | (~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.73/0.59    inference(ennf_transformation,[],[f30])).
% 1.73/0.59  fof(f30,axiom,(
% 1.73/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tex_2(X1,X0) & v3_pre_topc(X1,X0)) => v1_tops_1(X1,X0))))),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_tex_2)).
% 1.73/0.59  fof(f683,plain,(
% 1.73/0.59    sK1 = k2_pre_topc(sK0,sK1) | k1_xboole_0 = sK1),
% 1.73/0.59    inference(subsumption_resolution,[],[f682,f181])).
% 1.73/0.59  fof(f682,plain,(
% 1.73/0.59    k1_xboole_0 = sK1 | ~m1_subset_1(sK1,u1_pre_topc(sK0)) | sK1 = k2_pre_topc(sK0,sK1)),
% 1.73/0.59    inference(resolution,[],[f681,f258])).
% 1.73/0.59  fof(f258,plain,(
% 1.73/0.59    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,u1_pre_topc(sK0)) | k2_pre_topc(sK0,X0) = X0) )),
% 1.73/0.59    inference(forward_demodulation,[],[f257,f180])).
% 1.73/0.59  fof(f257,plain,(
% 1.73/0.59    ( ! [X0] : (~m1_subset_1(X0,k9_setfam_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0) | k2_pre_topc(sK0,X0) = X0) )),
% 1.73/0.59    inference(resolution,[],[f135,f80])).
% 1.73/0.59  fof(f135,plain,(
% 1.73/0.59    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1) )),
% 1.73/0.59    inference(definition_unfolding,[],[f97,f85])).
% 1.73/0.59  fof(f97,plain,(
% 1.73/0.59    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1) )),
% 1.73/0.59    inference(cnf_transformation,[],[f47])).
% 1.73/0.59  fof(f47,plain,(
% 1.73/0.59    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.73/0.59    inference(flattening,[],[f46])).
% 1.73/0.59  fof(f46,plain,(
% 1.73/0.59    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.73/0.59    inference(ennf_transformation,[],[f17])).
% 1.73/0.59  fof(f17,axiom,(
% 1.73/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 1.73/0.59  fof(f681,plain,(
% 1.73/0.59    v4_pre_topc(sK1,sK0) | k1_xboole_0 = sK1),
% 1.73/0.59    inference(subsumption_resolution,[],[f677,f194])).
% 1.73/0.59  fof(f194,plain,(
% 1.73/0.59    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.73/0.59    inference(subsumption_resolution,[],[f193,f131])).
% 1.73/0.59  fof(f131,plain,(
% 1.73/0.59    ( ! [X0] : (m1_subset_1(k1_xboole_0,k9_setfam_1(X0))) )),
% 1.73/0.59    inference(definition_unfolding,[],[f86,f83,f85])).
% 1.73/0.59  fof(f86,plain,(
% 1.73/0.59    ( ! [X0] : (m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.73/0.59    inference(cnf_transformation,[],[f7])).
% 1.73/0.59  fof(f7,axiom,(
% 1.73/0.59    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_subset_1)).
% 1.73/0.59  fof(f193,plain,(
% 1.73/0.59    ( ! [X0] : (k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k9_setfam_1(X0)) | ~v1_xboole_0(X0)) )),
% 1.73/0.59    inference(resolution,[],[f190,f139])).
% 1.73/0.59  fof(f139,plain,(
% 1.73/0.59    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k9_setfam_1(X0)) | ~v1_xboole_0(X0)) )),
% 1.73/0.59    inference(definition_unfolding,[],[f100,f85])).
% 1.73/0.59  fof(f100,plain,(
% 1.73/0.59    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_subset_1(X1,X0)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f49])).
% 1.73/0.59  fof(f49,plain,(
% 1.73/0.59    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 1.73/0.59    inference(ennf_transformation,[],[f12])).
% 1.73/0.59  fof(f12,axiom,(
% 1.73/0.59    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~v1_subset_1(X1,X0)))),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_subset_1)).
% 1.73/0.59  fof(f190,plain,(
% 1.73/0.59    ( ! [X1] : (v1_subset_1(k1_xboole_0,X1) | k1_xboole_0 = X1) )),
% 1.73/0.59    inference(resolution,[],[f155,f131])).
% 1.73/0.59  fof(f677,plain,(
% 1.73/0.59    v4_pre_topc(sK1,sK0) | v1_xboole_0(sK1) | k1_xboole_0 = sK1),
% 1.73/0.59    inference(superposition,[],[f670,f358])).
% 1.73/0.59  fof(f358,plain,(
% 1.73/0.59    sK1 = u1_struct_0(sK3(sK0,sK1)) | k1_xboole_0 = sK1),
% 1.73/0.59    inference(resolution,[],[f354,f194])).
% 1.73/0.59  fof(f354,plain,(
% 1.73/0.59    v1_xboole_0(sK1) | sK1 = u1_struct_0(sK3(sK0,sK1))),
% 1.73/0.59    inference(resolution,[],[f350,f181])).
% 1.73/0.59  fof(f350,plain,(
% 1.73/0.59    ( ! [X0] : (~m1_subset_1(X0,u1_pre_topc(sK0)) | v1_xboole_0(X0) | u1_struct_0(sK3(sK0,X0)) = X0) )),
% 1.73/0.59    inference(forward_demodulation,[],[f349,f180])).
% 1.73/0.59  fof(f349,plain,(
% 1.73/0.59    ( ! [X0] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k9_setfam_1(u1_struct_0(sK0))) | u1_struct_0(sK3(sK0,X0)) = X0) )),
% 1.73/0.59    inference(subsumption_resolution,[],[f347,f77])).
% 1.73/0.59  fof(f347,plain,(
% 1.73/0.59    ( ! [X0] : (v2_struct_0(sK0) | v1_xboole_0(X0) | ~m1_subset_1(X0,k9_setfam_1(u1_struct_0(sK0))) | u1_struct_0(sK3(sK0,X0)) = X0) )),
% 1.73/0.59    inference(resolution,[],[f145,f80])).
% 1.73/0.59  fof(f145,plain,(
% 1.73/0.59    ( ! [X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0))) | u1_struct_0(sK3(X0,X1)) = X1) )),
% 1.73/0.59    inference(definition_unfolding,[],[f113,f85])).
% 1.73/0.59  fof(f113,plain,(
% 1.73/0.59    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(sK3(X0,X1)) = X1) )),
% 1.73/0.59    inference(cnf_transformation,[],[f63])).
% 1.73/0.59  fof(f63,plain,(
% 1.73/0.59    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.73/0.59    inference(flattening,[],[f62])).
% 1.73/0.59  fof(f62,plain,(
% 1.73/0.59    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.73/0.59    inference(ennf_transformation,[],[f26])).
% 1.73/0.59  fof(f26,axiom,(
% 1.73/0.59    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))))),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tsep_1)).
% 1.73/0.59  fof(f670,plain,(
% 1.73/0.59    v4_pre_topc(u1_struct_0(sK3(sK0,sK1)),sK0) | v1_xboole_0(sK1)),
% 1.73/0.59    inference(resolution,[],[f665,f181])).
% 1.73/0.59  fof(f665,plain,(
% 1.73/0.59    ( ! [X0] : (~m1_subset_1(X0,u1_pre_topc(sK0)) | v4_pre_topc(u1_struct_0(sK3(sK0,X0)),sK0) | v1_xboole_0(X0)) )),
% 1.73/0.59    inference(subsumption_resolution,[],[f664,f281])).
% 1.73/0.59  fof(f281,plain,(
% 1.73/0.59    ( ! [X0] : (m1_pre_topc(sK3(sK0,X0),sK0) | v1_xboole_0(X0) | ~m1_subset_1(X0,u1_pre_topc(sK0))) )),
% 1.73/0.59    inference(forward_demodulation,[],[f280,f180])).
% 1.73/0.59  fof(f280,plain,(
% 1.73/0.59    ( ! [X0] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k9_setfam_1(u1_struct_0(sK0))) | m1_pre_topc(sK3(sK0,X0),sK0)) )),
% 1.73/0.59    inference(subsumption_resolution,[],[f279,f77])).
% 1.73/0.59  fof(f279,plain,(
% 1.73/0.59    ( ! [X0] : (v2_struct_0(sK0) | v1_xboole_0(X0) | ~m1_subset_1(X0,k9_setfam_1(u1_struct_0(sK0))) | m1_pre_topc(sK3(sK0,X0),sK0)) )),
% 1.73/0.59    inference(resolution,[],[f146,f80])).
% 1.73/0.59  fof(f146,plain,(
% 1.73/0.59    ( ! [X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0))) | m1_pre_topc(sK3(X0,X1),X0)) )),
% 1.73/0.59    inference(definition_unfolding,[],[f112,f85])).
% 1.73/0.59  fof(f112,plain,(
% 1.73/0.59    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_pre_topc(sK3(X0,X1),X0)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f63])).
% 1.73/0.59  fof(f664,plain,(
% 1.73/0.59    ( ! [X0] : (~m1_subset_1(X0,u1_pre_topc(sK0)) | v4_pre_topc(u1_struct_0(sK3(sK0,X0)),sK0) | v1_xboole_0(X0) | ~m1_pre_topc(sK3(sK0,X0),sK0)) )),
% 1.73/0.59    inference(subsumption_resolution,[],[f663,f77])).
% 1.73/0.59  fof(f663,plain,(
% 1.73/0.59    ( ! [X0] : (~m1_subset_1(X0,u1_pre_topc(sK0)) | v4_pre_topc(u1_struct_0(sK3(sK0,X0)),sK0) | v1_xboole_0(X0) | ~m1_pre_topc(sK3(sK0,X0),sK0) | v2_struct_0(sK0)) )),
% 1.73/0.59    inference(subsumption_resolution,[],[f662,f80])).
% 1.73/0.59  fof(f662,plain,(
% 1.73/0.59    ( ! [X0] : (~m1_subset_1(X0,u1_pre_topc(sK0)) | v4_pre_topc(u1_struct_0(sK3(sK0,X0)),sK0) | v1_xboole_0(X0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK3(sK0,X0),sK0) | v2_struct_0(sK0)) )),
% 1.73/0.59    inference(subsumption_resolution,[],[f661,f79])).
% 1.73/0.59  fof(f661,plain,(
% 1.73/0.59    ( ! [X0] : (~m1_subset_1(X0,u1_pre_topc(sK0)) | v4_pre_topc(u1_struct_0(sK3(sK0,X0)),sK0) | v1_xboole_0(X0) | ~v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK3(sK0,X0),sK0) | v2_struct_0(sK0)) )),
% 1.73/0.59    inference(resolution,[],[f290,f168])).
% 1.73/0.59  fof(f168,plain,(
% 1.73/0.59    ( ! [X0,X1] : (v1_borsuk_1(X1,X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0)) )),
% 1.73/0.59    inference(subsumption_resolution,[],[f101,f91])).
% 1.73/0.59  fof(f101,plain,(
% 1.73/0.59    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v1_borsuk_1(X1,X0)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f51])).
% 1.73/0.59  fof(f51,plain,(
% 1.73/0.59    ! [X0] : (! [X1] : ((v1_tdlat_3(X1) & v1_borsuk_1(X1,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.73/0.59    inference(flattening,[],[f50])).
% 1.73/0.59  fof(f50,plain,(
% 1.73/0.59    ! [X0] : (! [X1] : ((v1_tdlat_3(X1) & v1_borsuk_1(X1,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.73/0.59    inference(ennf_transformation,[],[f34])).
% 1.73/0.59  fof(f34,plain,(
% 1.73/0.59    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tdlat_3(X1) & v1_borsuk_1(X1,X0))))),
% 1.73/0.59    inference(pure_predicate_removal,[],[f21])).
% 1.73/0.59  fof(f21,axiom,(
% 1.73/0.59    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tdlat_3(X1) & v1_tsep_1(X1,X0) & v1_borsuk_1(X1,X0))))),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_tdlat_3)).
% 1.73/0.59  fof(f290,plain,(
% 1.73/0.59    ( ! [X0] : (~v1_borsuk_1(sK3(sK0,X0),sK0) | ~m1_subset_1(X0,u1_pre_topc(sK0)) | v4_pre_topc(u1_struct_0(sK3(sK0,X0)),sK0) | v1_xboole_0(X0)) )),
% 1.73/0.59    inference(subsumption_resolution,[],[f289,f78])).
% 1.73/0.59  fof(f289,plain,(
% 1.73/0.59    ( ! [X0] : (v1_xboole_0(X0) | ~m1_subset_1(X0,u1_pre_topc(sK0)) | v4_pre_topc(u1_struct_0(sK3(sK0,X0)),sK0) | ~v1_borsuk_1(sK3(sK0,X0),sK0) | ~v2_pre_topc(sK0)) )),
% 1.73/0.59    inference(subsumption_resolution,[],[f285,f80])).
% 1.73/0.59  fof(f285,plain,(
% 1.73/0.59    ( ! [X0] : (v1_xboole_0(X0) | ~m1_subset_1(X0,u1_pre_topc(sK0)) | ~l1_pre_topc(sK0) | v4_pre_topc(u1_struct_0(sK3(sK0,X0)),sK0) | ~v1_borsuk_1(sK3(sK0,X0),sK0) | ~v2_pre_topc(sK0)) )),
% 1.73/0.59    inference(resolution,[],[f281,f172])).
% 1.73/0.59  fof(f172,plain,(
% 1.73/0.59    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v4_pre_topc(u1_struct_0(X1),X0) | ~v1_borsuk_1(X1,X0) | ~v2_pre_topc(X0)) )),
% 1.73/0.59    inference(subsumption_resolution,[],[f162,f134])).
% 1.73/0.59  fof(f134,plain,(
% 1.73/0.59    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | m1_subset_1(u1_struct_0(X1),k9_setfam_1(u1_struct_0(X0)))) )),
% 1.73/0.59    inference(definition_unfolding,[],[f95,f85])).
% 1.73/0.59  fof(f95,plain,(
% 1.73/0.59    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.73/0.59    inference(cnf_transformation,[],[f45])).
% 1.73/0.59  fof(f45,plain,(
% 1.73/0.59    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.73/0.59    inference(ennf_transformation,[],[f19])).
% 1.73/0.59  fof(f19,axiom,(
% 1.73/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 1.73/0.59  fof(f162,plain,(
% 1.73/0.59    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(u1_struct_0(X1),k9_setfam_1(u1_struct_0(X0))) | v4_pre_topc(u1_struct_0(X1),X0) | ~v1_borsuk_1(X1,X0) | ~m1_pre_topc(X1,X0)) )),
% 1.73/0.59    inference(equality_resolution,[],[f152])).
% 1.73/0.59  fof(f152,plain,(
% 1.73/0.59    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k9_setfam_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | v4_pre_topc(X2,X0) | ~v1_borsuk_1(X1,X0) | ~m1_pre_topc(X1,X0)) )),
% 1.73/0.59    inference(definition_unfolding,[],[f117,f85])).
% 1.73/0.59  fof(f117,plain,(
% 1.73/0.59    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | v4_pre_topc(X2,X0) | ~v1_borsuk_1(X1,X0) | ~m1_pre_topc(X1,X0)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f67])).
% 1.73/0.59  fof(f67,plain,(
% 1.73/0.59    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> v4_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.73/0.59    inference(flattening,[],[f66])).
% 1.73/0.59  fof(f66,plain,(
% 1.73/0.59    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> v4_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.73/0.59    inference(ennf_transformation,[],[f18])).
% 1.73/0.59  fof(f18,axiom,(
% 1.73/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> v4_pre_topc(X2,X0))))))),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tsep_1)).
% 1.73/0.59  fof(f720,plain,(
% 1.73/0.59    v1_subset_1(sK1,u1_struct_0(sK0)) | k1_xboole_0 = sK1),
% 1.73/0.59    inference(resolution,[],[f704,f75])).
% 1.73/0.59  fof(f75,plain,(
% 1.73/0.59    ~v3_tex_2(sK1,sK0) | v1_subset_1(sK1,u1_struct_0(sK0))),
% 1.73/0.59    inference(cnf_transformation,[],[f36])).
% 1.73/0.59  fof(f704,plain,(
% 1.73/0.59    v3_tex_2(sK1,sK0) | k1_xboole_0 = sK1),
% 1.73/0.59    inference(subsumption_resolution,[],[f703,f181])).
% 1.73/0.59  fof(f703,plain,(
% 1.73/0.59    ~m1_subset_1(sK1,u1_pre_topc(sK0)) | k1_xboole_0 = sK1 | v3_tex_2(sK1,sK0)),
% 1.73/0.59    inference(forward_demodulation,[],[f702,f180])).
% 1.73/0.59  fof(f702,plain,(
% 1.73/0.59    k1_xboole_0 = sK1 | ~m1_subset_1(sK1,k9_setfam_1(u1_struct_0(sK0))) | v3_tex_2(sK1,sK0)),
% 1.73/0.59    inference(subsumption_resolution,[],[f701,f255])).
% 1.73/0.59  fof(f255,plain,(
% 1.73/0.59    v2_tex_2(sK1,sK0)),
% 1.73/0.59    inference(resolution,[],[f252,f181])).
% 1.73/0.59  fof(f252,plain,(
% 1.73/0.59    ( ! [X0] : (~m1_subset_1(X0,u1_pre_topc(sK0)) | v2_tex_2(X0,sK0)) )),
% 1.73/0.59    inference(forward_demodulation,[],[f251,f180])).
% 1.73/0.59  fof(f251,plain,(
% 1.73/0.59    ( ! [X0] : (~m1_subset_1(X0,k9_setfam_1(u1_struct_0(sK0))) | v2_tex_2(X0,sK0)) )),
% 1.73/0.59    inference(subsumption_resolution,[],[f250,f80])).
% 1.73/0.59  fof(f250,plain,(
% 1.73/0.59    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k9_setfam_1(u1_struct_0(sK0))) | v2_tex_2(X0,sK0)) )),
% 1.73/0.59    inference(subsumption_resolution,[],[f249,f77])).
% 1.73/0.59  fof(f249,plain,(
% 1.73/0.59    ( ! [X0] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X0,k9_setfam_1(u1_struct_0(sK0))) | v2_tex_2(X0,sK0)) )),
% 1.73/0.59    inference(resolution,[],[f169,f79])).
% 1.73/0.59  fof(f169,plain,(
% 1.73/0.59    ( ! [X0,X1] : (~v1_tdlat_3(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0))) | v2_tex_2(X1,X0)) )),
% 1.73/0.59    inference(subsumption_resolution,[],[f140,f91])).
% 1.73/0.59  fof(f140,plain,(
% 1.73/0.59    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0))) | v2_tex_2(X1,X0)) )),
% 1.73/0.59    inference(definition_unfolding,[],[f103,f85])).
% 1.73/0.59  fof(f103,plain,(
% 1.73/0.59    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(X1,X0)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f53])).
% 1.73/0.59  fof(f53,plain,(
% 1.73/0.59    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.73/0.59    inference(flattening,[],[f52])).
% 1.73/0.59  fof(f52,plain,(
% 1.73/0.59    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.73/0.59    inference(ennf_transformation,[],[f28])).
% 1.73/0.59  fof(f28,axiom,(
% 1.73/0.59    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).
% 1.73/0.59  fof(f701,plain,(
% 1.73/0.59    k1_xboole_0 = sK1 | ~m1_subset_1(sK1,k9_setfam_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0) | v3_tex_2(sK1,sK0)),
% 1.73/0.59    inference(subsumption_resolution,[],[f700,f77])).
% 1.73/0.59  fof(f700,plain,(
% 1.73/0.59    k1_xboole_0 = sK1 | ~m1_subset_1(sK1,k9_setfam_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~v2_tex_2(sK1,sK0) | v3_tex_2(sK1,sK0)),
% 1.73/0.59    inference(subsumption_resolution,[],[f699,f80])).
% 1.73/0.59  fof(f699,plain,(
% 1.73/0.59    k1_xboole_0 = sK1 | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k9_setfam_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~v2_tex_2(sK1,sK0) | v3_tex_2(sK1,sK0)),
% 1.73/0.59    inference(subsumption_resolution,[],[f697,f78])).
% 1.73/0.59  fof(f697,plain,(
% 1.73/0.59    k1_xboole_0 = sK1 | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k9_setfam_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~v2_tex_2(sK1,sK0) | v3_tex_2(sK1,sK0)),
% 1.73/0.59    inference(resolution,[],[f696,f142])).
% 1.73/0.59  fof(f142,plain,(
% 1.73/0.59    ( ! [X0,X1] : (~v1_tops_1(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0))) | v2_struct_0(X0) | ~v2_tex_2(X1,X0) | v3_tex_2(X1,X0)) )),
% 1.73/0.59    inference(definition_unfolding,[],[f105,f85])).
% 1.73/0.59  fof(f105,plain,(
% 1.73/0.59    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_1(X1,X0) | ~v2_tex_2(X1,X0) | v3_tex_2(X1,X0)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f57])).
% 1.73/0.59  fof(f57,plain,(
% 1.73/0.59    ! [X0] : (! [X1] : (v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.73/0.59    inference(flattening,[],[f56])).
% 1.73/0.59  fof(f56,plain,(
% 1.73/0.59    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) | (~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.73/0.59    inference(ennf_transformation,[],[f31])).
% 1.73/0.59  fof(f31,axiom,(
% 1.73/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & v1_tops_1(X1,X0)) => v3_tex_2(X1,X0))))),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tex_2)).
% 1.73/0.59  fof(f696,plain,(
% 1.73/0.59    v1_tops_1(sK1,sK0) | k1_xboole_0 = sK1),
% 1.73/0.59    inference(subsumption_resolution,[],[f695,f181])).
% 1.73/0.59  fof(f695,plain,(
% 1.73/0.59    ~m1_subset_1(sK1,u1_pre_topc(sK0)) | v1_tops_1(sK1,sK0) | k1_xboole_0 = sK1),
% 1.73/0.59    inference(forward_demodulation,[],[f694,f180])).
% 1.73/0.59  fof(f694,plain,(
% 1.73/0.59    ~m1_subset_1(sK1,k9_setfam_1(u1_struct_0(sK0))) | v1_tops_1(sK1,sK0) | k1_xboole_0 = sK1),
% 1.73/0.59    inference(subsumption_resolution,[],[f693,f692])).
% 1.73/0.59  fof(f693,plain,(
% 1.73/0.59    sK1 != u1_struct_0(sK0) | ~m1_subset_1(sK1,k9_setfam_1(u1_struct_0(sK0))) | v1_tops_1(sK1,sK0) | k1_xboole_0 = sK1),
% 1.73/0.59    inference(subsumption_resolution,[],[f689,f80])).
% 1.73/0.59  fof(f689,plain,(
% 1.73/0.59    sK1 != u1_struct_0(sK0) | ~m1_subset_1(sK1,k9_setfam_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v1_tops_1(sK1,sK0) | k1_xboole_0 = sK1),
% 1.73/0.59    inference(superposition,[],[f138,f683])).
% 1.73/0.59  fof(f138,plain,(
% 1.73/0.59    ( ! [X0,X1] : (u1_struct_0(X0) != k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v1_tops_1(X1,X0)) )),
% 1.73/0.59    inference(definition_unfolding,[],[f98,f85])).
% 1.73/0.59  fof(f98,plain,(
% 1.73/0.59    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X0) != k2_pre_topc(X0,X1) | v1_tops_1(X1,X0)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f48])).
% 1.73/0.59  fof(f785,plain,(
% 1.73/0.59    k1_xboole_0 = u1_struct_0(sK0) | ~v1_xboole_0(sK1)),
% 1.73/0.59    inference(backward_demodulation,[],[f278,f775])).
% 1.73/0.59  fof(f278,plain,(
% 1.73/0.59    ~v1_xboole_0(sK1) | sK1 = u1_struct_0(sK0)),
% 1.73/0.59    inference(subsumption_resolution,[],[f277,f181])).
% 1.73/0.59  fof(f277,plain,(
% 1.73/0.59    ~v1_xboole_0(sK1) | ~m1_subset_1(sK1,u1_pre_topc(sK0)) | sK1 = u1_struct_0(sK0)),
% 1.73/0.59    inference(resolution,[],[f276,f201])).
% 1.73/0.59  fof(f276,plain,(
% 1.73/0.59    ( ! [X0] : (~v3_tex_2(X0,sK0) | ~v1_xboole_0(X0) | ~m1_subset_1(X0,u1_pre_topc(sK0))) )),
% 1.73/0.59    inference(forward_demodulation,[],[f275,f180])).
% 1.73/0.59  fof(f275,plain,(
% 1.73/0.59    ( ! [X0] : (~v1_xboole_0(X0) | ~m1_subset_1(X0,k9_setfam_1(u1_struct_0(sK0))) | ~v3_tex_2(X0,sK0)) )),
% 1.73/0.59    inference(subsumption_resolution,[],[f274,f80])).
% 1.73/0.59  fof(f274,plain,(
% 1.73/0.59    ( ! [X0] : (~l1_pre_topc(sK0) | ~v1_xboole_0(X0) | ~m1_subset_1(X0,k9_setfam_1(u1_struct_0(sK0))) | ~v3_tex_2(X0,sK0)) )),
% 1.73/0.59    inference(subsumption_resolution,[],[f273,f77])).
% 1.73/0.59  fof(f273,plain,(
% 1.73/0.59    ( ! [X0] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~v1_xboole_0(X0) | ~m1_subset_1(X0,k9_setfam_1(u1_struct_0(sK0))) | ~v3_tex_2(X0,sK0)) )),
% 1.73/0.59    inference(resolution,[],[f143,f78])).
% 1.73/0.59  fof(f143,plain,(
% 1.73/0.59    ( ! [X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0))) | ~v3_tex_2(X1,X0)) )),
% 1.73/0.59    inference(definition_unfolding,[],[f106,f85])).
% 1.73/0.59  fof(f106,plain,(
% 1.73/0.59    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tex_2(X1,X0)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f59])).
% 1.73/0.59  fof(f59,plain,(
% 1.73/0.59    ! [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.73/0.59    inference(flattening,[],[f58])).
% 1.73/0.59  fof(f58,plain,(
% 1.73/0.59    ! [X0] : (! [X1] : (~v3_tex_2(X1,X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.73/0.59    inference(ennf_transformation,[],[f29])).
% 1.73/0.59  fof(f29,axiom,(
% 1.73/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).
% 1.73/0.59  fof(f850,plain,(
% 1.73/0.59    ~v3_tex_2(k1_xboole_0,sK0) | v1_subset_1(k1_xboole_0,u1_struct_0(sK0))),
% 1.73/0.59    inference(forward_demodulation,[],[f777,f775])).
% 1.73/0.59  fof(f777,plain,(
% 1.73/0.59    v1_subset_1(k1_xboole_0,u1_struct_0(sK0)) | ~v3_tex_2(sK1,sK0)),
% 1.73/0.59    inference(backward_demodulation,[],[f75,f775])).
% 1.73/0.59  fof(f1016,plain,(
% 1.73/0.59    v3_tex_2(k1_xboole_0,sK0)),
% 1.73/0.59    inference(subsumption_resolution,[],[f1015,f253])).
% 1.73/0.59  fof(f253,plain,(
% 1.73/0.59    v2_tex_2(k1_xboole_0,sK0)),
% 1.73/0.59    inference(resolution,[],[f252,f186])).
% 1.73/0.59  fof(f186,plain,(
% 1.73/0.59    m1_subset_1(k1_xboole_0,u1_pre_topc(sK0))),
% 1.73/0.59    inference(superposition,[],[f131,f180])).
% 1.73/0.59  fof(f1015,plain,(
% 1.73/0.59    ~v2_tex_2(k1_xboole_0,sK0) | v3_tex_2(k1_xboole_0,sK0)),
% 1.73/0.59    inference(subsumption_resolution,[],[f1014,f77])).
% 1.73/0.59  fof(f1014,plain,(
% 1.73/0.59    v2_struct_0(sK0) | ~v2_tex_2(k1_xboole_0,sK0) | v3_tex_2(k1_xboole_0,sK0)),
% 1.73/0.59    inference(subsumption_resolution,[],[f1013,f131])).
% 1.73/0.59  fof(f1013,plain,(
% 1.73/0.59    ~m1_subset_1(k1_xboole_0,k9_setfam_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~v2_tex_2(k1_xboole_0,sK0) | v3_tex_2(k1_xboole_0,sK0)),
% 1.73/0.59    inference(subsumption_resolution,[],[f1012,f80])).
% 1.73/0.59  fof(f1012,plain,(
% 1.73/0.59    ~l1_pre_topc(sK0) | ~m1_subset_1(k1_xboole_0,k9_setfam_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~v2_tex_2(k1_xboole_0,sK0) | v3_tex_2(k1_xboole_0,sK0)),
% 1.73/0.59    inference(subsumption_resolution,[],[f1010,f78])).
% 1.73/0.59  fof(f1010,plain,(
% 1.73/0.59    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(k1_xboole_0,k9_setfam_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~v2_tex_2(k1_xboole_0,sK0) | v3_tex_2(k1_xboole_0,sK0)),
% 1.73/0.59    inference(resolution,[],[f1005,f142])).
% 1.73/0.59  fof(f1005,plain,(
% 1.73/0.59    v1_tops_1(k1_xboole_0,sK0)),
% 1.73/0.59    inference(trivial_inequality_removal,[],[f1004])).
% 1.73/0.59  fof(f1004,plain,(
% 1.73/0.59    k1_xboole_0 != k1_xboole_0 | v1_tops_1(k1_xboole_0,sK0)),
% 1.73/0.59    inference(backward_demodulation,[],[f941,f992])).
% 1.73/0.59  fof(f992,plain,(
% 1.73/0.59    k1_xboole_0 = sK2(sK0)),
% 1.73/0.59    inference(resolution,[],[f934,f895])).
% 1.73/0.59  fof(f895,plain,(
% 1.73/0.59    m1_subset_1(sK2(sK0),k9_setfam_1(k1_xboole_0))),
% 1.73/0.59    inference(backward_demodulation,[],[f227,f862])).
% 1.73/0.59  fof(f862,plain,(
% 1.73/0.59    u1_pre_topc(sK0) = k9_setfam_1(k1_xboole_0)),
% 1.73/0.59    inference(backward_demodulation,[],[f180,f861])).
% 1.73/0.59  fof(f227,plain,(
% 1.73/0.59    m1_subset_1(sK2(sK0),u1_pre_topc(sK0))),
% 1.73/0.59    inference(forward_demodulation,[],[f226,f180])).
% 1.73/0.59  fof(f226,plain,(
% 1.73/0.59    m1_subset_1(sK2(sK0),k9_setfam_1(u1_struct_0(sK0)))),
% 1.73/0.59    inference(subsumption_resolution,[],[f225,f80])).
% 1.73/0.59  fof(f225,plain,(
% 1.73/0.59    ~l1_pre_topc(sK0) | m1_subset_1(sK2(sK0),k9_setfam_1(u1_struct_0(sK0)))),
% 1.73/0.59    inference(subsumption_resolution,[],[f224,f77])).
% 1.73/0.59  fof(f224,plain,(
% 1.73/0.59    v2_struct_0(sK0) | ~l1_pre_topc(sK0) | m1_subset_1(sK2(sK0),k9_setfam_1(u1_struct_0(sK0)))),
% 1.73/0.59    inference(resolution,[],[f144,f78])).
% 1.73/0.59  fof(f144,plain,(
% 1.73/0.59    ( ! [X0] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | m1_subset_1(sK2(X0),k9_setfam_1(u1_struct_0(X0)))) )),
% 1.73/0.59    inference(definition_unfolding,[],[f107,f85])).
% 1.73/0.59  fof(f107,plain,(
% 1.73/0.59    ( ! [X0] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.73/0.59    inference(cnf_transformation,[],[f61])).
% 1.73/0.59  fof(f61,plain,(
% 1.73/0.59    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.73/0.59    inference(flattening,[],[f60])).
% 1.73/0.59  fof(f60,plain,(
% 1.73/0.59    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.73/0.59    inference(ennf_transformation,[],[f16])).
% 1.73/0.59  fof(f16,axiom,(
% 1.73/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v4_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.73/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc7_pre_topc)).
% 1.73/0.59  fof(f934,plain,(
% 1.73/0.59    ( ! [X0] : (~m1_subset_1(X0,k9_setfam_1(k1_xboole_0)) | k1_xboole_0 = X0) )),
% 1.73/0.59    inference(forward_demodulation,[],[f933,f862])).
% 1.73/0.59  fof(f933,plain,(
% 1.73/0.59    ( ! [X0] : (k1_xboole_0 = X0 | ~m1_subset_1(X0,u1_pre_topc(sK0))) )),
% 1.73/0.59    inference(subsumption_resolution,[],[f932,f178])).
% 1.73/0.59  fof(f932,plain,(
% 1.73/0.59    ( ! [X0] : (~v1_xboole_0(k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X0,u1_pre_topc(sK0))) )),
% 1.73/0.59    inference(forward_demodulation,[],[f867,f861])).
% 1.73/0.59  fof(f867,plain,(
% 1.73/0.59    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_pre_topc(sK0))) )),
% 1.73/0.59    inference(backward_demodulation,[],[f200,f861])).
% 1.73/0.59  fof(f200,plain,(
% 1.73/0.59    ( ! [X0] : (~v1_xboole_0(u1_struct_0(sK0)) | u1_struct_0(sK0) = X0 | ~m1_subset_1(X0,u1_pre_topc(sK0))) )),
% 1.73/0.59    inference(duplicate_literal_removal,[],[f199])).
% 1.73/0.59  fof(f199,plain,(
% 1.73/0.59    ( ! [X0] : (~m1_subset_1(X0,u1_pre_topc(sK0)) | u1_struct_0(sK0) = X0 | ~m1_subset_1(X0,u1_pre_topc(sK0)) | ~v1_xboole_0(u1_struct_0(sK0))) )),
% 1.73/0.59    inference(forward_demodulation,[],[f197,f180])).
% 1.73/0.59  fof(f197,plain,(
% 1.73/0.59    ( ! [X0] : (u1_struct_0(sK0) = X0 | ~m1_subset_1(X0,u1_pre_topc(sK0)) | ~m1_subset_1(X0,k9_setfam_1(u1_struct_0(sK0))) | ~v1_xboole_0(u1_struct_0(sK0))) )),
% 1.73/0.59    inference(resolution,[],[f191,f139])).
% 1.73/0.59  fof(f941,plain,(
% 1.73/0.59    v1_tops_1(k1_xboole_0,sK0) | k1_xboole_0 != sK2(sK0)),
% 1.73/0.59    inference(forward_demodulation,[],[f874,f861])).
% 1.73/0.59  fof(f874,plain,(
% 1.73/0.59    k1_xboole_0 != sK2(sK0) | v1_tops_1(u1_struct_0(sK0),sK0)),
% 1.73/0.59    inference(backward_demodulation,[],[f272,f861])).
% 1.73/0.59  fof(f272,plain,(
% 1.73/0.59    u1_struct_0(sK0) != sK2(sK0) | v1_tops_1(u1_struct_0(sK0),sK0)),
% 1.73/0.59    inference(inner_rewriting,[],[f271])).
% 1.73/0.59  fof(f271,plain,(
% 1.73/0.59    u1_struct_0(sK0) != sK2(sK0) | v1_tops_1(sK2(sK0),sK0)),
% 1.73/0.59    inference(subsumption_resolution,[],[f270,f227])).
% 1.73/0.59  fof(f270,plain,(
% 1.73/0.59    ~m1_subset_1(sK2(sK0),u1_pre_topc(sK0)) | u1_struct_0(sK0) != sK2(sK0) | v1_tops_1(sK2(sK0),sK0)),
% 1.73/0.59    inference(forward_demodulation,[],[f269,f180])).
% 1.73/0.59  fof(f269,plain,(
% 1.73/0.59    u1_struct_0(sK0) != sK2(sK0) | ~m1_subset_1(sK2(sK0),k9_setfam_1(u1_struct_0(sK0))) | v1_tops_1(sK2(sK0),sK0)),
% 1.73/0.59    inference(subsumption_resolution,[],[f268,f80])).
% 1.73/0.59  fof(f268,plain,(
% 1.73/0.59    u1_struct_0(sK0) != sK2(sK0) | ~m1_subset_1(sK2(sK0),k9_setfam_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v1_tops_1(sK2(sK0),sK0)),
% 1.73/0.59    inference(superposition,[],[f138,f263])).
% 1.73/0.59  fof(f263,plain,(
% 1.73/0.59    sK2(sK0) = k2_pre_topc(sK0,sK2(sK0))),
% 1.73/0.59    inference(subsumption_resolution,[],[f262,f77])).
% 1.73/0.59  fof(f262,plain,(
% 1.73/0.59    sK2(sK0) = k2_pre_topc(sK0,sK2(sK0)) | v2_struct_0(sK0)),
% 1.73/0.59    inference(subsumption_resolution,[],[f261,f80])).
% 1.73/0.59  fof(f261,plain,(
% 1.73/0.59    sK2(sK0) = k2_pre_topc(sK0,sK2(sK0)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.73/0.59    inference(subsumption_resolution,[],[f260,f78])).
% 1.73/0.59  fof(f260,plain,(
% 1.73/0.59    sK2(sK0) = k2_pre_topc(sK0,sK2(sK0)) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.73/0.59    inference(subsumption_resolution,[],[f259,f227])).
% 1.73/0.59  fof(f259,plain,(
% 1.73/0.59    ~m1_subset_1(sK2(sK0),u1_pre_topc(sK0)) | sK2(sK0) = k2_pre_topc(sK0,sK2(sK0)) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.73/0.59    inference(resolution,[],[f258,f109])).
% 1.73/0.59  fof(f109,plain,(
% 1.73/0.59    ( ! [X0] : (v4_pre_topc(sK2(X0),X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f61])).
% 1.73/0.59  % SZS output end Proof for theBenchmark
% 1.73/0.59  % (15559)------------------------------
% 1.73/0.59  % (15559)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.73/0.59  % (15559)Termination reason: Refutation
% 1.73/0.59  
% 1.73/0.59  % (15559)Memory used [KB]: 6652
% 1.73/0.59  % (15559)Time elapsed: 0.168 s
% 1.73/0.59  % (15559)------------------------------
% 1.73/0.59  % (15559)------------------------------
% 1.73/0.59  % (15552)Success in time 0.215 s
%------------------------------------------------------------------------------
