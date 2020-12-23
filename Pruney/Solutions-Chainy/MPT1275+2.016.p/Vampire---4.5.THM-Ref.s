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
% DateTime   : Thu Dec  3 13:12:44 EST 2020

% Result     : Theorem 1.33s
% Output     : Refutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 214 expanded)
%              Number of leaves         :   27 (  80 expanded)
%              Depth                    :   11
%              Number of atoms          :  369 ( 749 expanded)
%              Number of equality atoms :   83 ( 171 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f200,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f83,f88,f93,f102,f105,f119,f137,f148,f150,f160,f199])).

fof(f199,plain,
    ( ~ spl2_3
    | spl2_5
    | ~ spl2_8 ),
    inference(avatar_contradiction_clause,[],[f198])).

fof(f198,plain,
    ( $false
    | ~ spl2_3
    | spl2_5
    | ~ spl2_8 ),
    inference(subsumption_resolution,[],[f197,f100])).

fof(f100,plain,
    ( sK1 != k2_tops_1(sK0,sK1)
    | spl2_5 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl2_5
  <=> sK1 = k2_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

% (31366)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
fof(f197,plain,
    ( sK1 = k2_tops_1(sK0,sK1)
    | ~ spl2_3
    | ~ spl2_8 ),
    inference(backward_demodulation,[],[f159,f195])).

fof(f195,plain,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)
    | ~ spl2_3 ),
    inference(superposition,[],[f125,f129])).

fof(f129,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k1_enumset1(sK1,sK1,X0)))
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f92,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ) ),
    inference(definition_unfolding,[],[f69,f72])).

fof(f72,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f64,f71])).

fof(f71,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f62,f63])).

fof(f63,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f62,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f64,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f92,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f125,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,k1_xboole_0))) = X0 ),
    inference(forward_demodulation,[],[f122,f74])).

fof(f74,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f49,f73])).

% (31363)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
fof(f73,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f52,f50])).

fof(f50,plain,(
    ! [X0] : k1_subset_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_subset_1(X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(f52,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

fof(f49,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f122,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,k1_xboole_0))) ),
    inference(unit_resulting_resolution,[],[f51,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f65,f72])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f51,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f159,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl2_8
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

% (31341)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
fof(f160,plain,
    ( spl2_8
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f155,f134,f116,f90,f80,f157])).

fof(f80,plain,
    ( spl2_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f116,plain,
    ( spl2_6
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f134,plain,
    ( spl2_7
  <=> v2_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f155,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(backward_demodulation,[],[f141,f154])).

fof(f154,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(unit_resulting_resolution,[],[f82,f92,f135,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 = k1_tops_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

fof(f135,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f134])).

fof(f82,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f80])).

fof(f141,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f138,f118])).

fof(f118,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f116])).

fof(f138,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f82,f92,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(f150,plain,
    ( ~ spl2_1
    | ~ spl2_3
    | ~ spl2_4
    | spl2_7 ),
    inference(avatar_contradiction_clause,[],[f149])).

fof(f149,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_4
    | spl2_7 ),
    inference(subsumption_resolution,[],[f97,f145])).

fof(f145,plain,
    ( ~ v3_tops_1(sK1,sK0)
    | ~ spl2_1
    | ~ spl2_3
    | spl2_7 ),
    inference(unit_resulting_resolution,[],[f82,f92,f136,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v3_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
           => v2_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_tops_1)).

fof(f136,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | spl2_7 ),
    inference(avatar_component_clause,[],[f134])).

fof(f97,plain,
    ( v3_tops_1(sK1,sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl2_4
  <=> v3_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f148,plain,
    ( ~ spl2_1
    | ~ spl2_3
    | ~ spl2_5
    | spl2_7 ),
    inference(avatar_contradiction_clause,[],[f147])).

fof(f147,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_5
    | spl2_7 ),
    inference(subsumption_resolution,[],[f146,f77])).

fof(f77,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f146,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_5
    | spl2_7 ),
    inference(forward_demodulation,[],[f143,f101])).

fof(f101,plain,
    ( sK1 = k2_tops_1(sK0,sK1)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f99])).

fof(f143,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_1
    | ~ spl2_3
    | spl2_7 ),
    inference(unit_resulting_resolution,[],[f82,f92,f136,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ r1_tarski(X1,k2_tops_1(X0,X1)) )
            & ( r1_tarski(X1,k2_tops_1(X0,X1))
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tops_1)).

fof(f137,plain,
    ( ~ spl2_7
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_4 ),
    inference(avatar_split_clause,[],[f127,f95,f90,f85,f80,f134])).

fof(f85,plain,
    ( spl2_2
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f127,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_4 ),
    inference(unit_resulting_resolution,[],[f82,f96,f87,f92,f57])).

% (31366)Refutation not found, incomplete strategy% (31366)------------------------------
% (31366)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f57,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

% (31366)Termination reason: Refutation not found, incomplete strategy

% (31366)Memory used [KB]: 1663
% (31366)Time elapsed: 0.002 s
fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v2_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

% (31366)------------------------------
% (31366)------------------------------
fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v2_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v4_pre_topc(X1,X0)
              & v2_tops_1(X1,X0) )
           => v3_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_tops_1)).

fof(f87,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f85])).

fof(f96,plain,
    ( ~ v3_tops_1(sK1,sK0)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f95])).

fof(f119,plain,
    ( spl2_6
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f111,f90,f85,f80,f116])).

fof(f111,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f82,f87,f92,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f105,plain,
    ( ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f104,f99,f95])).

fof(f104,plain,
    ( ~ v3_tops_1(sK1,sK0)
    | ~ spl2_5 ),
    inference(trivial_inequality_removal,[],[f103])).

fof(f103,plain,
    ( sK1 != sK1
    | ~ v3_tops_1(sK1,sK0)
    | ~ spl2_5 ),
    inference(backward_demodulation,[],[f48,f101])).

fof(f48,plain,
    ( sK1 != k2_tops_1(sK0,sK1)
    | ~ v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ( sK1 != k2_tops_1(sK0,sK1)
      | ~ v3_tops_1(sK1,sK0) )
    & ( sK1 = k2_tops_1(sK0,sK1)
      | v3_tops_1(sK1,sK0) )
    & v4_pre_topc(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f38,f37])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != X1
              | ~ v3_tops_1(X1,X0) )
            & ( k2_tops_1(X0,X1) = X1
              | v3_tops_1(X1,X0) )
            & v4_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != X1
            | ~ v3_tops_1(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = X1
            | v3_tops_1(X1,sK0) )
          & v4_pre_topc(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != X1
          | ~ v3_tops_1(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = X1
          | v3_tops_1(X1,sK0) )
        & v4_pre_topc(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( sK1 != k2_tops_1(sK0,sK1)
        | ~ v3_tops_1(sK1,sK0) )
      & ( sK1 = k2_tops_1(sK0,sK1)
        | v3_tops_1(sK1,sK0) )
      & v4_pre_topc(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != X1
            | ~ v3_tops_1(X1,X0) )
          & ( k2_tops_1(X0,X1) = X1
            | v3_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != X1
            | ~ v3_tops_1(X1,X0) )
          & ( k2_tops_1(X0,X1) = X1
            | v3_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tops_1(X1,X0)
          <~> k2_tops_1(X0,X1) = X1 )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tops_1(X1,X0)
          <~> k2_tops_1(X0,X1) = X1 )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => ( v3_tops_1(X1,X0)
              <=> k2_tops_1(X0,X1) = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => ( v3_tops_1(X1,X0)
            <=> k2_tops_1(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_tops_1)).

fof(f102,plain,
    ( spl2_4
    | spl2_5 ),
    inference(avatar_split_clause,[],[f47,f99,f95])).

fof(f47,plain,
    ( sK1 = k2_tops_1(sK0,sK1)
    | v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f93,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f45,f90])).

fof(f45,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f88,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f46,f85])).

fof(f46,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f83,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f44,f80])).

fof(f44,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:49:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.51  % (31357)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.51  % (31338)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.51  % (31338)Refutation not found, incomplete strategy% (31338)------------------------------
% 0.21/0.51  % (31338)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (31338)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (31338)Memory used [KB]: 1663
% 0.21/0.51  % (31338)Time elapsed: 0.100 s
% 0.21/0.51  % (31338)------------------------------
% 0.21/0.51  % (31338)------------------------------
% 0.21/0.52  % (31349)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.52  % (31359)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.52  % (31337)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (31360)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.52  % (31342)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (31352)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.53  % (31345)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.53  % (31348)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.53  % (31340)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.33/0.53  % (31350)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.33/0.53  % (31346)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.33/0.53  % (31343)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.33/0.54  % (31357)Refutation found. Thanks to Tanya!
% 1.33/0.54  % SZS status Theorem for theBenchmark
% 1.33/0.54  % SZS output start Proof for theBenchmark
% 1.33/0.54  fof(f200,plain,(
% 1.33/0.54    $false),
% 1.33/0.54    inference(avatar_sat_refutation,[],[f83,f88,f93,f102,f105,f119,f137,f148,f150,f160,f199])).
% 1.33/0.54  fof(f199,plain,(
% 1.33/0.54    ~spl2_3 | spl2_5 | ~spl2_8),
% 1.33/0.54    inference(avatar_contradiction_clause,[],[f198])).
% 1.33/0.54  fof(f198,plain,(
% 1.33/0.54    $false | (~spl2_3 | spl2_5 | ~spl2_8)),
% 1.33/0.54    inference(subsumption_resolution,[],[f197,f100])).
% 1.33/0.54  fof(f100,plain,(
% 1.33/0.54    sK1 != k2_tops_1(sK0,sK1) | spl2_5),
% 1.33/0.54    inference(avatar_component_clause,[],[f99])).
% 1.33/0.54  fof(f99,plain,(
% 1.33/0.54    spl2_5 <=> sK1 = k2_tops_1(sK0,sK1)),
% 1.33/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 1.33/0.54  % (31366)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.33/0.54  fof(f197,plain,(
% 1.33/0.54    sK1 = k2_tops_1(sK0,sK1) | (~spl2_3 | ~spl2_8)),
% 1.33/0.54    inference(backward_demodulation,[],[f159,f195])).
% 1.33/0.54  fof(f195,plain,(
% 1.33/0.54    sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) | ~spl2_3),
% 1.33/0.54    inference(superposition,[],[f125,f129])).
% 1.33/0.54  fof(f129,plain,(
% 1.33/0.54    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k1_enumset1(sK1,sK1,X0)))) ) | ~spl2_3),
% 1.33/0.54    inference(unit_resulting_resolution,[],[f92,f76])).
% 1.33/0.54  fof(f76,plain,(
% 1.33/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))) )),
% 1.33/0.54    inference(definition_unfolding,[],[f69,f72])).
% 1.33/0.54  fof(f72,plain,(
% 1.33/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1)))) )),
% 1.33/0.54    inference(definition_unfolding,[],[f64,f71])).
% 1.33/0.54  fof(f71,plain,(
% 1.33/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 1.33/0.54    inference(definition_unfolding,[],[f62,f63])).
% 1.33/0.54  fof(f63,plain,(
% 1.33/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f3])).
% 1.33/0.54  fof(f3,axiom,(
% 1.33/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.33/0.54  fof(f62,plain,(
% 1.33/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.33/0.54    inference(cnf_transformation,[],[f10])).
% 1.33/0.54  fof(f10,axiom,(
% 1.33/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.33/0.54  fof(f64,plain,(
% 1.33/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.33/0.54    inference(cnf_transformation,[],[f2])).
% 1.33/0.54  fof(f2,axiom,(
% 1.33/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.33/0.54  fof(f69,plain,(
% 1.33/0.54    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.33/0.54    inference(cnf_transformation,[],[f32])).
% 1.33/0.54  fof(f32,plain,(
% 1.33/0.54    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.33/0.54    inference(ennf_transformation,[],[f7])).
% 1.33/0.54  fof(f7,axiom,(
% 1.33/0.54    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.33/0.54  fof(f92,plain,(
% 1.33/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 1.33/0.54    inference(avatar_component_clause,[],[f90])).
% 1.33/0.54  fof(f90,plain,(
% 1.33/0.54    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.33/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.33/0.54  fof(f125,plain,(
% 1.33/0.54    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,k1_xboole_0))) = X0) )),
% 1.33/0.54    inference(forward_demodulation,[],[f122,f74])).
% 1.33/0.54  fof(f74,plain,(
% 1.33/0.54    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 1.33/0.54    inference(definition_unfolding,[],[f49,f73])).
% 1.33/0.54  % (31363)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.33/0.54  fof(f73,plain,(
% 1.33/0.54    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 1.33/0.54    inference(definition_unfolding,[],[f52,f50])).
% 1.33/0.54  fof(f50,plain,(
% 1.33/0.54    ( ! [X0] : (k1_subset_1(X0) = k1_xboole_0) )),
% 1.33/0.54    inference(cnf_transformation,[],[f4])).
% 1.33/0.54  fof(f4,axiom,(
% 1.33/0.54    ! [X0] : k1_subset_1(X0) = k1_xboole_0),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).
% 1.33/0.54  fof(f52,plain,(
% 1.33/0.54    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 1.33/0.54    inference(cnf_transformation,[],[f8])).
% 1.33/0.54  fof(f8,axiom,(
% 1.33/0.54    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).
% 1.33/0.54  fof(f49,plain,(
% 1.33/0.54    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.33/0.54    inference(cnf_transformation,[],[f5])).
% 1.33/0.54  fof(f5,axiom,(
% 1.33/0.54    ! [X0] : k2_subset_1(X0) = X0),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.33/0.54  fof(f122,plain,(
% 1.33/0.54    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,k1_xboole_0)))) )),
% 1.33/0.54    inference(unit_resulting_resolution,[],[f51,f75])).
% 1.33/0.54  fof(f75,plain,(
% 1.33/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1)))) )),
% 1.33/0.54    inference(definition_unfolding,[],[f65,f72])).
% 1.33/0.54  fof(f65,plain,(
% 1.33/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.33/0.54    inference(cnf_transformation,[],[f31])).
% 1.33/0.54  fof(f31,plain,(
% 1.33/0.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.33/0.54    inference(ennf_transformation,[],[f6])).
% 1.33/0.54  fof(f6,axiom,(
% 1.33/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.33/0.54  fof(f51,plain,(
% 1.33/0.54    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.33/0.54    inference(cnf_transformation,[],[f9])).
% 1.33/0.54  fof(f9,axiom,(
% 1.33/0.54    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.33/0.54  fof(f159,plain,(
% 1.33/0.54    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) | ~spl2_8),
% 1.33/0.54    inference(avatar_component_clause,[],[f157])).
% 1.33/0.54  fof(f157,plain,(
% 1.33/0.54    spl2_8 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)),
% 1.33/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 1.33/0.54  % (31341)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.33/0.54  fof(f160,plain,(
% 1.33/0.54    spl2_8 | ~spl2_1 | ~spl2_3 | ~spl2_6 | ~spl2_7),
% 1.33/0.54    inference(avatar_split_clause,[],[f155,f134,f116,f90,f80,f157])).
% 1.33/0.54  fof(f80,plain,(
% 1.33/0.54    spl2_1 <=> l1_pre_topc(sK0)),
% 1.33/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.33/0.54  fof(f116,plain,(
% 1.33/0.54    spl2_6 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 1.33/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 1.33/0.54  fof(f134,plain,(
% 1.33/0.54    spl2_7 <=> v2_tops_1(sK1,sK0)),
% 1.33/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 1.33/0.54  fof(f155,plain,(
% 1.33/0.54    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) | (~spl2_1 | ~spl2_3 | ~spl2_6 | ~spl2_7)),
% 1.33/0.54    inference(backward_demodulation,[],[f141,f154])).
% 1.33/0.54  fof(f154,plain,(
% 1.33/0.54    k1_xboole_0 = k1_tops_1(sK0,sK1) | (~spl2_1 | ~spl2_3 | ~spl2_7)),
% 1.33/0.54    inference(unit_resulting_resolution,[],[f82,f92,f135,f58])).
% 1.33/0.54  fof(f58,plain,(
% 1.33/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = k1_tops_1(X0,X1)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f40])).
% 1.33/0.54  fof(f40,plain,(
% 1.33/0.54    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.33/0.54    inference(nnf_transformation,[],[f29])).
% 1.33/0.54  fof(f29,plain,(
% 1.33/0.54    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.33/0.54    inference(ennf_transformation,[],[f14])).
% 1.33/0.54  fof(f14,axiom,(
% 1.33/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).
% 1.33/0.54  fof(f135,plain,(
% 1.33/0.54    v2_tops_1(sK1,sK0) | ~spl2_7),
% 1.33/0.54    inference(avatar_component_clause,[],[f134])).
% 1.33/0.54  fof(f82,plain,(
% 1.33/0.54    l1_pre_topc(sK0) | ~spl2_1),
% 1.33/0.54    inference(avatar_component_clause,[],[f80])).
% 1.33/0.54  fof(f141,plain,(
% 1.33/0.54    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | (~spl2_1 | ~spl2_3 | ~spl2_6)),
% 1.33/0.54    inference(forward_demodulation,[],[f138,f118])).
% 1.33/0.54  fof(f118,plain,(
% 1.33/0.54    sK1 = k2_pre_topc(sK0,sK1) | ~spl2_6),
% 1.33/0.54    inference(avatar_component_clause,[],[f116])).
% 1.33/0.54  fof(f138,plain,(
% 1.33/0.54    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | (~spl2_1 | ~spl2_3)),
% 1.33/0.54    inference(unit_resulting_resolution,[],[f82,f92,f53])).
% 1.33/0.54  fof(f53,plain,(
% 1.33/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))) )),
% 1.33/0.54    inference(cnf_transformation,[],[f22])).
% 1.33/0.54  fof(f22,plain,(
% 1.33/0.54    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.33/0.54    inference(ennf_transformation,[],[f13])).
% 1.33/0.54  fof(f13,axiom,(
% 1.33/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 1.33/0.54  fof(f150,plain,(
% 1.33/0.54    ~spl2_1 | ~spl2_3 | ~spl2_4 | spl2_7),
% 1.33/0.54    inference(avatar_contradiction_clause,[],[f149])).
% 1.33/0.54  fof(f149,plain,(
% 1.33/0.54    $false | (~spl2_1 | ~spl2_3 | ~spl2_4 | spl2_7)),
% 1.33/0.54    inference(subsumption_resolution,[],[f97,f145])).
% 1.33/0.54  fof(f145,plain,(
% 1.33/0.54    ~v3_tops_1(sK1,sK0) | (~spl2_1 | ~spl2_3 | spl2_7)),
% 1.33/0.54    inference(unit_resulting_resolution,[],[f82,f92,f136,f56])).
% 1.33/0.54  fof(f56,plain,(
% 1.33/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tops_1(X1,X0)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f26])).
% 1.33/0.54  fof(f26,plain,(
% 1.33/0.54    ! [X0] : (! [X1] : (v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.33/0.54    inference(flattening,[],[f25])).
% 1.33/0.54  fof(f25,plain,(
% 1.33/0.54    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.33/0.54    inference(ennf_transformation,[],[f16])).
% 1.33/0.54  fof(f16,axiom,(
% 1.33/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v2_tops_1(X1,X0))))),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_tops_1)).
% 1.33/0.54  fof(f136,plain,(
% 1.33/0.54    ~v2_tops_1(sK1,sK0) | spl2_7),
% 1.33/0.54    inference(avatar_component_clause,[],[f134])).
% 1.33/0.54  fof(f97,plain,(
% 1.33/0.54    v3_tops_1(sK1,sK0) | ~spl2_4),
% 1.33/0.54    inference(avatar_component_clause,[],[f95])).
% 1.33/0.54  fof(f95,plain,(
% 1.33/0.54    spl2_4 <=> v3_tops_1(sK1,sK0)),
% 1.33/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 1.33/0.54  fof(f148,plain,(
% 1.33/0.54    ~spl2_1 | ~spl2_3 | ~spl2_5 | spl2_7),
% 1.33/0.54    inference(avatar_contradiction_clause,[],[f147])).
% 1.33/0.54  fof(f147,plain,(
% 1.33/0.54    $false | (~spl2_1 | ~spl2_3 | ~spl2_5 | spl2_7)),
% 1.33/0.54    inference(subsumption_resolution,[],[f146,f77])).
% 1.33/0.54  fof(f77,plain,(
% 1.33/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.33/0.54    inference(equality_resolution,[],[f67])).
% 1.33/0.54  fof(f67,plain,(
% 1.33/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.33/0.54    inference(cnf_transformation,[],[f43])).
% 1.33/0.54  fof(f43,plain,(
% 1.33/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.33/0.54    inference(flattening,[],[f42])).
% 1.33/0.54  fof(f42,plain,(
% 1.33/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.33/0.54    inference(nnf_transformation,[],[f1])).
% 1.33/0.54  fof(f1,axiom,(
% 1.33/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.33/0.54  fof(f146,plain,(
% 1.33/0.54    ~r1_tarski(sK1,sK1) | (~spl2_1 | ~spl2_3 | ~spl2_5 | spl2_7)),
% 1.33/0.54    inference(forward_demodulation,[],[f143,f101])).
% 1.33/0.54  fof(f101,plain,(
% 1.33/0.54    sK1 = k2_tops_1(sK0,sK1) | ~spl2_5),
% 1.33/0.54    inference(avatar_component_clause,[],[f99])).
% 1.33/0.54  fof(f143,plain,(
% 1.33/0.54    ~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | (~spl2_1 | ~spl2_3 | spl2_7)),
% 1.33/0.54    inference(unit_resulting_resolution,[],[f82,f92,f136,f61])).
% 1.33/0.54  fof(f61,plain,(
% 1.33/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~r1_tarski(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tops_1(X1,X0)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f41])).
% 1.33/0.54  fof(f41,plain,(
% 1.33/0.54    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~r1_tarski(X1,k2_tops_1(X0,X1))) & (r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.33/0.54    inference(nnf_transformation,[],[f30])).
% 1.33/0.54  fof(f30,plain,(
% 1.33/0.54    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.33/0.54    inference(ennf_transformation,[],[f15])).
% 1.33/0.54  fof(f15,axiom,(
% 1.33/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tops_1)).
% 1.33/0.54  fof(f137,plain,(
% 1.33/0.54    ~spl2_7 | ~spl2_1 | ~spl2_2 | ~spl2_3 | spl2_4),
% 1.33/0.54    inference(avatar_split_clause,[],[f127,f95,f90,f85,f80,f134])).
% 1.33/0.54  fof(f85,plain,(
% 1.33/0.54    spl2_2 <=> v4_pre_topc(sK1,sK0)),
% 1.33/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.33/0.54  fof(f127,plain,(
% 1.33/0.54    ~v2_tops_1(sK1,sK0) | (~spl2_1 | ~spl2_2 | ~spl2_3 | spl2_4)),
% 1.33/0.54    inference(unit_resulting_resolution,[],[f82,f96,f87,f92,f57])).
% 1.33/0.54  % (31366)Refutation not found, incomplete strategy% (31366)------------------------------
% 1.33/0.54  % (31366)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  fof(f57,plain,(
% 1.33/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_tops_1(X1,X0)) )),
% 1.33/0.54    inference(cnf_transformation,[],[f28])).
% 1.33/0.54  % (31366)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.54  
% 1.33/0.54  % (31366)Memory used [KB]: 1663
% 1.33/0.54  % (31366)Time elapsed: 0.002 s
% 1.33/0.54  fof(f28,plain,(
% 1.33/0.54    ! [X0] : (! [X1] : (v3_tops_1(X1,X0) | ~v4_pre_topc(X1,X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.33/0.54    inference(flattening,[],[f27])).
% 1.33/0.54  % (31366)------------------------------
% 1.33/0.54  % (31366)------------------------------
% 1.33/0.54  fof(f27,plain,(
% 1.33/0.54    ! [X0] : (! [X1] : ((v3_tops_1(X1,X0) | (~v4_pre_topc(X1,X0) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.33/0.54    inference(ennf_transformation,[],[f17])).
% 1.33/0.54  fof(f17,axiom,(
% 1.33/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X1,X0) & v2_tops_1(X1,X0)) => v3_tops_1(X1,X0))))),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_tops_1)).
% 1.33/0.54  fof(f87,plain,(
% 1.33/0.54    v4_pre_topc(sK1,sK0) | ~spl2_2),
% 1.33/0.54    inference(avatar_component_clause,[],[f85])).
% 1.33/0.54  fof(f96,plain,(
% 1.33/0.54    ~v3_tops_1(sK1,sK0) | spl2_4),
% 1.33/0.54    inference(avatar_component_clause,[],[f95])).
% 1.33/0.54  fof(f119,plain,(
% 1.33/0.54    spl2_6 | ~spl2_1 | ~spl2_2 | ~spl2_3),
% 1.33/0.54    inference(avatar_split_clause,[],[f111,f90,f85,f80,f116])).
% 1.33/0.54  fof(f111,plain,(
% 1.33/0.54    sK1 = k2_pre_topc(sK0,sK1) | (~spl2_1 | ~spl2_2 | ~spl2_3)),
% 1.33/0.54    inference(unit_resulting_resolution,[],[f82,f87,f92,f54])).
% 1.33/0.54  fof(f54,plain,(
% 1.33/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = X1) )),
% 1.33/0.54    inference(cnf_transformation,[],[f24])).
% 1.33/0.54  fof(f24,plain,(
% 1.33/0.54    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.33/0.54    inference(flattening,[],[f23])).
% 1.33/0.54  fof(f23,plain,(
% 1.33/0.54    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.33/0.54    inference(ennf_transformation,[],[f12])).
% 1.33/0.54  fof(f12,axiom,(
% 1.33/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 1.33/0.54  fof(f105,plain,(
% 1.33/0.54    ~spl2_4 | ~spl2_5),
% 1.33/0.54    inference(avatar_split_clause,[],[f104,f99,f95])).
% 1.33/0.54  fof(f104,plain,(
% 1.33/0.54    ~v3_tops_1(sK1,sK0) | ~spl2_5),
% 1.33/0.54    inference(trivial_inequality_removal,[],[f103])).
% 1.33/0.54  fof(f103,plain,(
% 1.33/0.54    sK1 != sK1 | ~v3_tops_1(sK1,sK0) | ~spl2_5),
% 1.33/0.54    inference(backward_demodulation,[],[f48,f101])).
% 1.33/0.54  fof(f48,plain,(
% 1.33/0.54    sK1 != k2_tops_1(sK0,sK1) | ~v3_tops_1(sK1,sK0)),
% 1.33/0.54    inference(cnf_transformation,[],[f39])).
% 1.33/0.54  fof(f39,plain,(
% 1.33/0.54    ((sK1 != k2_tops_1(sK0,sK1) | ~v3_tops_1(sK1,sK0)) & (sK1 = k2_tops_1(sK0,sK1) | v3_tops_1(sK1,sK0)) & v4_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 1.33/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f38,f37])).
% 1.33/0.54  fof(f37,plain,(
% 1.33/0.54    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != X1 | ~v3_tops_1(X1,sK0)) & (k2_tops_1(sK0,X1) = X1 | v3_tops_1(X1,sK0)) & v4_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 1.33/0.54    introduced(choice_axiom,[])).
% 1.33/0.54  fof(f38,plain,(
% 1.33/0.54    ? [X1] : ((k2_tops_1(sK0,X1) != X1 | ~v3_tops_1(X1,sK0)) & (k2_tops_1(sK0,X1) = X1 | v3_tops_1(X1,sK0)) & v4_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((sK1 != k2_tops_1(sK0,sK1) | ~v3_tops_1(sK1,sK0)) & (sK1 = k2_tops_1(sK0,sK1) | v3_tops_1(sK1,sK0)) & v4_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.33/0.54    introduced(choice_axiom,[])).
% 1.33/0.54  fof(f36,plain,(
% 1.33/0.54    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.33/0.54    inference(flattening,[],[f35])).
% 1.33/0.54  fof(f35,plain,(
% 1.33/0.54    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0))) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.33/0.54    inference(nnf_transformation,[],[f21])).
% 1.33/0.54  fof(f21,plain,(
% 1.33/0.54    ? [X0] : (? [X1] : ((v3_tops_1(X1,X0) <~> k2_tops_1(X0,X1) = X1) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.33/0.54    inference(flattening,[],[f20])).
% 1.33/0.54  fof(f20,plain,(
% 1.33/0.54    ? [X0] : (? [X1] : (((v3_tops_1(X1,X0) <~> k2_tops_1(X0,X1) = X1) & v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.33/0.54    inference(ennf_transformation,[],[f19])).
% 1.33/0.54  fof(f19,negated_conjecture,(
% 1.33/0.54    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => (v3_tops_1(X1,X0) <=> k2_tops_1(X0,X1) = X1))))),
% 1.33/0.54    inference(negated_conjecture,[],[f18])).
% 1.33/0.54  fof(f18,conjecture,(
% 1.33/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => (v3_tops_1(X1,X0) <=> k2_tops_1(X0,X1) = X1))))),
% 1.33/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_tops_1)).
% 1.33/0.54  fof(f102,plain,(
% 1.33/0.54    spl2_4 | spl2_5),
% 1.33/0.54    inference(avatar_split_clause,[],[f47,f99,f95])).
% 1.33/0.54  fof(f47,plain,(
% 1.33/0.54    sK1 = k2_tops_1(sK0,sK1) | v3_tops_1(sK1,sK0)),
% 1.33/0.54    inference(cnf_transformation,[],[f39])).
% 1.33/0.54  fof(f93,plain,(
% 1.33/0.54    spl2_3),
% 1.33/0.54    inference(avatar_split_clause,[],[f45,f90])).
% 1.33/0.54  fof(f45,plain,(
% 1.33/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.33/0.54    inference(cnf_transformation,[],[f39])).
% 1.33/0.54  fof(f88,plain,(
% 1.33/0.54    spl2_2),
% 1.33/0.54    inference(avatar_split_clause,[],[f46,f85])).
% 1.33/0.54  fof(f46,plain,(
% 1.33/0.54    v4_pre_topc(sK1,sK0)),
% 1.33/0.54    inference(cnf_transformation,[],[f39])).
% 1.33/0.54  fof(f83,plain,(
% 1.33/0.54    spl2_1),
% 1.33/0.54    inference(avatar_split_clause,[],[f44,f80])).
% 1.33/0.54  fof(f44,plain,(
% 1.33/0.54    l1_pre_topc(sK0)),
% 1.33/0.54    inference(cnf_transformation,[],[f39])).
% 1.33/0.54  % SZS output end Proof for theBenchmark
% 1.33/0.54  % (31357)------------------------------
% 1.33/0.54  % (31357)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (31357)Termination reason: Refutation
% 1.33/0.54  
% 1.33/0.54  % (31357)Memory used [KB]: 10874
% 1.33/0.54  % (31357)Time elapsed: 0.135 s
% 1.33/0.54  % (31357)------------------------------
% 1.33/0.54  % (31357)------------------------------
% 1.33/0.54  % (31336)Success in time 0.18 s
%------------------------------------------------------------------------------
