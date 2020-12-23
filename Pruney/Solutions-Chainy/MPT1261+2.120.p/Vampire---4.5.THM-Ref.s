%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:06 EST 2020

% Result     : Theorem 54.15s
% Output     : Refutation 54.15s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 331 expanded)
%              Number of leaves         :   41 ( 134 expanded)
%              Depth                    :   12
%              Number of atoms          :  420 ( 911 expanded)
%              Number of equality atoms :  108 ( 252 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f64462,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f83,f88,f27463,f39347,f39358,f39384,f40078,f40089,f40102,f40114,f40156,f40164,f56703,f57761,f57772,f58197,f58820,f60759,f60761,f61229,f62135,f64461])).

fof(f64461,plain,
    ( spl2_181
    | ~ spl2_193 ),
    inference(avatar_contradiction_clause,[],[f64460])).

fof(f64460,plain,
    ( $false
    | spl2_181
    | ~ spl2_193 ),
    inference(global_subsumption,[],[f57955,f64043])).

fof(f64043,plain,
    ( sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_193 ),
    inference(superposition,[],[f206,f61228])).

fof(f61228,plain,
    ( sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_193 ),
    inference(avatar_component_clause,[],[f61226])).

fof(f61226,plain,
    ( spl2_193
  <=> sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_193])])).

fof(f206,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[],[f66,f54])).

fof(f54,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f66,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f57955,plain,
    ( sK1 != k2_xboole_0(k2_tops_1(sK0,sK1),sK1)
    | spl2_181 ),
    inference(avatar_component_clause,[],[f57954])).

fof(f57954,plain,
    ( spl2_181
  <=> sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_181])])).

fof(f62135,plain,
    ( ~ spl2_2
    | ~ spl2_3
    | spl2_26
    | ~ spl2_89 ),
    inference(avatar_contradiction_clause,[],[f62134])).

fof(f62134,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_3
    | spl2_26
    | ~ spl2_89 ),
    inference(global_subsumption,[],[f27461,f62085])).

fof(f62085,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_89 ),
    inference(forward_demodulation,[],[f62083,f40163])).

fof(f40163,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_89 ),
    inference(avatar_component_clause,[],[f40161])).

fof(f40161,plain,
    ( spl2_89
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_89])])).

fof(f62083,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f82,f87,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f87,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f82,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl2_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f27461,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | spl2_26 ),
    inference(avatar_component_clause,[],[f27460])).

fof(f27460,plain,
    ( spl2_26
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f61229,plain,
    ( spl2_193
    | ~ spl2_84
    | ~ spl2_85
    | ~ spl2_88 ),
    inference(avatar_split_clause,[],[f60849,f40153,f40111,f40099,f61226])).

fof(f40099,plain,
    ( spl2_84
  <=> r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_84])])).

fof(f40111,plain,
    ( spl2_85
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_85])])).

fof(f40153,plain,
    ( spl2_88
  <=> m1_subset_1(k3_subset_1(sK1,k2_tops_1(sK0,sK1)),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_88])])).

fof(f60849,plain,
    ( sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_84
    | ~ spl2_85
    | ~ spl2_88 ),
    inference(forward_demodulation,[],[f60804,f60787])).

fof(f60787,plain,
    ( sK1 = k4_subset_1(sK1,k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_84 ),
    inference(unit_resulting_resolution,[],[f40101,f2411])).

fof(f2411,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0 ) ),
    inference(resolution,[],[f73,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0 ) ),
    inference(forward_demodulation,[],[f61,f49])).

fof(f49,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f61,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

fof(f40101,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_84 ),
    inference(avatar_component_clause,[],[f40099])).

fof(f60804,plain,
    ( k4_subset_1(sK1,k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1))) = k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_85
    | ~ spl2_88 ),
    inference(unit_resulting_resolution,[],[f40155,f40113,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f40113,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_85 ),
    inference(avatar_component_clause,[],[f40111])).

fof(f40155,plain,
    ( m1_subset_1(k3_subset_1(sK1,k2_tops_1(sK0,sK1)),k1_zfmisc_1(sK1))
    | ~ spl2_88 ),
    inference(avatar_component_clause,[],[f40153])).

fof(f60761,plain,
    ( k2_pre_topc(sK0,sK1) != k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) != k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | sK1 != k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f60759,plain,
    ( k2_pre_topc(sK0,sK1) != k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) != k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | sK1 != k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0)
    | ~ v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f58820,plain,
    ( spl2_188
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f57754,f85,f80,f58817])).

fof(f58817,plain,
    ( spl2_188
  <=> k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_188])])).

fof(f57754,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f82,f87,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f58197,plain,
    ( spl2_180
    | ~ spl2_181 ),
    inference(avatar_contradiction_clause,[],[f58196])).

fof(f58196,plain,
    ( $false
    | spl2_180
    | ~ spl2_181 ),
    inference(global_subsumption,[],[f58125,f57768])).

fof(f57768,plain,
    ( sK1 != k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | spl2_180 ),
    inference(avatar_component_clause,[],[f57767])).

fof(f57767,plain,
    ( spl2_180
  <=> sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_180])])).

fof(f58125,plain,
    ( sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_181 ),
    inference(forward_demodulation,[],[f58064,f54])).

fof(f58064,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,sK1)
    | ~ spl2_181 ),
    inference(superposition,[],[f5742,f57956])).

fof(f57956,plain,
    ( sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_181 ),
    inference(avatar_component_clause,[],[f57954])).

fof(f5742,plain,(
    ! [X37,X38] : k2_xboole_0(X38,X37) = k2_xboole_0(k2_xboole_0(X37,X38),X38) ),
    inference(forward_demodulation,[],[f5520,f457])).

fof(f457,plain,(
    ! [X30,X29] : k2_xboole_0(X29,X30) = k2_xboole_0(k2_xboole_0(X30,X29),k2_xboole_0(X29,X30)) ),
    inference(superposition,[],[f219,f358])).

fof(f358,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f211,f206])).

fof(f211,plain,(
    ! [X6,X7,X5] : k2_xboole_0(X5,k2_xboole_0(X6,X7)) = k2_xboole_0(X7,k2_xboole_0(X5,X6)) ),
    inference(superposition,[],[f66,f56])).

fof(f56,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f219,plain,(
    ! [X2,X1] : k2_xboole_0(X2,X1) = k2_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f206,f56])).

fof(f5520,plain,(
    ! [X37,X38] : k2_xboole_0(k2_xboole_0(X37,X38),X38) = k2_xboole_0(k2_xboole_0(X37,X38),k2_xboole_0(X38,X37)) ),
    inference(superposition,[],[f456,f206])).

fof(f456,plain,(
    ! [X28,X26,X27] : k2_xboole_0(k2_xboole_0(X27,X26),k2_xboole_0(X28,X26)) = k2_xboole_0(X28,k2_xboole_0(X26,X27)) ),
    inference(superposition,[],[f211,f358])).

fof(f57772,plain,
    ( spl2_180
    | ~ spl2_163
    | ~ spl2_178 ),
    inference(avatar_split_clause,[],[f57770,f57758,f56700,f57767])).

fof(f56700,plain,
    ( spl2_163
  <=> k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_163])])).

fof(f57758,plain,
    ( spl2_178
  <=> sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_178])])).

fof(f57770,plain,
    ( sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_163
    | ~ spl2_178 ),
    inference(superposition,[],[f57760,f56702])).

fof(f56702,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_163 ),
    inference(avatar_component_clause,[],[f56700])).

fof(f57760,plain,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_178 ),
    inference(avatar_component_clause,[],[f57758])).

fof(f57761,plain,
    ( spl2_178
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_89 ),
    inference(avatar_split_clause,[],[f57756,f40161,f85,f80,f57758])).

fof(f57756,plain,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_89 ),
    inference(forward_demodulation,[],[f57754,f40163])).

fof(f56703,plain,
    ( spl2_163
    | ~ spl2_3
    | ~ spl2_32 ),
    inference(avatar_split_clause,[],[f41186,f39381,f85,f56700])).

fof(f39381,plain,
    ( spl2_32
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f41186,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_32 ),
    inference(unit_resulting_resolution,[],[f87,f39383,f68])).

fof(f39383,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_32 ),
    inference(avatar_component_clause,[],[f39381])).

fof(f40164,plain,
    ( spl2_89
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_25 ),
    inference(avatar_split_clause,[],[f40158,f27456,f85,f80,f40161])).

fof(f27456,plain,
    ( spl2_25
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f40158,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_25 ),
    inference(unit_resulting_resolution,[],[f82,f87,f27458,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f27])).

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
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f27458,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_25 ),
    inference(avatar_component_clause,[],[f27456])).

fof(f40156,plain,
    ( spl2_88
    | ~ spl2_85 ),
    inference(avatar_split_clause,[],[f40119,f40111,f40153])).

fof(f40119,plain,
    ( m1_subset_1(k3_subset_1(sK1,k2_tops_1(sK0,sK1)),k1_zfmisc_1(sK1))
    | ~ spl2_85 ),
    inference(unit_resulting_resolution,[],[f40113,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f40114,plain,
    ( spl2_85
    | ~ spl2_84 ),
    inference(avatar_split_clause,[],[f40106,f40099,f40111])).

fof(f40106,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_84 ),
    inference(unit_resulting_resolution,[],[f40101,f65])).

fof(f40102,plain,
    ( spl2_84
    | ~ spl2_26
    | ~ spl2_83 ),
    inference(avatar_split_clause,[],[f40097,f40087,f27460,f40099])).

fof(f40087,plain,
    ( spl2_83
  <=> ! [X5] : r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X5),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_83])])).

fof(f40097,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_26
    | ~ spl2_83 ),
    inference(superposition,[],[f40088,f27462])).

fof(f27462,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f27460])).

fof(f40088,plain,
    ( ! [X5] : r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X5),sK1)
    | ~ spl2_83 ),
    inference(avatar_component_clause,[],[f40087])).

fof(f40089,plain,
    ( spl2_83
    | ~ spl2_82 ),
    inference(avatar_split_clause,[],[f40085,f40076,f40087])).

fof(f40076,plain,
    ( spl2_82
  <=> ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_82])])).

fof(f40085,plain,
    ( ! [X5] : r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X5),sK1)
    | ~ spl2_82 ),
    inference(superposition,[],[f70,f40077])).

fof(f40077,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0)))
    | ~ spl2_82 ),
    inference(avatar_component_clause,[],[f40076])).

fof(f70,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
    inference(definition_unfolding,[],[f55,f69])).

fof(f69,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f58,f57])).

fof(f57,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f58,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f55,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f40078,plain,
    ( spl2_82
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f40045,f85,f40076])).

fof(f40045,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0)))
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f87,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ) ),
    inference(definition_unfolding,[],[f67,f69])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f39384,plain,
    ( spl2_32
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f39373,f85,f80,f39381])).

fof(f39373,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f82,f87,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f39358,plain,
    ( spl2_28
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f39348,f85,f80,f75,f39355])).

fof(f39355,plain,
    ( spl2_28
  <=> v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f75,plain,
    ( spl2_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f39348,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f77,f82,f87,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

fof(f77,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f39347,plain,
    ( ~ spl2_25
    | ~ spl2_26 ),
    inference(avatar_split_clause,[],[f48,f27460,f27456])).

fof(f48,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f39,f41,f40])).

fof(f40,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
              | ~ v4_pre_topc(X1,X0) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
              | v4_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
            | ~ v4_pre_topc(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
            | v4_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
          | ~ v4_pre_topc(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
          | v4_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
        | ~ v4_pre_topc(sK1,sK0) )
      & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
        | v4_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

fof(f27463,plain,
    ( spl2_25
    | spl2_26 ),
    inference(avatar_split_clause,[],[f47,f27460,f27456])).

fof(f47,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f88,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f46,f85])).

fof(f46,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f42])).

fof(f83,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f45,f80])).

fof(f45,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f78,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f44,f75])).

fof(f44,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:47:14 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (8890)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.47  % (8895)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.47  % (8886)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.47  % (8887)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (8885)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.47  % (8898)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.48  % (8888)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (8900)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.48  % (8892)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.48  % (8896)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.48  % (8884)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.48  % (8894)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.48  % (8883)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.48  % (8893)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.49  % (8899)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.49  % (8889)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.49  % (8897)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 1.36/0.53  % (8891)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 5.47/1.05  % (8887)Time limit reached!
% 5.47/1.05  % (8887)------------------------------
% 5.47/1.05  % (8887)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.47/1.07  % (8887)Termination reason: Time limit
% 5.47/1.07  
% 5.47/1.07  % (8887)Memory used [KB]: 21492
% 5.47/1.07  % (8887)Time elapsed: 0.632 s
% 5.47/1.07  % (8887)------------------------------
% 5.47/1.07  % (8887)------------------------------
% 12.87/2.00  % (8889)Time limit reached!
% 12.87/2.00  % (8889)------------------------------
% 12.87/2.00  % (8889)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.87/2.00  % (8889)Termination reason: Time limit
% 12.87/2.00  
% 12.87/2.00  % (8889)Memory used [KB]: 39914
% 12.87/2.00  % (8889)Time elapsed: 1.580 s
% 12.87/2.00  % (8889)------------------------------
% 12.87/2.00  % (8889)------------------------------
% 14.01/2.12  % (8888)Time limit reached!
% 14.01/2.12  % (8888)------------------------------
% 14.01/2.12  % (8888)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.01/2.12  % (8888)Termination reason: Time limit
% 14.01/2.12  % (8888)Termination phase: Saturation
% 14.01/2.12  
% 14.01/2.12  % (8888)Memory used [KB]: 65755
% 14.01/2.12  % (8888)Time elapsed: 1.500 s
% 14.01/2.12  % (8888)------------------------------
% 14.01/2.12  % (8888)------------------------------
% 14.37/2.22  % (8885)Time limit reached!
% 14.37/2.22  % (8885)------------------------------
% 14.37/2.22  % (8885)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.37/2.22  % (8885)Termination reason: Time limit
% 14.37/2.22  % (8885)Termination phase: Saturation
% 14.37/2.22  
% 14.37/2.22  % (8885)Memory used [KB]: 27760
% 14.37/2.22  % (8885)Time elapsed: 1.800 s
% 14.37/2.22  % (8885)------------------------------
% 14.37/2.22  % (8885)------------------------------
% 18.27/2.72  % (8895)Time limit reached!
% 18.27/2.72  % (8895)------------------------------
% 18.27/2.72  % (8895)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 18.27/2.72  % (8895)Termination reason: Time limit
% 18.27/2.72  
% 18.27/2.72  % (8895)Memory used [KB]: 66395
% 18.27/2.72  % (8895)Time elapsed: 2.296 s
% 18.27/2.72  % (8895)------------------------------
% 18.27/2.72  % (8895)------------------------------
% 54.15/7.18  % (8900)Refutation found. Thanks to Tanya!
% 54.15/7.18  % SZS status Theorem for theBenchmark
% 54.15/7.18  % SZS output start Proof for theBenchmark
% 54.15/7.18  fof(f64462,plain,(
% 54.15/7.18    $false),
% 54.15/7.18    inference(avatar_sat_refutation,[],[f78,f83,f88,f27463,f39347,f39358,f39384,f40078,f40089,f40102,f40114,f40156,f40164,f56703,f57761,f57772,f58197,f58820,f60759,f60761,f61229,f62135,f64461])).
% 54.15/7.18  fof(f64461,plain,(
% 54.15/7.18    spl2_181 | ~spl2_193),
% 54.15/7.18    inference(avatar_contradiction_clause,[],[f64460])).
% 54.15/7.18  fof(f64460,plain,(
% 54.15/7.18    $false | (spl2_181 | ~spl2_193)),
% 54.15/7.18    inference(global_subsumption,[],[f57955,f64043])).
% 54.15/7.18  fof(f64043,plain,(
% 54.15/7.18    sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),sK1) | ~spl2_193),
% 54.15/7.18    inference(superposition,[],[f206,f61228])).
% 54.15/7.18  fof(f61228,plain,(
% 54.15/7.18    sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1))) | ~spl2_193),
% 54.15/7.18    inference(avatar_component_clause,[],[f61226])).
% 54.15/7.18  fof(f61226,plain,(
% 54.15/7.18    spl2_193 <=> sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1)))),
% 54.15/7.18    introduced(avatar_definition,[new_symbols(naming,[spl2_193])])).
% 54.15/7.18  fof(f206,plain,(
% 54.15/7.18    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 54.15/7.18    inference(superposition,[],[f66,f54])).
% 54.15/7.18  fof(f54,plain,(
% 54.15/7.18    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 54.15/7.18    inference(cnf_transformation,[],[f21])).
% 54.15/7.18  fof(f21,plain,(
% 54.15/7.18    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 54.15/7.18    inference(rectify,[],[f2])).
% 54.15/7.18  fof(f2,axiom,(
% 54.15/7.18    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 54.15/7.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 54.15/7.18  fof(f66,plain,(
% 54.15/7.18    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 54.15/7.18    inference(cnf_transformation,[],[f6])).
% 54.15/7.18  fof(f6,axiom,(
% 54.15/7.18    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 54.15/7.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 54.15/7.18  fof(f57955,plain,(
% 54.15/7.18    sK1 != k2_xboole_0(k2_tops_1(sK0,sK1),sK1) | spl2_181),
% 54.15/7.18    inference(avatar_component_clause,[],[f57954])).
% 54.15/7.18  fof(f57954,plain,(
% 54.15/7.18    spl2_181 <=> sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),sK1)),
% 54.15/7.18    introduced(avatar_definition,[new_symbols(naming,[spl2_181])])).
% 54.15/7.18  fof(f62135,plain,(
% 54.15/7.18    ~spl2_2 | ~spl2_3 | spl2_26 | ~spl2_89),
% 54.15/7.18    inference(avatar_contradiction_clause,[],[f62134])).
% 54.15/7.19  fof(f62134,plain,(
% 54.15/7.19    $false | (~spl2_2 | ~spl2_3 | spl2_26 | ~spl2_89)),
% 54.15/7.19    inference(global_subsumption,[],[f27461,f62085])).
% 54.15/7.19  fof(f62085,plain,(
% 54.15/7.19    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3 | ~spl2_89)),
% 54.15/7.19    inference(forward_demodulation,[],[f62083,f40163])).
% 54.15/7.19  fof(f40163,plain,(
% 54.15/7.19    sK1 = k2_pre_topc(sK0,sK1) | ~spl2_89),
% 54.15/7.19    inference(avatar_component_clause,[],[f40161])).
% 54.15/7.19  fof(f40161,plain,(
% 54.15/7.19    spl2_89 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 54.15/7.19    introduced(avatar_definition,[new_symbols(naming,[spl2_89])])).
% 54.15/7.19  fof(f62083,plain,(
% 54.15/7.19    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3)),
% 54.15/7.19    inference(unit_resulting_resolution,[],[f82,f87,f51])).
% 54.15/7.19  fof(f51,plain,(
% 54.15/7.19    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))) )),
% 54.15/7.19    inference(cnf_transformation,[],[f25])).
% 54.15/7.19  fof(f25,plain,(
% 54.15/7.19    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 54.15/7.19    inference(ennf_transformation,[],[f17])).
% 54.15/7.19  fof(f17,axiom,(
% 54.15/7.19    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 54.15/7.19    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 54.15/7.19  fof(f87,plain,(
% 54.15/7.19    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 54.15/7.19    inference(avatar_component_clause,[],[f85])).
% 54.15/7.19  fof(f85,plain,(
% 54.15/7.19    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 54.15/7.19    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 54.15/7.19  fof(f82,plain,(
% 54.15/7.19    l1_pre_topc(sK0) | ~spl2_2),
% 54.15/7.19    inference(avatar_component_clause,[],[f80])).
% 54.15/7.19  fof(f80,plain,(
% 54.15/7.19    spl2_2 <=> l1_pre_topc(sK0)),
% 54.15/7.19    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 54.15/7.19  fof(f27461,plain,(
% 54.15/7.19    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | spl2_26),
% 54.15/7.19    inference(avatar_component_clause,[],[f27460])).
% 54.15/7.19  fof(f27460,plain,(
% 54.15/7.19    spl2_26 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 54.15/7.19    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 54.15/7.19  fof(f61229,plain,(
% 54.15/7.19    spl2_193 | ~spl2_84 | ~spl2_85 | ~spl2_88),
% 54.15/7.19    inference(avatar_split_clause,[],[f60849,f40153,f40111,f40099,f61226])).
% 54.15/7.19  fof(f40099,plain,(
% 54.15/7.19    spl2_84 <=> r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 54.15/7.19    introduced(avatar_definition,[new_symbols(naming,[spl2_84])])).
% 54.15/7.19  fof(f40111,plain,(
% 54.15/7.19    spl2_85 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))),
% 54.15/7.19    introduced(avatar_definition,[new_symbols(naming,[spl2_85])])).
% 54.15/7.19  fof(f40153,plain,(
% 54.15/7.19    spl2_88 <=> m1_subset_1(k3_subset_1(sK1,k2_tops_1(sK0,sK1)),k1_zfmisc_1(sK1))),
% 54.15/7.19    introduced(avatar_definition,[new_symbols(naming,[spl2_88])])).
% 54.15/7.19  fof(f60849,plain,(
% 54.15/7.19    sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1))) | (~spl2_84 | ~spl2_85 | ~spl2_88)),
% 54.15/7.19    inference(forward_demodulation,[],[f60804,f60787])).
% 54.15/7.19  fof(f60787,plain,(
% 54.15/7.19    sK1 = k4_subset_1(sK1,k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1))) | ~spl2_84),
% 54.15/7.19    inference(unit_resulting_resolution,[],[f40101,f2411])).
% 54.15/7.19  fof(f2411,plain,(
% 54.15/7.19    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0) )),
% 54.15/7.19    inference(resolution,[],[f73,f65])).
% 54.15/7.19  fof(f65,plain,(
% 54.15/7.19    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 54.15/7.19    inference(cnf_transformation,[],[f43])).
% 54.15/7.19  fof(f43,plain,(
% 54.15/7.19    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 54.15/7.19    inference(nnf_transformation,[],[f13])).
% 54.15/7.19  fof(f13,axiom,(
% 54.15/7.19    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 54.15/7.19    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 54.15/7.19  fof(f73,plain,(
% 54.15/7.19    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0) )),
% 54.15/7.19    inference(forward_demodulation,[],[f61,f49])).
% 54.15/7.19  fof(f49,plain,(
% 54.15/7.19    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 54.15/7.19    inference(cnf_transformation,[],[f7])).
% 54.15/7.19  fof(f7,axiom,(
% 54.15/7.19    ! [X0] : k2_subset_1(X0) = X0),
% 54.15/7.19    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 54.15/7.19  fof(f61,plain,(
% 54.15/7.19    ( ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 54.15/7.19    inference(cnf_transformation,[],[f30])).
% 54.15/7.19  fof(f30,plain,(
% 54.15/7.19    ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 54.15/7.19    inference(ennf_transformation,[],[f11])).
% 54.15/7.19  fof(f11,axiom,(
% 54.15/7.19    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 54.15/7.19    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).
% 54.15/7.19  fof(f40101,plain,(
% 54.15/7.19    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl2_84),
% 54.15/7.19    inference(avatar_component_clause,[],[f40099])).
% 54.15/7.19  fof(f60804,plain,(
% 54.15/7.19    k4_subset_1(sK1,k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1))) = k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1))) | (~spl2_85 | ~spl2_88)),
% 54.15/7.19    inference(unit_resulting_resolution,[],[f40155,f40113,f68])).
% 54.15/7.19  fof(f68,plain,(
% 54.15/7.19    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)) )),
% 54.15/7.19    inference(cnf_transformation,[],[f37])).
% 54.15/7.19  fof(f37,plain,(
% 54.15/7.19    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 54.15/7.19    inference(flattening,[],[f36])).
% 54.15/7.19  fof(f36,plain,(
% 54.15/7.19    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 54.15/7.19    inference(ennf_transformation,[],[f9])).
% 54.15/7.19  fof(f9,axiom,(
% 54.15/7.19    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 54.15/7.19    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 54.15/7.19  fof(f40113,plain,(
% 54.15/7.19    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_85),
% 54.15/7.19    inference(avatar_component_clause,[],[f40111])).
% 54.15/7.19  fof(f40155,plain,(
% 54.15/7.19    m1_subset_1(k3_subset_1(sK1,k2_tops_1(sK0,sK1)),k1_zfmisc_1(sK1)) | ~spl2_88),
% 54.15/7.19    inference(avatar_component_clause,[],[f40153])).
% 54.15/7.19  fof(f60761,plain,(
% 54.15/7.19    k2_pre_topc(sK0,sK1) != k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) != k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | sK1 != k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | sK1 = k2_pre_topc(sK0,sK1)),
% 54.15/7.19    introduced(theory_tautology_sat_conflict,[])).
% 54.15/7.19  fof(f60759,plain,(
% 54.15/7.19    k2_pre_topc(sK0,sK1) != k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) != k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | sK1 != k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0) | ~v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)),
% 54.15/7.19    introduced(theory_tautology_sat_conflict,[])).
% 54.15/7.19  fof(f58820,plain,(
% 54.15/7.19    spl2_188 | ~spl2_2 | ~spl2_3),
% 54.15/7.19    inference(avatar_split_clause,[],[f57754,f85,f80,f58817])).
% 54.15/7.19  fof(f58817,plain,(
% 54.15/7.19    spl2_188 <=> k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 54.15/7.19    introduced(avatar_definition,[new_symbols(naming,[spl2_188])])).
% 54.15/7.19  fof(f57754,plain,(
% 54.15/7.19    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3)),
% 54.15/7.19    inference(unit_resulting_resolution,[],[f82,f87,f50])).
% 54.15/7.19  fof(f50,plain,(
% 54.15/7.19    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 54.15/7.19    inference(cnf_transformation,[],[f24])).
% 54.15/7.19  fof(f24,plain,(
% 54.15/7.19    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 54.15/7.19    inference(ennf_transformation,[],[f18])).
% 54.15/7.19  fof(f18,axiom,(
% 54.15/7.19    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 54.15/7.19    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 54.15/7.19  fof(f58197,plain,(
% 54.15/7.19    spl2_180 | ~spl2_181),
% 54.15/7.19    inference(avatar_contradiction_clause,[],[f58196])).
% 54.15/7.19  fof(f58196,plain,(
% 54.15/7.19    $false | (spl2_180 | ~spl2_181)),
% 54.15/7.19    inference(global_subsumption,[],[f58125,f57768])).
% 54.15/7.19  fof(f57768,plain,(
% 54.15/7.19    sK1 != k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | spl2_180),
% 54.15/7.19    inference(avatar_component_clause,[],[f57767])).
% 54.15/7.19  fof(f57767,plain,(
% 54.15/7.19    spl2_180 <=> sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 54.15/7.19    introduced(avatar_definition,[new_symbols(naming,[spl2_180])])).
% 54.15/7.19  fof(f58125,plain,(
% 54.15/7.19    sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_181),
% 54.15/7.19    inference(forward_demodulation,[],[f58064,f54])).
% 54.15/7.19  fof(f58064,plain,(
% 54.15/7.19    k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,sK1) | ~spl2_181),
% 54.15/7.19    inference(superposition,[],[f5742,f57956])).
% 54.15/7.19  fof(f57956,plain,(
% 54.15/7.19    sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),sK1) | ~spl2_181),
% 54.15/7.19    inference(avatar_component_clause,[],[f57954])).
% 54.15/7.19  fof(f5742,plain,(
% 54.15/7.19    ( ! [X37,X38] : (k2_xboole_0(X38,X37) = k2_xboole_0(k2_xboole_0(X37,X38),X38)) )),
% 54.15/7.19    inference(forward_demodulation,[],[f5520,f457])).
% 54.15/7.19  fof(f457,plain,(
% 54.15/7.19    ( ! [X30,X29] : (k2_xboole_0(X29,X30) = k2_xboole_0(k2_xboole_0(X30,X29),k2_xboole_0(X29,X30))) )),
% 54.15/7.19    inference(superposition,[],[f219,f358])).
% 54.15/7.19  fof(f358,plain,(
% 54.15/7.19    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X1,X0))) )),
% 54.15/7.19    inference(superposition,[],[f211,f206])).
% 54.15/7.19  fof(f211,plain,(
% 54.15/7.19    ( ! [X6,X7,X5] : (k2_xboole_0(X5,k2_xboole_0(X6,X7)) = k2_xboole_0(X7,k2_xboole_0(X5,X6))) )),
% 54.15/7.19    inference(superposition,[],[f66,f56])).
% 54.15/7.19  fof(f56,plain,(
% 54.15/7.19    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 54.15/7.19    inference(cnf_transformation,[],[f1])).
% 54.15/7.19  fof(f1,axiom,(
% 54.15/7.19    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 54.15/7.19    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 54.15/7.19  fof(f219,plain,(
% 54.15/7.19    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = k2_xboole_0(X1,k2_xboole_0(X2,X1))) )),
% 54.15/7.19    inference(superposition,[],[f206,f56])).
% 54.15/7.19  fof(f5520,plain,(
% 54.15/7.19    ( ! [X37,X38] : (k2_xboole_0(k2_xboole_0(X37,X38),X38) = k2_xboole_0(k2_xboole_0(X37,X38),k2_xboole_0(X38,X37))) )),
% 54.15/7.19    inference(superposition,[],[f456,f206])).
% 54.15/7.19  fof(f456,plain,(
% 54.15/7.19    ( ! [X28,X26,X27] : (k2_xboole_0(k2_xboole_0(X27,X26),k2_xboole_0(X28,X26)) = k2_xboole_0(X28,k2_xboole_0(X26,X27))) )),
% 54.15/7.19    inference(superposition,[],[f211,f358])).
% 54.15/7.19  fof(f57772,plain,(
% 54.15/7.19    spl2_180 | ~spl2_163 | ~spl2_178),
% 54.15/7.19    inference(avatar_split_clause,[],[f57770,f57758,f56700,f57767])).
% 54.15/7.19  fof(f56700,plain,(
% 54.15/7.19    spl2_163 <=> k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 54.15/7.19    introduced(avatar_definition,[new_symbols(naming,[spl2_163])])).
% 54.15/7.19  fof(f57758,plain,(
% 54.15/7.19    spl2_178 <=> sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 54.15/7.19    introduced(avatar_definition,[new_symbols(naming,[spl2_178])])).
% 54.15/7.19  fof(f57770,plain,(
% 54.15/7.19    sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_163 | ~spl2_178)),
% 54.15/7.19    inference(superposition,[],[f57760,f56702])).
% 54.15/7.19  fof(f56702,plain,(
% 54.15/7.19    k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_163),
% 54.15/7.19    inference(avatar_component_clause,[],[f56700])).
% 54.15/7.19  fof(f57760,plain,(
% 54.15/7.19    sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_178),
% 54.15/7.19    inference(avatar_component_clause,[],[f57758])).
% 54.15/7.19  fof(f57761,plain,(
% 54.15/7.19    spl2_178 | ~spl2_2 | ~spl2_3 | ~spl2_89),
% 54.15/7.19    inference(avatar_split_clause,[],[f57756,f40161,f85,f80,f57758])).
% 54.15/7.19  fof(f57756,plain,(
% 54.15/7.19    sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3 | ~spl2_89)),
% 54.15/7.19    inference(forward_demodulation,[],[f57754,f40163])).
% 54.15/7.19  fof(f56703,plain,(
% 54.15/7.19    spl2_163 | ~spl2_3 | ~spl2_32),
% 54.15/7.19    inference(avatar_split_clause,[],[f41186,f39381,f85,f56700])).
% 54.15/7.19  fof(f39381,plain,(
% 54.15/7.19    spl2_32 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 54.15/7.19    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 54.15/7.19  fof(f41186,plain,(
% 54.15/7.19    k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_32)),
% 54.15/7.19    inference(unit_resulting_resolution,[],[f87,f39383,f68])).
% 54.15/7.19  fof(f39383,plain,(
% 54.15/7.19    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_32),
% 54.15/7.19    inference(avatar_component_clause,[],[f39381])).
% 54.15/7.19  fof(f40164,plain,(
% 54.15/7.19    spl2_89 | ~spl2_2 | ~spl2_3 | ~spl2_25),
% 54.15/7.19    inference(avatar_split_clause,[],[f40158,f27456,f85,f80,f40161])).
% 54.15/7.19  fof(f27456,plain,(
% 54.15/7.19    spl2_25 <=> v4_pre_topc(sK1,sK0)),
% 54.15/7.19    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 54.15/7.19  fof(f40158,plain,(
% 54.15/7.19    sK1 = k2_pre_topc(sK0,sK1) | (~spl2_2 | ~spl2_3 | ~spl2_25)),
% 54.15/7.19    inference(unit_resulting_resolution,[],[f82,f87,f27458,f52])).
% 54.15/7.19  fof(f52,plain,(
% 54.15/7.19    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = X1) )),
% 54.15/7.19    inference(cnf_transformation,[],[f27])).
% 54.15/7.19  fof(f27,plain,(
% 54.15/7.19    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 54.15/7.19    inference(flattening,[],[f26])).
% 54.15/7.19  fof(f26,plain,(
% 54.15/7.19    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 54.15/7.19    inference(ennf_transformation,[],[f14])).
% 54.15/7.19  fof(f14,axiom,(
% 54.15/7.19    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 54.15/7.19    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 54.15/7.19  fof(f27458,plain,(
% 54.15/7.19    v4_pre_topc(sK1,sK0) | ~spl2_25),
% 54.15/7.19    inference(avatar_component_clause,[],[f27456])).
% 54.15/7.19  fof(f40156,plain,(
% 54.15/7.19    spl2_88 | ~spl2_85),
% 54.15/7.19    inference(avatar_split_clause,[],[f40119,f40111,f40153])).
% 54.15/7.19  fof(f40119,plain,(
% 54.15/7.19    m1_subset_1(k3_subset_1(sK1,k2_tops_1(sK0,sK1)),k1_zfmisc_1(sK1)) | ~spl2_85),
% 54.15/7.19    inference(unit_resulting_resolution,[],[f40113,f60])).
% 54.15/7.19  fof(f60,plain,(
% 54.15/7.19    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 54.15/7.19    inference(cnf_transformation,[],[f29])).
% 54.15/7.19  fof(f29,plain,(
% 54.15/7.19    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 54.15/7.19    inference(ennf_transformation,[],[f8])).
% 54.15/7.19  fof(f8,axiom,(
% 54.15/7.19    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 54.15/7.19    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 54.15/7.19  fof(f40114,plain,(
% 54.15/7.19    spl2_85 | ~spl2_84),
% 54.15/7.19    inference(avatar_split_clause,[],[f40106,f40099,f40111])).
% 54.15/7.19  fof(f40106,plain,(
% 54.15/7.19    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_84),
% 54.15/7.19    inference(unit_resulting_resolution,[],[f40101,f65])).
% 54.15/7.19  fof(f40102,plain,(
% 54.15/7.19    spl2_84 | ~spl2_26 | ~spl2_83),
% 54.15/7.19    inference(avatar_split_clause,[],[f40097,f40087,f27460,f40099])).
% 54.15/7.19  fof(f40087,plain,(
% 54.15/7.19    spl2_83 <=> ! [X5] : r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X5),sK1)),
% 54.15/7.19    introduced(avatar_definition,[new_symbols(naming,[spl2_83])])).
% 54.15/7.19  fof(f40097,plain,(
% 54.15/7.19    r1_tarski(k2_tops_1(sK0,sK1),sK1) | (~spl2_26 | ~spl2_83)),
% 54.15/7.19    inference(superposition,[],[f40088,f27462])).
% 54.15/7.19  fof(f27462,plain,(
% 54.15/7.19    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_26),
% 54.15/7.19    inference(avatar_component_clause,[],[f27460])).
% 54.15/7.19  fof(f40088,plain,(
% 54.15/7.19    ( ! [X5] : (r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X5),sK1)) ) | ~spl2_83),
% 54.15/7.19    inference(avatar_component_clause,[],[f40087])).
% 54.15/7.19  fof(f40089,plain,(
% 54.15/7.19    spl2_83 | ~spl2_82),
% 54.15/7.19    inference(avatar_split_clause,[],[f40085,f40076,f40087])).
% 54.15/7.19  fof(f40076,plain,(
% 54.15/7.19    spl2_82 <=> ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0)))),
% 54.15/7.19    introduced(avatar_definition,[new_symbols(naming,[spl2_82])])).
% 54.15/7.19  fof(f40085,plain,(
% 54.15/7.19    ( ! [X5] : (r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X5),sK1)) ) | ~spl2_82),
% 54.15/7.19    inference(superposition,[],[f70,f40077])).
% 54.15/7.19  fof(f40077,plain,(
% 54.15/7.19    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0)))) ) | ~spl2_82),
% 54.15/7.19    inference(avatar_component_clause,[],[f40076])).
% 54.15/7.19  fof(f70,plain,(
% 54.15/7.19    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)) )),
% 54.15/7.19    inference(definition_unfolding,[],[f55,f69])).
% 54.15/7.19  fof(f69,plain,(
% 54.15/7.19    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 54.15/7.19    inference(definition_unfolding,[],[f58,f57])).
% 54.15/7.19  fof(f57,plain,(
% 54.15/7.19    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 54.15/7.19    inference(cnf_transformation,[],[f12])).
% 54.15/7.19  fof(f12,axiom,(
% 54.15/7.19    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 54.15/7.19    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 54.15/7.19  fof(f58,plain,(
% 54.15/7.19    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 54.15/7.19    inference(cnf_transformation,[],[f3])).
% 54.15/7.19  fof(f3,axiom,(
% 54.15/7.19    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 54.15/7.19    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 54.15/7.19  fof(f55,plain,(
% 54.15/7.19    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 54.15/7.19    inference(cnf_transformation,[],[f5])).
% 54.15/7.19  fof(f5,axiom,(
% 54.15/7.19    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 54.15/7.19    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 54.15/7.19  fof(f40078,plain,(
% 54.15/7.19    spl2_82 | ~spl2_3),
% 54.15/7.19    inference(avatar_split_clause,[],[f40045,f85,f40076])).
% 54.15/7.19  fof(f40045,plain,(
% 54.15/7.19    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0)))) ) | ~spl2_3),
% 54.15/7.19    inference(unit_resulting_resolution,[],[f87,f72])).
% 54.15/7.19  fof(f72,plain,(
% 54.15/7.19    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) )),
% 54.15/7.19    inference(definition_unfolding,[],[f67,f69])).
% 54.15/7.19  fof(f67,plain,(
% 54.15/7.19    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 54.15/7.19    inference(cnf_transformation,[],[f35])).
% 54.15/7.19  fof(f35,plain,(
% 54.15/7.19    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 54.15/7.19    inference(ennf_transformation,[],[f10])).
% 54.15/7.19  fof(f10,axiom,(
% 54.15/7.19    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 54.15/7.19    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 54.15/7.19  fof(f39384,plain,(
% 54.15/7.19    spl2_32 | ~spl2_2 | ~spl2_3),
% 54.15/7.19    inference(avatar_split_clause,[],[f39373,f85,f80,f39381])).
% 54.15/7.19  fof(f39373,plain,(
% 54.15/7.19    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_2 | ~spl2_3)),
% 54.15/7.19    inference(unit_resulting_resolution,[],[f82,f87,f63])).
% 54.15/7.19  fof(f63,plain,(
% 54.15/7.19    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 54.15/7.19    inference(cnf_transformation,[],[f34])).
% 54.15/7.19  fof(f34,plain,(
% 54.15/7.19    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 54.15/7.19    inference(flattening,[],[f33])).
% 54.15/7.19  fof(f33,plain,(
% 54.15/7.19    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 54.15/7.19    inference(ennf_transformation,[],[f15])).
% 54.15/7.19  fof(f15,axiom,(
% 54.15/7.19    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 54.15/7.19    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 54.15/7.19  fof(f39358,plain,(
% 54.15/7.19    spl2_28 | ~spl2_1 | ~spl2_2 | ~spl2_3),
% 54.15/7.19    inference(avatar_split_clause,[],[f39348,f85,f80,f75,f39355])).
% 54.15/7.19  fof(f39355,plain,(
% 54.15/7.19    spl2_28 <=> v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)),
% 54.15/7.19    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 54.15/7.19  fof(f75,plain,(
% 54.15/7.19    spl2_1 <=> v2_pre_topc(sK0)),
% 54.15/7.19    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 54.15/7.19  fof(f39348,plain,(
% 54.15/7.19    v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) | (~spl2_1 | ~spl2_2 | ~spl2_3)),
% 54.15/7.19    inference(unit_resulting_resolution,[],[f77,f82,f87,f62])).
% 54.15/7.19  fof(f62,plain,(
% 54.15/7.19    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 54.15/7.19    inference(cnf_transformation,[],[f32])).
% 54.15/7.19  fof(f32,plain,(
% 54.15/7.19    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 54.15/7.19    inference(flattening,[],[f31])).
% 54.15/7.19  fof(f31,plain,(
% 54.15/7.19    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 54.15/7.19    inference(ennf_transformation,[],[f16])).
% 54.15/7.19  fof(f16,axiom,(
% 54.15/7.19    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 54.15/7.19    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).
% 54.15/7.19  fof(f77,plain,(
% 54.15/7.19    v2_pre_topc(sK0) | ~spl2_1),
% 54.15/7.19    inference(avatar_component_clause,[],[f75])).
% 54.15/7.19  fof(f39347,plain,(
% 54.15/7.19    ~spl2_25 | ~spl2_26),
% 54.15/7.19    inference(avatar_split_clause,[],[f48,f27460,f27456])).
% 54.15/7.19  fof(f48,plain,(
% 54.15/7.19    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 54.15/7.19    inference(cnf_transformation,[],[f42])).
% 54.15/7.19  fof(f42,plain,(
% 54.15/7.19    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 54.15/7.19    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f39,f41,f40])).
% 54.15/7.19  fof(f40,plain,(
% 54.15/7.19    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 54.15/7.19    introduced(choice_axiom,[])).
% 54.15/7.19  fof(f41,plain,(
% 54.15/7.19    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 54.15/7.19    introduced(choice_axiom,[])).
% 54.15/7.19  fof(f39,plain,(
% 54.15/7.19    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 54.15/7.19    inference(flattening,[],[f38])).
% 54.15/7.19  fof(f38,plain,(
% 54.15/7.19    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 54.15/7.19    inference(nnf_transformation,[],[f23])).
% 54.15/7.19  fof(f23,plain,(
% 54.15/7.19    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 54.15/7.19    inference(flattening,[],[f22])).
% 54.15/7.19  fof(f22,plain,(
% 54.15/7.19    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 54.15/7.19    inference(ennf_transformation,[],[f20])).
% 54.15/7.19  fof(f20,negated_conjecture,(
% 54.15/7.19    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 54.15/7.19    inference(negated_conjecture,[],[f19])).
% 54.15/7.19  fof(f19,conjecture,(
% 54.15/7.19    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 54.15/7.19    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).
% 54.15/7.19  fof(f27463,plain,(
% 54.15/7.19    spl2_25 | spl2_26),
% 54.15/7.19    inference(avatar_split_clause,[],[f47,f27460,f27456])).
% 54.15/7.19  fof(f47,plain,(
% 54.15/7.19    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 54.15/7.19    inference(cnf_transformation,[],[f42])).
% 54.15/7.19  fof(f88,plain,(
% 54.15/7.19    spl2_3),
% 54.15/7.19    inference(avatar_split_clause,[],[f46,f85])).
% 54.15/7.19  fof(f46,plain,(
% 54.15/7.19    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 54.15/7.19    inference(cnf_transformation,[],[f42])).
% 54.15/7.19  fof(f83,plain,(
% 54.15/7.19    spl2_2),
% 54.15/7.19    inference(avatar_split_clause,[],[f45,f80])).
% 54.15/7.19  fof(f45,plain,(
% 54.15/7.19    l1_pre_topc(sK0)),
% 54.15/7.19    inference(cnf_transformation,[],[f42])).
% 54.15/7.19  fof(f78,plain,(
% 54.15/7.19    spl2_1),
% 54.15/7.19    inference(avatar_split_clause,[],[f44,f75])).
% 54.15/7.19  fof(f44,plain,(
% 54.15/7.19    v2_pre_topc(sK0)),
% 54.15/7.19    inference(cnf_transformation,[],[f42])).
% 54.15/7.19  % SZS output end Proof for theBenchmark
% 54.15/7.19  % (8900)------------------------------
% 54.15/7.19  % (8900)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 54.15/7.19  % (8900)Termination reason: Refutation
% 54.15/7.19  
% 54.15/7.19  % (8900)Memory used [KB]: 157481
% 54.15/7.19  % (8900)Time elapsed: 6.738 s
% 54.15/7.19  % (8900)------------------------------
% 54.15/7.19  % (8900)------------------------------
% 54.15/7.21  % (8882)Success in time 6.852 s
%------------------------------------------------------------------------------
