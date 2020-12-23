%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:53 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 612 expanded)
%              Number of leaves         :   26 ( 213 expanded)
%              Depth                    :   12
%              Number of atoms          :  316 (1254 expanded)
%              Number of equality atoms :   33 ( 356 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1059,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f60,f65,f70,f75,f213,f237,f274,f613,f867,f897,f1052])).

fof(f1052,plain,
    ( ~ spl3_5
    | spl3_23
    | ~ spl3_34 ),
    inference(avatar_contradiction_clause,[],[f997])).

fof(f997,plain,
    ( $false
    | ~ spl3_5
    | spl3_23
    | ~ spl3_34 ),
    inference(unit_resulting_resolution,[],[f612,f958])).

fof(f958,plain,
    ( ! [X0] : v2_tex_2(k9_subset_1(sK1,X0,sK1),sK0)
    | ~ spl3_5
    | ~ spl3_34 ),
    inference(forward_demodulation,[],[f956,f567])).

fof(f567,plain,
    ( ! [X1] : k1_setfam_1(k1_enumset1(sK1,sK1,X1)) = k9_subset_1(sK1,X1,sK1)
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f214,f264])).

fof(f264,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK1) = k9_subset_1(sK1,X0,sK1)
    | ~ spl3_5 ),
    inference(backward_demodulation,[],[f118,f120])).

fof(f120,plain,(
    ! [X0,X1] : k1_setfam_1(k1_enumset1(X1,X1,X0)) = k9_subset_1(X0,X1,X0) ),
    inference(unit_resulting_resolution,[],[f76,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k1_setfam_1(k1_enumset1(X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f42,f43])).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f35,f36])).

fof(f36,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f76,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f32,f31])).

fof(f31,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f32,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f118,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK1) = k1_setfam_1(k1_enumset1(X0,X0,sK1))
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f69,f46])).

fof(f69,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl3_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f214,plain,
    ( ! [X1] : k9_subset_1(u1_struct_0(sK0),X1,sK1) = k1_setfam_1(k1_enumset1(sK1,sK1,X1))
    | ~ spl3_5 ),
    inference(superposition,[],[f118,f44])).

fof(f44,plain,(
    ! [X0,X1] : k1_setfam_1(k1_enumset1(X0,X0,X1)) = k1_setfam_1(k1_enumset1(X1,X1,X0)) ),
    inference(definition_unfolding,[],[f34,f43,f43])).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

% (28551)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
fof(f956,plain,
    ( ! [X0] : v2_tex_2(k1_setfam_1(k1_enumset1(sK1,sK1,X0)),sK0)
    | ~ spl3_5
    | ~ spl3_34 ),
    inference(superposition,[],[f924,f45])).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f37,f43])).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f924,plain,
    ( ! [X0] : v2_tex_2(k4_xboole_0(sK1,X0),sK0)
    | ~ spl3_5
    | ~ spl3_34 ),
    inference(unit_resulting_resolution,[],[f244,f180,f896])).

fof(f896,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f895])).

fof(f895,plain,
    ( spl3_34
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f180,plain,
    ( ! [X0] : m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_5 ),
    inference(backward_demodulation,[],[f99,f105])).

fof(f105,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f69,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f99,plain,
    ( ! [X0] : m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f69,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).

fof(f244,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(unit_resulting_resolution,[],[f238,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f238,plain,(
    ! [X0,X1] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f100,f106])).

fof(f106,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1) ),
    inference(unit_resulting_resolution,[],[f76,f41])).

fof(f100,plain,(
    ! [X0,X1] : m1_subset_1(k7_subset_1(X0,X0,X1),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f76,f40])).

fof(f612,plain,
    ( ~ v2_tex_2(k9_subset_1(sK1,sK2,sK1),sK0)
    | spl3_23 ),
    inference(avatar_component_clause,[],[f610])).

fof(f610,plain,
    ( spl3_23
  <=> v2_tex_2(k9_subset_1(sK1,sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f897,plain,
    ( ~ spl3_5
    | spl3_34
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f879,f72,f53,f895,f67])).

fof(f53,plain,
    ( spl3_2
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f72,plain,
    ( spl3_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f879,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(X0,sK0) )
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(resolution,[],[f55,f132])).

fof(f132,plain,
    ( ! [X0,X1] :
        ( ~ v2_tex_2(X0,sK0)
        | ~ r1_tarski(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(X1,sK0) )
    | ~ spl3_6 ),
    inference(resolution,[],[f33,f74])).

fof(f74,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f72])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_tex_2(X1,X0)
      | ~ r1_tarski(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X2,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_tex_2(X1,X0)
                  & r1_tarski(X2,X1) )
               => v2_tex_2(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_tex_2)).

fof(f55,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f867,plain,
    ( ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_17
    | spl3_23 ),
    inference(avatar_contradiction_clause,[],[f855])).

fof(f855,plain,
    ( $false
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_17
    | spl3_23 ),
    inference(unit_resulting_resolution,[],[f74,f612,f424,f79,f424,f701,f33])).

fof(f701,plain,
    ( ! [X0] : v2_tex_2(k9_subset_1(X0,sK2,X0),sK0)
    | ~ spl3_4
    | ~ spl3_17 ),
    inference(superposition,[],[f663,f520])).

fof(f520,plain,
    ( ! [X0] : k9_subset_1(sK2,X0,sK2) = k9_subset_1(X0,sK2,X0)
    | ~ spl3_4 ),
    inference(superposition,[],[f515,f120])).

fof(f515,plain,
    ( ! [X1] : k1_setfam_1(k1_enumset1(sK2,sK2,X1)) = k9_subset_1(sK2,X1,sK2)
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f205,f263])).

fof(f263,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK2) = k9_subset_1(sK2,X0,sK2)
    | ~ spl3_4 ),
    inference(backward_demodulation,[],[f117,f120])).

fof(f117,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK2) = k1_setfam_1(k1_enumset1(X0,X0,sK2))
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f64,f46])).

fof(f64,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl3_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f205,plain,
    ( ! [X1] : k1_setfam_1(k1_enumset1(sK2,sK2,X1)) = k9_subset_1(u1_struct_0(sK0),X1,sK2)
    | ~ spl3_4 ),
    inference(superposition,[],[f117,f44])).

fof(f663,plain,
    ( ! [X0] : v2_tex_2(k9_subset_1(sK2,X0,sK2),sK0)
    | ~ spl3_4
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f661,f515])).

fof(f661,plain,
    ( ! [X0] : v2_tex_2(k1_setfam_1(k1_enumset1(sK2,sK2,X0)),sK0)
    | ~ spl3_4
    | ~ spl3_17 ),
    inference(superposition,[],[f644,f45])).

fof(f644,plain,
    ( ! [X0] : v2_tex_2(k4_xboole_0(sK2,X0),sK0)
    | ~ spl3_4
    | ~ spl3_17 ),
    inference(unit_resulting_resolution,[],[f164,f244,f236])).

fof(f236,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK2)
        | v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f235])).

fof(f235,plain,
    ( spl3_17
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK2)
        | v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f164,plain,
    ( ! [X0] : m1_subset_1(k4_xboole_0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_4 ),
    inference(backward_demodulation,[],[f98,f104])).

fof(f104,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),sK2,X0) = k4_xboole_0(sK2,X0)
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f64,f41])).

fof(f98,plain,
    ( ! [X0] : m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK2,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f64,f40])).

fof(f79,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(unit_resulting_resolution,[],[f76,f38])).

fof(f424,plain,
    ( ! [X1] : m1_subset_1(k9_subset_1(sK1,X1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f422,f120])).

fof(f422,plain,
    ( ! [X1] : m1_subset_1(k1_setfam_1(k1_enumset1(X1,X1,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_5 ),
    inference(superposition,[],[f199,f44])).

fof(f199,plain,
    ( ! [X0] : m1_subset_1(k1_setfam_1(k1_enumset1(sK1,sK1,X0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_5 ),
    inference(superposition,[],[f180,f45])).

fof(f613,plain,
    ( ~ spl3_23
    | ~ spl3_4
    | spl3_18 ),
    inference(avatar_split_clause,[],[f590,f271,f62,f610])).

fof(f271,plain,
    ( spl3_18
  <=> v2_tex_2(k9_subset_1(sK2,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f590,plain,
    ( ~ v2_tex_2(k9_subset_1(sK1,sK2,sK1),sK0)
    | ~ spl3_4
    | spl3_18 ),
    inference(backward_demodulation,[],[f273,f520])).

fof(f273,plain,
    ( ~ v2_tex_2(k9_subset_1(sK2,sK1,sK2),sK0)
    | spl3_18 ),
    inference(avatar_component_clause,[],[f271])).

fof(f274,plain,
    ( ~ spl3_18
    | spl3_16 ),
    inference(avatar_split_clause,[],[f265,f210,f271])).

fof(f210,plain,
    ( spl3_16
  <=> v2_tex_2(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f265,plain,
    ( ~ v2_tex_2(k9_subset_1(sK2,sK1,sK2),sK0)
    | spl3_16 ),
    inference(backward_demodulation,[],[f212,f120])).

fof(f212,plain,
    ( ~ v2_tex_2(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)),sK0)
    | spl3_16 ),
    inference(avatar_component_clause,[],[f210])).

fof(f237,plain,
    ( ~ spl3_4
    | spl3_17
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f233,f72,f57,f235,f62])).

fof(f57,plain,
    ( spl3_3
  <=> v2_tex_2(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f233,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(X0,sK0) )
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(resolution,[],[f132,f59])).

fof(f59,plain,
    ( v2_tex_2(sK2,sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f57])).

fof(f213,plain,
    ( ~ spl3_16
    | spl3_1
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f204,f62,f48,f210])).

fof(f48,plain,
    ( spl3_1
  <=> v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f204,plain,
    ( ~ v2_tex_2(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)),sK0)
    | spl3_1
    | ~ spl3_4 ),
    inference(backward_demodulation,[],[f50,f117])).

fof(f50,plain,
    ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f75,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f26,f72])).

fof(f26,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & ( v2_tex_2(sK2,sK0)
      | v2_tex_2(sK1,sK0) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f23,f22,f21])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                & ( v2_tex_2(X2,X0)
                  | v2_tex_2(X1,X0) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
              & ( v2_tex_2(X2,sK0)
                | v2_tex_2(X1,sK0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
            & ( v2_tex_2(X2,sK0)
              | v2_tex_2(X1,sK0) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
          & ( v2_tex_2(X2,sK0)
            | v2_tex_2(sK1,sK0) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X2] :
        ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
        & ( v2_tex_2(X2,sK0)
          | v2_tex_2(sK1,sK0) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
      & ( v2_tex_2(sK2,sK0)
        | v2_tex_2(sK1,sK0) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v2_tex_2(X2,X0)
                    | v2_tex_2(X1,X0) )
                 => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_tex_2(X2,X0)
                  | v2_tex_2(X1,X0) )
               => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tex_2)).

fof(f70,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f27,f67])).

fof(f27,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f65,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f28,f62])).

fof(f28,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f60,plain,
    ( spl3_2
    | spl3_3 ),
    inference(avatar_split_clause,[],[f29,f57,f53])).

fof(f29,plain,
    ( v2_tex_2(sK2,sK0)
    | v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f51,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f30,f48])).

fof(f30,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:45:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.45  % (28534)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.46  % (28542)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.46  % (28540)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.47  % (28536)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (28537)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (28547)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.49  % (28535)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.49  % (28539)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.49  % (28543)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.49  % (28538)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.49  % (28549)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.50  % (28540)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f1059,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f51,f60,f65,f70,f75,f213,f237,f274,f613,f867,f897,f1052])).
% 0.22/0.50  fof(f1052,plain,(
% 0.22/0.50    ~spl3_5 | spl3_23 | ~spl3_34),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f997])).
% 0.22/0.50  fof(f997,plain,(
% 0.22/0.50    $false | (~spl3_5 | spl3_23 | ~spl3_34)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f612,f958])).
% 0.22/0.50  fof(f958,plain,(
% 0.22/0.50    ( ! [X0] : (v2_tex_2(k9_subset_1(sK1,X0,sK1),sK0)) ) | (~spl3_5 | ~spl3_34)),
% 0.22/0.50    inference(forward_demodulation,[],[f956,f567])).
% 0.22/0.50  fof(f567,plain,(
% 0.22/0.50    ( ! [X1] : (k1_setfam_1(k1_enumset1(sK1,sK1,X1)) = k9_subset_1(sK1,X1,sK1)) ) | ~spl3_5),
% 0.22/0.50    inference(forward_demodulation,[],[f214,f264])).
% 0.22/0.50  fof(f264,plain,(
% 0.22/0.50    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,sK1) = k9_subset_1(sK1,X0,sK1)) ) | ~spl3_5),
% 0.22/0.50    inference(backward_demodulation,[],[f118,f120])).
% 0.22/0.50  fof(f120,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(X1,X1,X0)) = k9_subset_1(X0,X1,X0)) )),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f76,f46])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k1_setfam_1(k1_enumset1(X1,X1,X2))) )),
% 0.22/0.50    inference(definition_unfolding,[],[f42,f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 0.22/0.50    inference(definition_unfolding,[],[f35,f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.22/0.50  fof(f76,plain,(
% 0.22/0.50    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.22/0.50    inference(forward_demodulation,[],[f32,f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0] : k2_subset_1(X0) = X0),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.22/0.50  fof(f118,plain,(
% 0.22/0.50    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,sK1) = k1_setfam_1(k1_enumset1(X0,X0,sK1))) ) | ~spl3_5),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f69,f46])).
% 0.22/0.50  fof(f69,plain,(
% 0.22/0.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f67])).
% 0.22/0.50  fof(f67,plain,(
% 0.22/0.50    spl3_5 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.50  fof(f214,plain,(
% 0.22/0.50    ( ! [X1] : (k9_subset_1(u1_struct_0(sK0),X1,sK1) = k1_setfam_1(k1_enumset1(sK1,sK1,X1))) ) | ~spl3_5),
% 0.22/0.50    inference(superposition,[],[f118,f44])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,X1)) = k1_setfam_1(k1_enumset1(X1,X1,X0))) )),
% 0.22/0.50    inference(definition_unfolding,[],[f34,f43,f43])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.50  % (28551)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.50  fof(f956,plain,(
% 0.22/0.50    ( ! [X0] : (v2_tex_2(k1_setfam_1(k1_enumset1(sK1,sK1,X0)),sK0)) ) | (~spl3_5 | ~spl3_34)),
% 0.22/0.50    inference(superposition,[],[f924,f45])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 0.22/0.50    inference(definition_unfolding,[],[f37,f43])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.50  fof(f924,plain,(
% 0.22/0.50    ( ! [X0] : (v2_tex_2(k4_xboole_0(sK1,X0),sK0)) ) | (~spl3_5 | ~spl3_34)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f244,f180,f896])).
% 0.22/0.50  fof(f896,plain,(
% 0.22/0.50    ( ! [X0] : (~r1_tarski(X0,sK1) | v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_34),
% 0.22/0.50    inference(avatar_component_clause,[],[f895])).
% 0.22/0.50  fof(f895,plain,(
% 0.22/0.50    spl3_34 <=> ! [X0] : (~r1_tarski(X0,sK1) | v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.22/0.50  fof(f180,plain,(
% 0.22/0.50    ( ! [X0] : (m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_5),
% 0.22/0.50    inference(backward_demodulation,[],[f99,f105])).
% 0.22/0.50  fof(f105,plain,(
% 0.22/0.50    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)) ) | ~spl3_5),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f69,f41])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.22/0.50  fof(f99,plain,(
% 0.22/0.50    ( ! [X0] : (m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_5),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f69,f40])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).
% 0.22/0.50  fof(f244,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f238,f38])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.50    inference(nnf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.50  fof(f238,plain,(
% 0.22/0.50    ( ! [X0,X1] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))) )),
% 0.22/0.50    inference(backward_demodulation,[],[f100,f106])).
% 0.22/0.50  fof(f106,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1)) )),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f76,f41])).
% 0.22/0.50  fof(f100,plain,(
% 0.22/0.50    ( ! [X0,X1] : (m1_subset_1(k7_subset_1(X0,X0,X1),k1_zfmisc_1(X0))) )),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f76,f40])).
% 0.22/0.50  fof(f612,plain,(
% 0.22/0.50    ~v2_tex_2(k9_subset_1(sK1,sK2,sK1),sK0) | spl3_23),
% 0.22/0.50    inference(avatar_component_clause,[],[f610])).
% 0.22/0.50  fof(f610,plain,(
% 0.22/0.50    spl3_23 <=> v2_tex_2(k9_subset_1(sK1,sK2,sK1),sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.22/0.50  fof(f897,plain,(
% 0.22/0.50    ~spl3_5 | spl3_34 | ~spl3_2 | ~spl3_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f879,f72,f53,f895,f67])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    spl3_2 <=> v2_tex_2(sK1,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.50  fof(f72,plain,(
% 0.22/0.50    spl3_6 <=> l1_pre_topc(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.50  fof(f879,plain,(
% 0.22/0.50    ( ! [X0] : (~r1_tarski(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X0,sK0)) ) | (~spl3_2 | ~spl3_6)),
% 0.22/0.50    inference(resolution,[],[f55,f132])).
% 0.22/0.50  fof(f132,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v2_tex_2(X0,sK0) | ~r1_tarski(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X1,sK0)) ) | ~spl3_6),
% 0.22/0.50    inference(resolution,[],[f33,f74])).
% 0.22/0.50  fof(f74,plain,(
% 0.22/0.50    l1_pre_topc(sK0) | ~spl3_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f72])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(X2,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (v2_tex_2(X2,X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(flattening,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) | (~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & r1_tarski(X2,X1)) => v2_tex_2(X2,X0)))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_tex_2)).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    v2_tex_2(sK1,sK0) | ~spl3_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f53])).
% 0.22/0.50  fof(f867,plain,(
% 0.22/0.50    ~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_17 | spl3_23),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f855])).
% 0.22/0.50  fof(f855,plain,(
% 0.22/0.50    $false | (~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_17 | spl3_23)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f74,f612,f424,f79,f424,f701,f33])).
% 0.22/0.50  fof(f701,plain,(
% 0.22/0.50    ( ! [X0] : (v2_tex_2(k9_subset_1(X0,sK2,X0),sK0)) ) | (~spl3_4 | ~spl3_17)),
% 0.22/0.50    inference(superposition,[],[f663,f520])).
% 0.22/0.50  fof(f520,plain,(
% 0.22/0.50    ( ! [X0] : (k9_subset_1(sK2,X0,sK2) = k9_subset_1(X0,sK2,X0)) ) | ~spl3_4),
% 0.22/0.50    inference(superposition,[],[f515,f120])).
% 0.22/0.50  fof(f515,plain,(
% 0.22/0.50    ( ! [X1] : (k1_setfam_1(k1_enumset1(sK2,sK2,X1)) = k9_subset_1(sK2,X1,sK2)) ) | ~spl3_4),
% 0.22/0.50    inference(forward_demodulation,[],[f205,f263])).
% 0.22/0.50  fof(f263,plain,(
% 0.22/0.50    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,sK2) = k9_subset_1(sK2,X0,sK2)) ) | ~spl3_4),
% 0.22/0.50    inference(backward_demodulation,[],[f117,f120])).
% 0.22/0.50  fof(f117,plain,(
% 0.22/0.50    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,sK2) = k1_setfam_1(k1_enumset1(X0,X0,sK2))) ) | ~spl3_4),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f64,f46])).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f62])).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    spl3_4 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.50  fof(f205,plain,(
% 0.22/0.50    ( ! [X1] : (k1_setfam_1(k1_enumset1(sK2,sK2,X1)) = k9_subset_1(u1_struct_0(sK0),X1,sK2)) ) | ~spl3_4),
% 0.22/0.50    inference(superposition,[],[f117,f44])).
% 0.22/0.50  fof(f663,plain,(
% 0.22/0.50    ( ! [X0] : (v2_tex_2(k9_subset_1(sK2,X0,sK2),sK0)) ) | (~spl3_4 | ~spl3_17)),
% 0.22/0.50    inference(forward_demodulation,[],[f661,f515])).
% 0.22/0.50  fof(f661,plain,(
% 0.22/0.50    ( ! [X0] : (v2_tex_2(k1_setfam_1(k1_enumset1(sK2,sK2,X0)),sK0)) ) | (~spl3_4 | ~spl3_17)),
% 0.22/0.50    inference(superposition,[],[f644,f45])).
% 0.22/0.50  fof(f644,plain,(
% 0.22/0.50    ( ! [X0] : (v2_tex_2(k4_xboole_0(sK2,X0),sK0)) ) | (~spl3_4 | ~spl3_17)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f164,f244,f236])).
% 0.22/0.50  fof(f236,plain,(
% 0.22/0.50    ( ! [X0] : (~r1_tarski(X0,sK2) | v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_17),
% 0.22/0.50    inference(avatar_component_clause,[],[f235])).
% 0.22/0.50  fof(f235,plain,(
% 0.22/0.50    spl3_17 <=> ! [X0] : (~r1_tarski(X0,sK2) | v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.22/0.50  fof(f164,plain,(
% 0.22/0.50    ( ! [X0] : (m1_subset_1(k4_xboole_0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_4),
% 0.22/0.50    inference(backward_demodulation,[],[f98,f104])).
% 0.22/0.50  fof(f104,plain,(
% 0.22/0.50    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK2,X0) = k4_xboole_0(sK2,X0)) ) | ~spl3_4),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f64,f41])).
% 0.22/0.50  fof(f98,plain,(
% 0.22/0.50    ( ! [X0] : (m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK2,X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_4),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f64,f40])).
% 0.22/0.50  fof(f79,plain,(
% 0.22/0.50    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f76,f38])).
% 0.22/0.50  fof(f424,plain,(
% 0.22/0.50    ( ! [X1] : (m1_subset_1(k9_subset_1(sK1,X1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_5),
% 0.22/0.50    inference(forward_demodulation,[],[f422,f120])).
% 0.22/0.50  fof(f422,plain,(
% 0.22/0.50    ( ! [X1] : (m1_subset_1(k1_setfam_1(k1_enumset1(X1,X1,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_5),
% 0.22/0.50    inference(superposition,[],[f199,f44])).
% 0.22/0.50  fof(f199,plain,(
% 0.22/0.50    ( ! [X0] : (m1_subset_1(k1_setfam_1(k1_enumset1(sK1,sK1,X0)),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_5),
% 0.22/0.50    inference(superposition,[],[f180,f45])).
% 0.22/0.50  fof(f613,plain,(
% 0.22/0.50    ~spl3_23 | ~spl3_4 | spl3_18),
% 0.22/0.50    inference(avatar_split_clause,[],[f590,f271,f62,f610])).
% 0.22/0.50  fof(f271,plain,(
% 0.22/0.50    spl3_18 <=> v2_tex_2(k9_subset_1(sK2,sK1,sK2),sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.22/0.50  fof(f590,plain,(
% 0.22/0.50    ~v2_tex_2(k9_subset_1(sK1,sK2,sK1),sK0) | (~spl3_4 | spl3_18)),
% 0.22/0.50    inference(backward_demodulation,[],[f273,f520])).
% 0.22/0.50  fof(f273,plain,(
% 0.22/0.50    ~v2_tex_2(k9_subset_1(sK2,sK1,sK2),sK0) | spl3_18),
% 0.22/0.50    inference(avatar_component_clause,[],[f271])).
% 0.22/0.50  fof(f274,plain,(
% 0.22/0.50    ~spl3_18 | spl3_16),
% 0.22/0.50    inference(avatar_split_clause,[],[f265,f210,f271])).
% 0.22/0.50  fof(f210,plain,(
% 0.22/0.50    spl3_16 <=> v2_tex_2(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)),sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.22/0.50  fof(f265,plain,(
% 0.22/0.50    ~v2_tex_2(k9_subset_1(sK2,sK1,sK2),sK0) | spl3_16),
% 0.22/0.50    inference(backward_demodulation,[],[f212,f120])).
% 0.22/0.50  fof(f212,plain,(
% 0.22/0.50    ~v2_tex_2(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)),sK0) | spl3_16),
% 0.22/0.50    inference(avatar_component_clause,[],[f210])).
% 0.22/0.50  fof(f237,plain,(
% 0.22/0.50    ~spl3_4 | spl3_17 | ~spl3_3 | ~spl3_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f233,f72,f57,f235,f62])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    spl3_3 <=> v2_tex_2(sK2,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.50  fof(f233,plain,(
% 0.22/0.50    ( ! [X0] : (~r1_tarski(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X0,sK0)) ) | (~spl3_3 | ~spl3_6)),
% 0.22/0.50    inference(resolution,[],[f132,f59])).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    v2_tex_2(sK2,sK0) | ~spl3_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f57])).
% 0.22/0.50  fof(f213,plain,(
% 0.22/0.50    ~spl3_16 | spl3_1 | ~spl3_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f204,f62,f48,f210])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    spl3_1 <=> v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.50  fof(f204,plain,(
% 0.22/0.50    ~v2_tex_2(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)),sK0) | (spl3_1 | ~spl3_4)),
% 0.22/0.50    inference(backward_demodulation,[],[f50,f117])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    ~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) | spl3_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f48])).
% 0.22/0.50  fof(f75,plain,(
% 0.22/0.50    spl3_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f26,f72])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    l1_pre_topc(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ((~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & (v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f23,f22,f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & (v2_tex_2(X2,sK0) | v2_tex_2(X1,sK0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & (v2_tex_2(X2,sK0) | v2_tex_2(X1,sK0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & (v2_tex_2(X2,sK0) | v2_tex_2(sK1,sK0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & (v2_tex_2(X2,sK0) | v2_tex_2(sK1,sK0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & (v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.50    inference(flattening,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : ((~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,negated_conjecture,(
% 0.22/0.50    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.22/0.50    inference(negated_conjecture,[],[f12])).
% 0.22/0.50  fof(f12,conjecture,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tex_2)).
% 0.22/0.50  fof(f70,plain,(
% 0.22/0.50    spl3_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f27,f67])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.50    inference(cnf_transformation,[],[f24])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    spl3_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f28,f62])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.50    inference(cnf_transformation,[],[f24])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    spl3_2 | spl3_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f29,f57,f53])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f24])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    ~spl3_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f30,f48])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f24])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (28540)------------------------------
% 0.22/0.50  % (28540)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (28540)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (28540)Memory used [KB]: 6908
% 0.22/0.50  % (28540)Time elapsed: 0.042 s
% 0.22/0.50  % (28540)------------------------------
% 0.22/0.50  % (28540)------------------------------
% 0.22/0.50  % (28528)Success in time 0.137 s
%------------------------------------------------------------------------------
