%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 545 expanded)
%              Number of leaves         :   19 ( 187 expanded)
%              Depth                    :   11
%              Number of atoms          :  347 (1505 expanded)
%              Number of equality atoms :   18 ( 183 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f408,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f42,f47,f56,f61,f139,f166,f173,f390,f393,f395,f397,f399,f401,f403,f405,f407])).

fof(f407,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | spl3_7 ),
    inference(avatar_contradiction_clause,[],[f406])).

fof(f406,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | spl3_7 ),
    inference(subsumption_resolution,[],[f51,f362])).

fof(f362,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | spl3_7 ),
    inference(unit_resulting_resolution,[],[f36,f41,f31,f138,f121,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X1)
      | ~ v2_tex_2(X1,X0)
      | v2_tex_2(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f121,plain,
    ( ! [X0] : m1_subset_1(k1_setfam_1(k2_tarski(X0,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f84,f116])).

fof(f116,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),sK2,X0) = k1_setfam_1(k2_tarski(X0,sK2))
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f71,f93])).

fof(f93,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f46,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f29,f27])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f46,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f71,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK2) = k9_subset_1(u1_struct_0(sK0),sK2,X0)
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f46,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f84,plain,
    ( ! [X0] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK2,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(superposition,[],[f63,f71])).

fof(f63,plain,
    ( ! [X0] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f46,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f138,plain,
    ( ~ v2_tex_2(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl3_7
  <=> v2_tex_2(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f26,f27])).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f41,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl3_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f36,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl3_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f51,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl3_4
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f405,plain,
    ( ~ spl3_1
    | ~ spl3_3
    | ~ spl3_5
    | spl3_7
    | ~ spl3_9 ),
    inference(avatar_contradiction_clause,[],[f404])).

fof(f404,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_5
    | spl3_7
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f358,f121])).

fof(f358,plain,
    ( ~ m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_5
    | spl3_7
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f36,f138,f172,f55,f46,f25])).

fof(f55,plain,
    ( v2_tex_2(sK2,sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl3_5
  <=> v2_tex_2(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f172,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl3_9
  <=> r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f403,plain,
    ( ~ spl3_1
    | ~ spl3_3
    | ~ spl3_5
    | spl3_7
    | ~ spl3_9 ),
    inference(avatar_contradiction_clause,[],[f402])).

fof(f402,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_5
    | spl3_7
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f360,f138])).

fof(f360,plain,
    ( v2_tex_2(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f36,f55,f46,f172,f121,f25])).

fof(f401,plain,
    ( ~ spl3_1
    | ~ spl3_3
    | ~ spl3_5
    | spl3_7
    | ~ spl3_9 ),
    inference(avatar_contradiction_clause,[],[f400])).

fof(f400,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_5
    | spl3_7
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f361,f172])).

fof(f361,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2)
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_5
    | spl3_7 ),
    inference(unit_resulting_resolution,[],[f36,f55,f46,f138,f121,f25])).

fof(f399,plain,
    ( ~ spl3_1
    | ~ spl3_3
    | ~ spl3_5
    | spl3_7
    | ~ spl3_9 ),
    inference(avatar_contradiction_clause,[],[f398])).

fof(f398,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_5
    | spl3_7
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f363,f46])).

fof(f363,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_5
    | spl3_7
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f36,f55,f172,f138,f121,f25])).

fof(f397,plain,
    ( ~ spl3_1
    | ~ spl3_3
    | ~ spl3_5
    | spl3_7
    | ~ spl3_9 ),
    inference(avatar_contradiction_clause,[],[f396])).

fof(f396,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_5
    | spl3_7
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f364,f55])).

fof(f364,plain,
    ( ~ v2_tex_2(sK2,sK0)
    | ~ spl3_1
    | ~ spl3_3
    | spl3_7
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f36,f46,f172,f138,f121,f25])).

fof(f395,plain,
    ( ~ spl3_1
    | ~ spl3_3
    | ~ spl3_5
    | spl3_7
    | ~ spl3_9 ),
    inference(avatar_contradiction_clause,[],[f394])).

fof(f394,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_5
    | spl3_7
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f365,f36])).

fof(f365,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl3_3
    | ~ spl3_5
    | spl3_7
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f55,f46,f172,f138,f121,f25])).

fof(f393,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | spl3_7
    | ~ spl3_8 ),
    inference(avatar_contradiction_clause,[],[f392])).

fof(f392,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | spl3_7
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f391,f138])).

fof(f391,plain,
    ( v2_tex_2(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f367,f165])).

fof(f165,plain,
    ( k1_setfam_1(k2_tarski(sK1,sK2)) = k1_setfam_1(k2_tarski(sK2,sK1))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl3_8
  <=> k1_setfam_1(k2_tarski(sK1,sK2)) = k1_setfam_1(k2_tarski(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f367,plain,
    ( v2_tex_2(k1_setfam_1(k2_tarski(sK2,sK1)),sK0)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f36,f55,f46,f31,f130,f25])).

fof(f130,plain,
    ( ! [X0] : m1_subset_1(k1_setfam_1(k2_tarski(X0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f78,f125])).

fof(f125,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),sK1,X0) = k1_setfam_1(k2_tarski(X0,sK1))
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f70,f92])).

fof(f92,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK1) = k1_setfam_1(k2_tarski(X0,sK1))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f41,f32])).

fof(f70,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X0)
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f41,f30])).

fof(f78,plain,
    ( ! [X0] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2 ),
    inference(superposition,[],[f62,f70])).

fof(f62,plain,
    ( ! [X0] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f41,f28])).

fof(f390,plain,
    ( ~ spl3_1
    | ~ spl3_3
    | ~ spl3_5
    | spl3_7
    | ~ spl3_9 ),
    inference(avatar_contradiction_clause,[],[f366])).

fof(f366,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_5
    | spl3_7
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f36,f55,f46,f172,f138,f121,f25])).

fof(f173,plain,
    ( spl3_9
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f168,f163,f170])).

fof(f168,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2)
    | ~ spl3_8 ),
    inference(superposition,[],[f31,f165])).

fof(f166,plain,
    ( spl3_8
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f160,f44,f39,f163])).

fof(f160,plain,
    ( k1_setfam_1(k2_tarski(sK1,sK2)) = k1_setfam_1(k2_tarski(sK2,sK1))
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(superposition,[],[f116,f92])).

fof(f139,plain,
    ( ~ spl3_7
    | ~ spl3_3
    | spl3_6 ),
    inference(avatar_split_clause,[],[f112,f58,f44,f136])).

fof(f58,plain,
    ( spl3_6
  <=> v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f112,plain,
    ( ~ v2_tex_2(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)
    | ~ spl3_3
    | spl3_6 ),
    inference(backward_demodulation,[],[f60,f93])).

fof(f60,plain,
    ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f58])).

fof(f61,plain,(
    ~ spl3_6 ),
    inference(avatar_split_clause,[],[f24,f58])).

fof(f24,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & ( v2_tex_2(sK2,sK0)
      | v2_tex_2(sK1,sK0) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f18,f17,f16])).

fof(f16,plain,
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

fof(f17,plain,
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

fof(f18,plain,
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

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v2_tex_2(X2,X0)
                    | v2_tex_2(X1,X0) )
                 => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
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

fof(f56,plain,
    ( spl3_4
    | spl3_5 ),
    inference(avatar_split_clause,[],[f23,f53,f49])).

fof(f23,plain,
    ( v2_tex_2(sK2,sK0)
    | v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f47,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f22,f44])).

fof(f22,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f42,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f21,f39])).

fof(f21,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f37,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f20,f34])).

fof(f20,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:58:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.41  % (14160)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.46  % (14160)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f408,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f37,f42,f47,f56,f61,f139,f166,f173,f390,f393,f395,f397,f399,f401,f403,f405,f407])).
% 0.21/0.46  fof(f407,plain,(
% 0.21/0.46    ~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | spl3_7),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f406])).
% 0.21/0.46  fof(f406,plain,(
% 0.21/0.46    $false | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | spl3_7)),
% 0.21/0.46    inference(subsumption_resolution,[],[f51,f362])).
% 0.21/0.46  fof(f362,plain,(
% 0.21/0.46    ~v2_tex_2(sK1,sK0) | (~spl3_1 | ~spl3_2 | ~spl3_3 | spl3_7)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f36,f41,f31,f138,f121,f25])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~r1_tarski(X2,X1) | ~v2_tex_2(X1,X0) | v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : (v2_tex_2(X2,X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.46    inference(flattening,[],[f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) | (~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,axiom,(
% 0.21/0.46    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & r1_tarski(X2,X1)) => v2_tex_2(X2,X0)))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_tex_2)).
% 0.21/0.46  fof(f121,plain,(
% 0.21/0.46    ( ! [X0] : (m1_subset_1(k1_setfam_1(k2_tarski(X0,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_3),
% 0.21/0.46    inference(backward_demodulation,[],[f84,f116])).
% 0.21/0.46  fof(f116,plain,(
% 0.21/0.46    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),sK2,X0) = k1_setfam_1(k2_tarski(X0,sK2))) ) | ~spl3_3),
% 0.21/0.46    inference(backward_demodulation,[],[f71,f93])).
% 0.21/0.46  fof(f93,plain,(
% 0.21/0.46    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2))) ) | ~spl3_3),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f46,f32])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))) )),
% 0.21/0.46    inference(definition_unfolding,[],[f29,f27])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.21/0.46  fof(f46,plain,(
% 0.21/0.46    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 0.21/0.46    inference(avatar_component_clause,[],[f44])).
% 0.21/0.46  fof(f44,plain,(
% 0.21/0.46    spl3_3 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.46  fof(f71,plain,(
% 0.21/0.46    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,sK2) = k9_subset_1(u1_struct_0(sK0),sK2,X0)) ) | ~spl3_3),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f46,f30])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).
% 0.21/0.46  fof(f84,plain,(
% 0.21/0.46    ( ! [X0] : (m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK2,X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_3),
% 0.21/0.46    inference(superposition,[],[f63,f71])).
% 0.21/0.46  fof(f63,plain,(
% 0.21/0.46    ( ! [X0] : (m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_3),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f46,f28])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 0.21/0.46  fof(f138,plain,(
% 0.21/0.46    ~v2_tex_2(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) | spl3_7),
% 0.21/0.46    inference(avatar_component_clause,[],[f136])).
% 0.21/0.46  fof(f136,plain,(
% 0.21/0.46    spl3_7 <=> v2_tex_2(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f26,f27])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f39])).
% 0.21/0.46  fof(f39,plain,(
% 0.21/0.46    spl3_2 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    l1_pre_topc(sK0) | ~spl3_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f34])).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    spl3_1 <=> l1_pre_topc(sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.46  fof(f51,plain,(
% 0.21/0.46    v2_tex_2(sK1,sK0) | ~spl3_4),
% 0.21/0.46    inference(avatar_component_clause,[],[f49])).
% 0.21/0.46  fof(f49,plain,(
% 0.21/0.46    spl3_4 <=> v2_tex_2(sK1,sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.46  fof(f405,plain,(
% 0.21/0.46    ~spl3_1 | ~spl3_3 | ~spl3_5 | spl3_7 | ~spl3_9),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f404])).
% 0.21/0.46  fof(f404,plain,(
% 0.21/0.46    $false | (~spl3_1 | ~spl3_3 | ~spl3_5 | spl3_7 | ~spl3_9)),
% 0.21/0.46    inference(subsumption_resolution,[],[f358,f121])).
% 0.21/0.46  fof(f358,plain,(
% 0.21/0.46    ~m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_1 | ~spl3_3 | ~spl3_5 | spl3_7 | ~spl3_9)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f36,f138,f172,f55,f46,f25])).
% 0.21/0.46  fof(f55,plain,(
% 0.21/0.46    v2_tex_2(sK2,sK0) | ~spl3_5),
% 0.21/0.46    inference(avatar_component_clause,[],[f53])).
% 0.21/0.46  fof(f53,plain,(
% 0.21/0.46    spl3_5 <=> v2_tex_2(sK2,sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.46  fof(f172,plain,(
% 0.21/0.46    r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2) | ~spl3_9),
% 0.21/0.46    inference(avatar_component_clause,[],[f170])).
% 0.21/0.46  fof(f170,plain,(
% 0.21/0.46    spl3_9 <=> r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.46  fof(f403,plain,(
% 0.21/0.46    ~spl3_1 | ~spl3_3 | ~spl3_5 | spl3_7 | ~spl3_9),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f402])).
% 0.21/0.46  fof(f402,plain,(
% 0.21/0.46    $false | (~spl3_1 | ~spl3_3 | ~spl3_5 | spl3_7 | ~spl3_9)),
% 0.21/0.46    inference(subsumption_resolution,[],[f360,f138])).
% 0.21/0.46  fof(f360,plain,(
% 0.21/0.46    v2_tex_2(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) | (~spl3_1 | ~spl3_3 | ~spl3_5 | ~spl3_9)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f36,f55,f46,f172,f121,f25])).
% 0.21/0.46  fof(f401,plain,(
% 0.21/0.46    ~spl3_1 | ~spl3_3 | ~spl3_5 | spl3_7 | ~spl3_9),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f400])).
% 0.21/0.46  fof(f400,plain,(
% 0.21/0.46    $false | (~spl3_1 | ~spl3_3 | ~spl3_5 | spl3_7 | ~spl3_9)),
% 0.21/0.46    inference(subsumption_resolution,[],[f361,f172])).
% 0.21/0.46  fof(f361,plain,(
% 0.21/0.46    ~r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2) | (~spl3_1 | ~spl3_3 | ~spl3_5 | spl3_7)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f36,f55,f46,f138,f121,f25])).
% 0.21/0.46  fof(f399,plain,(
% 0.21/0.46    ~spl3_1 | ~spl3_3 | ~spl3_5 | spl3_7 | ~spl3_9),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f398])).
% 0.21/0.46  fof(f398,plain,(
% 0.21/0.46    $false | (~spl3_1 | ~spl3_3 | ~spl3_5 | spl3_7 | ~spl3_9)),
% 0.21/0.46    inference(subsumption_resolution,[],[f363,f46])).
% 0.21/0.46  fof(f363,plain,(
% 0.21/0.46    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_1 | ~spl3_3 | ~spl3_5 | spl3_7 | ~spl3_9)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f36,f55,f172,f138,f121,f25])).
% 0.21/0.46  fof(f397,plain,(
% 0.21/0.46    ~spl3_1 | ~spl3_3 | ~spl3_5 | spl3_7 | ~spl3_9),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f396])).
% 0.21/0.46  fof(f396,plain,(
% 0.21/0.46    $false | (~spl3_1 | ~spl3_3 | ~spl3_5 | spl3_7 | ~spl3_9)),
% 0.21/0.46    inference(subsumption_resolution,[],[f364,f55])).
% 0.21/0.46  fof(f364,plain,(
% 0.21/0.46    ~v2_tex_2(sK2,sK0) | (~spl3_1 | ~spl3_3 | spl3_7 | ~spl3_9)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f36,f46,f172,f138,f121,f25])).
% 0.21/0.46  fof(f395,plain,(
% 0.21/0.46    ~spl3_1 | ~spl3_3 | ~spl3_5 | spl3_7 | ~spl3_9),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f394])).
% 0.21/0.46  fof(f394,plain,(
% 0.21/0.46    $false | (~spl3_1 | ~spl3_3 | ~spl3_5 | spl3_7 | ~spl3_9)),
% 0.21/0.46    inference(subsumption_resolution,[],[f365,f36])).
% 0.21/0.46  fof(f365,plain,(
% 0.21/0.46    ~l1_pre_topc(sK0) | (~spl3_3 | ~spl3_5 | spl3_7 | ~spl3_9)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f55,f46,f172,f138,f121,f25])).
% 0.21/0.46  fof(f393,plain,(
% 0.21/0.46    ~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_5 | spl3_7 | ~spl3_8),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f392])).
% 0.21/0.46  fof(f392,plain,(
% 0.21/0.46    $false | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_5 | spl3_7 | ~spl3_8)),
% 0.21/0.46    inference(subsumption_resolution,[],[f391,f138])).
% 0.21/0.46  fof(f391,plain,(
% 0.21/0.46    v2_tex_2(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_5 | ~spl3_8)),
% 0.21/0.46    inference(forward_demodulation,[],[f367,f165])).
% 0.21/0.46  fof(f165,plain,(
% 0.21/0.46    k1_setfam_1(k2_tarski(sK1,sK2)) = k1_setfam_1(k2_tarski(sK2,sK1)) | ~spl3_8),
% 0.21/0.46    inference(avatar_component_clause,[],[f163])).
% 0.21/0.46  fof(f163,plain,(
% 0.21/0.46    spl3_8 <=> k1_setfam_1(k2_tarski(sK1,sK2)) = k1_setfam_1(k2_tarski(sK2,sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.46  fof(f367,plain,(
% 0.21/0.46    v2_tex_2(k1_setfam_1(k2_tarski(sK2,sK1)),sK0) | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_5)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f36,f55,f46,f31,f130,f25])).
% 0.21/0.46  fof(f130,plain,(
% 0.21/0.46    ( ! [X0] : (m1_subset_1(k1_setfam_1(k2_tarski(X0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_2),
% 0.21/0.46    inference(backward_demodulation,[],[f78,f125])).
% 0.21/0.46  fof(f125,plain,(
% 0.21/0.46    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),sK1,X0) = k1_setfam_1(k2_tarski(X0,sK1))) ) | ~spl3_2),
% 0.21/0.46    inference(backward_demodulation,[],[f70,f92])).
% 0.21/0.46  fof(f92,plain,(
% 0.21/0.46    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,sK1) = k1_setfam_1(k2_tarski(X0,sK1))) ) | ~spl3_2),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f41,f32])).
% 0.21/0.46  fof(f70,plain,(
% 0.21/0.46    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X0)) ) | ~spl3_2),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f41,f30])).
% 0.21/0.46  fof(f78,plain,(
% 0.21/0.46    ( ! [X0] : (m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_2),
% 0.21/0.46    inference(superposition,[],[f62,f70])).
% 0.21/0.46  fof(f62,plain,(
% 0.21/0.46    ( ! [X0] : (m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_2),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f41,f28])).
% 0.21/0.46  fof(f390,plain,(
% 0.21/0.46    ~spl3_1 | ~spl3_3 | ~spl3_5 | spl3_7 | ~spl3_9),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f366])).
% 0.21/0.46  fof(f366,plain,(
% 0.21/0.46    $false | (~spl3_1 | ~spl3_3 | ~spl3_5 | spl3_7 | ~spl3_9)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f36,f55,f46,f172,f138,f121,f25])).
% 0.21/0.46  fof(f173,plain,(
% 0.21/0.46    spl3_9 | ~spl3_8),
% 0.21/0.46    inference(avatar_split_clause,[],[f168,f163,f170])).
% 0.21/0.46  fof(f168,plain,(
% 0.21/0.46    r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2) | ~spl3_8),
% 0.21/0.46    inference(superposition,[],[f31,f165])).
% 0.21/0.46  fof(f166,plain,(
% 0.21/0.46    spl3_8 | ~spl3_2 | ~spl3_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f160,f44,f39,f163])).
% 0.21/0.46  fof(f160,plain,(
% 0.21/0.46    k1_setfam_1(k2_tarski(sK1,sK2)) = k1_setfam_1(k2_tarski(sK2,sK1)) | (~spl3_2 | ~spl3_3)),
% 0.21/0.46    inference(superposition,[],[f116,f92])).
% 0.21/0.46  fof(f139,plain,(
% 0.21/0.46    ~spl3_7 | ~spl3_3 | spl3_6),
% 0.21/0.46    inference(avatar_split_clause,[],[f112,f58,f44,f136])).
% 0.21/0.46  fof(f58,plain,(
% 0.21/0.46    spl3_6 <=> v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.46  fof(f112,plain,(
% 0.21/0.46    ~v2_tex_2(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) | (~spl3_3 | spl3_6)),
% 0.21/0.46    inference(backward_demodulation,[],[f60,f93])).
% 0.21/0.46  fof(f60,plain,(
% 0.21/0.46    ~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) | spl3_6),
% 0.21/0.46    inference(avatar_component_clause,[],[f58])).
% 0.21/0.46  fof(f61,plain,(
% 0.21/0.46    ~spl3_6),
% 0.21/0.46    inference(avatar_split_clause,[],[f24,f58])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    ~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f19])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ((~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & (v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f18,f17,f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & (v2_tex_2(X2,sK0) | v2_tex_2(X1,sK0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & (v2_tex_2(X2,sK0) | v2_tex_2(X1,sK0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & (v2_tex_2(X2,sK0) | v2_tex_2(sK1,sK0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & (v2_tex_2(X2,sK0) | v2_tex_2(sK1,sK0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & (v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.46    inference(flattening,[],[f9])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (? [X2] : ((~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f8])).
% 0.21/0.46  fof(f8,negated_conjecture,(
% 0.21/0.46    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.21/0.46    inference(negated_conjecture,[],[f7])).
% 0.21/0.46  fof(f7,conjecture,(
% 0.21/0.46    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tex_2)).
% 0.21/0.46  fof(f56,plain,(
% 0.21/0.46    spl3_4 | spl3_5),
% 0.21/0.46    inference(avatar_split_clause,[],[f23,f53,f49])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f19])).
% 0.21/0.46  fof(f47,plain,(
% 0.21/0.46    spl3_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f22,f44])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.46    inference(cnf_transformation,[],[f19])).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    spl3_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f21,f39])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.46    inference(cnf_transformation,[],[f19])).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    spl3_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f20,f34])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    l1_pre_topc(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f19])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (14160)------------------------------
% 0.21/0.46  % (14160)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (14160)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (14160)Memory used [KB]: 6780
% 0.21/0.46  % (14160)Time elapsed: 0.051 s
% 0.21/0.46  % (14160)------------------------------
% 0.21/0.46  % (14160)------------------------------
% 0.21/0.46  % (14151)Success in time 0.097 s
%------------------------------------------------------------------------------
