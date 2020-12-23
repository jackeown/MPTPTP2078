%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:52 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 187 expanded)
%              Number of leaves         :   31 (  88 expanded)
%              Depth                    :    7
%              Number of atoms          :  333 ( 706 expanded)
%              Number of equality atoms :   19 (  31 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f422,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f46,f51,f60,f65,f69,f73,f77,f81,f85,f93,f109,f116,f121,f161,f207,f226,f262,f314,f391,f421])).

fof(f421,plain,
    ( ~ spl3_1
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_7
    | spl3_22
    | ~ spl3_29
    | ~ spl3_32
    | ~ spl3_43 ),
    inference(avatar_contradiction_clause,[],[f420])).

fof(f420,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_7
    | spl3_22
    | ~ spl3_29
    | ~ spl3_32
    | ~ spl3_43 ),
    inference(subsumption_resolution,[],[f263,f396])).

fof(f396,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0)
    | ~ spl3_7
    | ~ spl3_43 ),
    inference(superposition,[],[f68,f390])).

fof(f390,plain,
    ( ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)
    | ~ spl3_43 ),
    inference(avatar_component_clause,[],[f389])).

fof(f389,plain,
    ( spl3_43
  <=> ! [X3,X2] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f68,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl3_7
  <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f263,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK2),sK2)
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_5
    | spl3_22
    | ~ spl3_29
    | ~ spl3_32 ),
    inference(unit_resulting_resolution,[],[f40,f59,f50,f160,f261,f225])).

fof(f225,plain,
    ( ! [X4,X2,X3] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
        | ~ r1_tarski(X4,X2)
        | v2_tex_2(X4,X3)
        | ~ v2_tex_2(X2,X3)
        | ~ l1_pre_topc(X3)
        | ~ r1_tarski(X4,u1_struct_0(X3)) )
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f224])).

fof(f224,plain,
    ( spl3_29
  <=> ! [X3,X2,X4] :
        ( ~ v2_tex_2(X2,X3)
        | ~ r1_tarski(X4,X2)
        | v2_tex_2(X4,X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
        | ~ l1_pre_topc(X3)
        | ~ r1_tarski(X4,u1_struct_0(X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f261,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(sK1,X0),u1_struct_0(sK0))
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f260])).

fof(f260,plain,
    ( spl3_32
  <=> ! [X0] : r1_tarski(k3_xboole_0(sK1,X0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f160,plain,
    ( ~ v2_tex_2(k3_xboole_0(sK1,sK2),sK0)
    | spl3_22 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl3_22
  <=> v2_tex_2(k3_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f50,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f59,plain,
    ( v2_tex_2(sK2,sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl3_5
  <=> v2_tex_2(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f40,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl3_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f391,plain,
    ( spl3_43
    | ~ spl3_11
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f210,f205,f83,f389])).

fof(f83,plain,
    ( spl3_11
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f205,plain,
    ( spl3_27
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f210,plain,
    ( ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)
    | ~ spl3_11
    | ~ spl3_27 ),
    inference(superposition,[],[f206,f84])).

fof(f84,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f83])).

fof(f206,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f205])).

fof(f314,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_7
    | spl3_22
    | ~ spl3_29
    | ~ spl3_32 ),
    inference(avatar_contradiction_clause,[],[f313])).

fof(f313,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_7
    | spl3_22
    | ~ spl3_29
    | ~ spl3_32 ),
    inference(subsumption_resolution,[],[f264,f55])).

fof(f55,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl3_4
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f264,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_7
    | spl3_22
    | ~ spl3_29
    | ~ spl3_32 ),
    inference(unit_resulting_resolution,[],[f40,f45,f68,f160,f261,f225])).

fof(f45,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl3_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f262,plain,
    ( spl3_32
    | ~ spl3_13
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f126,f118,f91,f260])).

fof(f91,plain,
    ( spl3_13
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k3_xboole_0(X0,X2),X1)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f118,plain,
    ( spl3_16
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f126,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(sK1,X0),u1_struct_0(sK0))
    | ~ spl3_13
    | ~ spl3_16 ),
    inference(unit_resulting_resolution,[],[f120,f92])).

fof(f92,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k3_xboole_0(X0,X2),X1)
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f91])).

fof(f120,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f118])).

fof(f226,plain,
    ( spl3_29
    | ~ spl3_10
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f125,f114,f79,f224])).

fof(f79,plain,
    ( spl3_10
  <=> ! [X1,X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f114,plain,
    ( spl3_15
  <=> ! [X1,X0,X2] :
        ( v2_tex_2(X2,X0)
        | ~ v2_tex_2(X1,X0)
        | ~ r1_tarski(X2,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f125,plain,
    ( ! [X4,X2,X3] :
        ( ~ v2_tex_2(X2,X3)
        | ~ r1_tarski(X4,X2)
        | v2_tex_2(X4,X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
        | ~ l1_pre_topc(X3)
        | ~ r1_tarski(X4,u1_struct_0(X3)) )
    | ~ spl3_10
    | ~ spl3_15 ),
    inference(resolution,[],[f115,f80])).

fof(f80,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f79])).

fof(f115,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_tex_2(X1,X0)
        | ~ r1_tarski(X2,X1)
        | v2_tex_2(X2,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f114])).

fof(f207,plain,
    ( spl3_27
    | ~ spl3_8
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f100,f83,f71,f205])).

fof(f71,plain,
    ( spl3_8
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f100,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))
    | ~ spl3_8
    | ~ spl3_11 ),
    inference(superposition,[],[f84,f72])).

fof(f72,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f71])).

fof(f161,plain,
    ( ~ spl3_3
    | ~ spl3_22
    | spl3_6
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f112,f107,f62,f158,f48])).

fof(f62,plain,
    ( spl3_6
  <=> v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f107,plain,
    ( spl3_14
  <=> ! [X1,X0,X2] :
        ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f112,plain,
    ( ~ v2_tex_2(k3_xboole_0(sK1,sK2),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_6
    | ~ spl3_14 ),
    inference(superposition,[],[f64,f108])).

fof(f108,plain,
    ( ! [X2,X0,X1] :
        ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f107])).

fof(f64,plain,
    ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f62])).

fof(f121,plain,
    ( spl3_16
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f94,f75,f43,f118])).

fof(f75,plain,
    ( spl3_9
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f94,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f45,f76])).

fof(f76,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r1_tarski(X0,X1) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f75])).

fof(f116,plain,(
    spl3_15 ),
    inference(avatar_split_clause,[],[f28,f114])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ r1_tarski(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f109,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f36,f107])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f93,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f35,f91])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

fof(f85,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f31,f83])).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f81,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f34,f79])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f77,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f33,f75])).

% (6666)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f73,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f30,f71])).

fof(f30,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f69,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f29,f67])).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f65,plain,(
    ~ spl3_6 ),
    inference(avatar_split_clause,[],[f27,f62])).

fof(f27,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & ( v2_tex_2(sK2,sK0)
      | v2_tex_2(sK1,sK0) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f20,f19,f18])).

fof(f18,plain,
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

fof(f19,plain,
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

fof(f20,plain,
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

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v2_tex_2(X2,X0)
                    | v2_tex_2(X1,X0) )
                 => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
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

fof(f60,plain,
    ( spl3_4
    | spl3_5 ),
    inference(avatar_split_clause,[],[f26,f57,f53])).

fof(f26,plain,
    ( v2_tex_2(sK2,sK0)
    | v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f51,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f25,f48])).

fof(f25,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f46,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f24,f43])).

fof(f24,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f41,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f23,f38])).

fof(f23,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:38:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.46  % (6663)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.46  % (6657)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.47  % (6660)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.47  % (6655)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (6650)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.48  % (6662)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.48  % (6652)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (6656)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.48  % (6662)Refutation not found, incomplete strategy% (6662)------------------------------
% 0.22/0.48  % (6662)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (6662)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (6662)Memory used [KB]: 10618
% 0.22/0.48  % (6662)Time elapsed: 0.073 s
% 0.22/0.48  % (6662)------------------------------
% 0.22/0.48  % (6662)------------------------------
% 0.22/0.49  % (6653)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.49  % (6659)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.49  % (6655)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f422,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f41,f46,f51,f60,f65,f69,f73,f77,f81,f85,f93,f109,f116,f121,f161,f207,f226,f262,f314,f391,f421])).
% 0.22/0.49  fof(f421,plain,(
% 0.22/0.49    ~spl3_1 | ~spl3_3 | ~spl3_5 | ~spl3_7 | spl3_22 | ~spl3_29 | ~spl3_32 | ~spl3_43),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f420])).
% 0.22/0.49  fof(f420,plain,(
% 0.22/0.49    $false | (~spl3_1 | ~spl3_3 | ~spl3_5 | ~spl3_7 | spl3_22 | ~spl3_29 | ~spl3_32 | ~spl3_43)),
% 0.22/0.49    inference(subsumption_resolution,[],[f263,f396])).
% 0.22/0.49  fof(f396,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) ) | (~spl3_7 | ~spl3_43)),
% 0.22/0.49    inference(superposition,[],[f68,f390])).
% 0.22/0.49  fof(f390,plain,(
% 0.22/0.49    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) ) | ~spl3_43),
% 0.22/0.49    inference(avatar_component_clause,[],[f389])).
% 0.22/0.49  fof(f389,plain,(
% 0.22/0.49    spl3_43 <=> ! [X3,X2] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).
% 0.22/0.49  fof(f68,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) ) | ~spl3_7),
% 0.22/0.49    inference(avatar_component_clause,[],[f67])).
% 0.22/0.49  fof(f67,plain,(
% 0.22/0.49    spl3_7 <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.49  fof(f263,plain,(
% 0.22/0.49    ~r1_tarski(k3_xboole_0(sK1,sK2),sK2) | (~spl3_1 | ~spl3_3 | ~spl3_5 | spl3_22 | ~spl3_29 | ~spl3_32)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f40,f59,f50,f160,f261,f225])).
% 0.22/0.49  fof(f225,plain,(
% 0.22/0.49    ( ! [X4,X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3))) | ~r1_tarski(X4,X2) | v2_tex_2(X4,X3) | ~v2_tex_2(X2,X3) | ~l1_pre_topc(X3) | ~r1_tarski(X4,u1_struct_0(X3))) ) | ~spl3_29),
% 0.22/0.49    inference(avatar_component_clause,[],[f224])).
% 0.22/0.49  fof(f224,plain,(
% 0.22/0.49    spl3_29 <=> ! [X3,X2,X4] : (~v2_tex_2(X2,X3) | ~r1_tarski(X4,X2) | v2_tex_2(X4,X3) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3))) | ~l1_pre_topc(X3) | ~r1_tarski(X4,u1_struct_0(X3)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.22/0.49  fof(f261,plain,(
% 0.22/0.49    ( ! [X0] : (r1_tarski(k3_xboole_0(sK1,X0),u1_struct_0(sK0))) ) | ~spl3_32),
% 0.22/0.49    inference(avatar_component_clause,[],[f260])).
% 0.22/0.49  fof(f260,plain,(
% 0.22/0.49    spl3_32 <=> ! [X0] : r1_tarski(k3_xboole_0(sK1,X0),u1_struct_0(sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.22/0.49  fof(f160,plain,(
% 0.22/0.49    ~v2_tex_2(k3_xboole_0(sK1,sK2),sK0) | spl3_22),
% 0.22/0.49    inference(avatar_component_clause,[],[f158])).
% 0.22/0.49  fof(f158,plain,(
% 0.22/0.49    spl3_22 <=> v2_tex_2(k3_xboole_0(sK1,sK2),sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f48])).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    spl3_3 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.49  fof(f59,plain,(
% 0.22/0.49    v2_tex_2(sK2,sK0) | ~spl3_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f57])).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    spl3_5 <=> v2_tex_2(sK2,sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    l1_pre_topc(sK0) | ~spl3_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f38])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    spl3_1 <=> l1_pre_topc(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.49  fof(f391,plain,(
% 0.22/0.49    spl3_43 | ~spl3_11 | ~spl3_27),
% 0.22/0.49    inference(avatar_split_clause,[],[f210,f205,f83,f389])).
% 0.22/0.49  fof(f83,plain,(
% 0.22/0.49    spl3_11 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.49  fof(f205,plain,(
% 0.22/0.49    spl3_27 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.22/0.49  fof(f210,plain,(
% 0.22/0.49    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) ) | (~spl3_11 | ~spl3_27)),
% 0.22/0.49    inference(superposition,[],[f206,f84])).
% 0.22/0.49  fof(f84,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) ) | ~spl3_11),
% 0.22/0.49    inference(avatar_component_clause,[],[f83])).
% 0.22/0.49  fof(f206,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) ) | ~spl3_27),
% 0.22/0.49    inference(avatar_component_clause,[],[f205])).
% 0.22/0.49  fof(f314,plain,(
% 0.22/0.49    ~spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_7 | spl3_22 | ~spl3_29 | ~spl3_32),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f313])).
% 0.22/0.49  fof(f313,plain,(
% 0.22/0.49    $false | (~spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_7 | spl3_22 | ~spl3_29 | ~spl3_32)),
% 0.22/0.49    inference(subsumption_resolution,[],[f264,f55])).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    v2_tex_2(sK1,sK0) | ~spl3_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f53])).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    spl3_4 <=> v2_tex_2(sK1,sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.49  fof(f264,plain,(
% 0.22/0.49    ~v2_tex_2(sK1,sK0) | (~spl3_1 | ~spl3_2 | ~spl3_7 | spl3_22 | ~spl3_29 | ~spl3_32)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f40,f45,f68,f160,f261,f225])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f43])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    spl3_2 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.49  fof(f262,plain,(
% 0.22/0.49    spl3_32 | ~spl3_13 | ~spl3_16),
% 0.22/0.49    inference(avatar_split_clause,[],[f126,f118,f91,f260])).
% 0.22/0.49  fof(f91,plain,(
% 0.22/0.49    spl3_13 <=> ! [X1,X0,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.49  fof(f118,plain,(
% 0.22/0.49    spl3_16 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.22/0.49  fof(f126,plain,(
% 0.22/0.49    ( ! [X0] : (r1_tarski(k3_xboole_0(sK1,X0),u1_struct_0(sK0))) ) | (~spl3_13 | ~spl3_16)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f120,f92])).
% 0.22/0.49  fof(f92,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) ) | ~spl3_13),
% 0.22/0.49    inference(avatar_component_clause,[],[f91])).
% 0.22/0.49  fof(f120,plain,(
% 0.22/0.49    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl3_16),
% 0.22/0.49    inference(avatar_component_clause,[],[f118])).
% 0.22/0.49  fof(f226,plain,(
% 0.22/0.49    spl3_29 | ~spl3_10 | ~spl3_15),
% 0.22/0.49    inference(avatar_split_clause,[],[f125,f114,f79,f224])).
% 0.22/0.49  fof(f79,plain,(
% 0.22/0.49    spl3_10 <=> ! [X1,X0] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.49  fof(f114,plain,(
% 0.22/0.49    spl3_15 <=> ! [X1,X0,X2] : (v2_tex_2(X2,X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.49  fof(f125,plain,(
% 0.22/0.49    ( ! [X4,X2,X3] : (~v2_tex_2(X2,X3) | ~r1_tarski(X4,X2) | v2_tex_2(X4,X3) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3))) | ~l1_pre_topc(X3) | ~r1_tarski(X4,u1_struct_0(X3))) ) | (~spl3_10 | ~spl3_15)),
% 0.22/0.49    inference(resolution,[],[f115,f80])).
% 0.22/0.49  fof(f80,plain,(
% 0.22/0.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) ) | ~spl3_10),
% 0.22/0.49    inference(avatar_component_clause,[],[f79])).
% 0.22/0.49  fof(f115,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | v2_tex_2(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl3_15),
% 0.22/0.49    inference(avatar_component_clause,[],[f114])).
% 0.22/0.49  fof(f207,plain,(
% 0.22/0.49    spl3_27 | ~spl3_8 | ~spl3_11),
% 0.22/0.49    inference(avatar_split_clause,[],[f100,f83,f71,f205])).
% 0.22/0.49  fof(f71,plain,(
% 0.22/0.49    spl3_8 <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.49  fof(f100,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) ) | (~spl3_8 | ~spl3_11)),
% 0.22/0.49    inference(superposition,[],[f84,f72])).
% 0.22/0.49  fof(f72,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) ) | ~spl3_8),
% 0.22/0.49    inference(avatar_component_clause,[],[f71])).
% 0.22/0.49  fof(f161,plain,(
% 0.22/0.49    ~spl3_3 | ~spl3_22 | spl3_6 | ~spl3_14),
% 0.22/0.49    inference(avatar_split_clause,[],[f112,f107,f62,f158,f48])).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    spl3_6 <=> v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.49  fof(f107,plain,(
% 0.22/0.49    spl3_14 <=> ! [X1,X0,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.49  fof(f112,plain,(
% 0.22/0.49    ~v2_tex_2(k3_xboole_0(sK1,sK2),sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | (spl3_6 | ~spl3_14)),
% 0.22/0.49    inference(superposition,[],[f64,f108])).
% 0.22/0.49  fof(f108,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) ) | ~spl3_14),
% 0.22/0.49    inference(avatar_component_clause,[],[f107])).
% 0.22/0.49  fof(f64,plain,(
% 0.22/0.49    ~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) | spl3_6),
% 0.22/0.49    inference(avatar_component_clause,[],[f62])).
% 0.22/0.49  fof(f121,plain,(
% 0.22/0.49    spl3_16 | ~spl3_2 | ~spl3_9),
% 0.22/0.49    inference(avatar_split_clause,[],[f94,f75,f43,f118])).
% 0.22/0.49  fof(f75,plain,(
% 0.22/0.49    spl3_9 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.49  fof(f94,plain,(
% 0.22/0.49    r1_tarski(sK1,u1_struct_0(sK0)) | (~spl3_2 | ~spl3_9)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f45,f76])).
% 0.22/0.49  fof(f76,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) ) | ~spl3_9),
% 0.22/0.49    inference(avatar_component_clause,[],[f75])).
% 0.22/0.49  fof(f116,plain,(
% 0.22/0.49    spl3_15),
% 0.22/0.49    inference(avatar_split_clause,[],[f28,f114])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (v2_tex_2(X2,X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (v2_tex_2(X2,X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(flattening,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) | (~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & r1_tarski(X2,X1)) => v2_tex_2(X2,X0)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_tex_2)).
% 0.22/0.49  fof(f109,plain,(
% 0.22/0.49    spl3_14),
% 0.22/0.49    inference(avatar_split_clause,[],[f36,f107])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.22/0.49  fof(f93,plain,(
% 0.22/0.49    spl3_13),
% 0.22/0.49    inference(avatar_split_clause,[],[f35,f91])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).
% 0.22/0.49  fof(f85,plain,(
% 0.22/0.49    spl3_11),
% 0.22/0.49    inference(avatar_split_clause,[],[f31,f83])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.49  fof(f81,plain,(
% 0.22/0.49    spl3_10),
% 0.22/0.49    inference(avatar_split_clause,[],[f34,f79])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.49    inference(nnf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.49  fof(f77,plain,(
% 0.22/0.49    spl3_9),
% 0.22/0.49    inference(avatar_split_clause,[],[f33,f75])).
% 0.22/0.49  % (6666)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f22])).
% 0.22/0.49  fof(f73,plain,(
% 0.22/0.49    spl3_8),
% 0.22/0.49    inference(avatar_split_clause,[],[f30,f71])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.22/0.49  fof(f69,plain,(
% 0.22/0.49    spl3_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f29,f67])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    ~spl3_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f27,f62])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ((~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & (v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f20,f19,f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & (v2_tex_2(X2,sK0) | v2_tex_2(X1,sK0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & (v2_tex_2(X2,sK0) | v2_tex_2(X1,sK0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & (v2_tex_2(X2,sK0) | v2_tex_2(sK1,sK0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & (v2_tex_2(X2,sK0) | v2_tex_2(sK1,sK0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & (v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.49    inference(flattening,[],[f11])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : ((~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,negated_conjecture,(
% 0.22/0.49    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.22/0.49    inference(negated_conjecture,[],[f9])).
% 0.22/0.49  fof(f9,conjecture,(
% 0.22/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tex_2)).
% 0.22/0.49  fof(f60,plain,(
% 0.22/0.49    spl3_4 | spl3_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f26,f57,f53])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f21])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    spl3_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f25,f48])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.49    inference(cnf_transformation,[],[f21])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    spl3_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f24,f43])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.49    inference(cnf_transformation,[],[f21])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    spl3_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f23,f38])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    l1_pre_topc(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f21])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (6655)------------------------------
% 0.22/0.49  % (6655)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (6655)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (6655)Memory used [KB]: 6396
% 0.22/0.49  % (6655)Time elapsed: 0.072 s
% 0.22/0.49  % (6655)------------------------------
% 0.22/0.49  % (6655)------------------------------
% 0.22/0.50  % (6649)Success in time 0.139 s
%------------------------------------------------------------------------------
