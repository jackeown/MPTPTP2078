%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1966+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:58 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  269 ( 654 expanded)
%              Number of leaves         :   65 ( 291 expanded)
%              Depth                    :   12
%              Number of atoms          :  973 (1956 expanded)
%              Number of equality atoms :   89 ( 299 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f691,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f109,f114,f119,f127,f132,f137,f142,f147,f152,f158,f164,f181,f247,f251,f257,f259,f262,f264,f266,f272,f281,f291,f305,f306,f444,f463,f470,f485,f490,f495,f500,f539,f545,f547,f561,f563,f574,f586,f629,f632,f638,f651,f652,f671,f689])).

fof(f689,plain,
    ( ~ spl4_9
    | spl4_37
    | spl4_79
    | ~ spl4_31
    | ~ spl4_35
    | ~ spl4_38 ),
    inference(avatar_split_clause,[],[f688,f337,f310,f289,f668,f332,f144])).

fof(f144,plain,
    ( spl4_9
  <=> v1_finset_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f332,plain,
    ( spl4_37
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f668,plain,
    ( spl4_79
  <=> r2_hidden(k1_setfam_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_79])])).

fof(f289,plain,
    ( spl4_31
  <=> ! [X0] :
        ( ~ v1_finset_1(X0)
        | r2_hidden(k2_yellow_0(k3_yellow_1(sK0),X0),sK1)
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f310,plain,
    ( spl4_35
  <=> m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f337,plain,
    ( spl4_38
  <=> k1_setfam_1(sK2) = k2_yellow_0(k3_yellow_1(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f688,plain,
    ( r2_hidden(k1_setfam_1(sK2),sK1)
    | k1_xboole_0 = sK2
    | ~ v1_finset_1(sK2)
    | ~ spl4_31
    | ~ spl4_35
    | ~ spl4_38 ),
    inference(forward_demodulation,[],[f686,f339])).

fof(f339,plain,
    ( k1_setfam_1(sK2) = k2_yellow_0(k3_yellow_1(sK0),sK2)
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f337])).

fof(f686,plain,
    ( r2_hidden(k2_yellow_0(k3_yellow_1(sK0),sK2),sK1)
    | k1_xboole_0 = sK2
    | ~ v1_finset_1(sK2)
    | ~ spl4_31
    | ~ spl4_35 ),
    inference(resolution,[],[f290,f312])).

fof(f312,plain,
    ( m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK1)))
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f310])).

fof(f290,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(sK1)))
        | r2_hidden(k2_yellow_0(k3_yellow_1(sK0),X0),sK1)
        | k1_xboole_0 = X0
        | ~ v1_finset_1(X0) )
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f289])).

fof(f671,plain,
    ( ~ spl4_79
    | spl4_6
    | ~ spl4_49 ),
    inference(avatar_split_clause,[],[f666,f392,f129,f668])).

fof(f129,plain,
    ( spl4_6
  <=> r2_hidden(k8_setfam_1(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f392,plain,
    ( spl4_49
  <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).

fof(f666,plain,
    ( ~ r2_hidden(k1_setfam_1(sK2),sK1)
    | spl4_6
    | ~ spl4_49 ),
    inference(backward_demodulation,[],[f131,f394])).

fof(f394,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ spl4_49 ),
    inference(avatar_component_clause,[],[f392])).

fof(f131,plain,
    ( ~ r2_hidden(k8_setfam_1(sK0,sK2),sK1)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f129])).

fof(f652,plain,
    ( spl4_40
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f643,f139,f346])).

fof(f346,plain,
    ( spl4_40
  <=> k6_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f139,plain,
    ( spl4_8
  <=> m1_subset_1(sK2,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f643,plain,
    ( k6_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ spl4_8 ),
    inference(resolution,[],[f141,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X0)))))
      | k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    inference(definition_unfolding,[],[f80,f88,f88])).

fof(f88,plain,(
    ! [X0] : k1_zfmisc_1(X0) = u1_struct_0(k3_yellow_1(X0)) ),
    inference(definition_unfolding,[],[f58,f60])).

fof(f60,plain,(
    ! [X0] : k9_setfam_1(X0) = u1_struct_0(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : k9_setfam_1(X0) = u1_struct_0(k3_yellow_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_waybel_7)).

fof(f58,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(f141,plain,
    ( m1_subset_1(sK2,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(sK0)))))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f139])).

fof(f651,plain,
    ( spl4_38
    | spl4_39
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f642,f139,f341,f337])).

fof(f341,plain,
    ( spl4_39
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f642,plain,
    ( v1_xboole_0(sK2)
    | k1_setfam_1(sK2) = k2_yellow_0(k3_yellow_1(sK0),sK2)
    | ~ spl4_8 ),
    inference(resolution,[],[f141,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X0)))))
      | v1_xboole_0(X1)
      | k1_setfam_1(X1) = k2_yellow_0(k3_yellow_1(X0),X1) ) ),
    inference(definition_unfolding,[],[f83,f88])).

fof(f83,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      | k1_setfam_1(X1) = k2_yellow_0(k3_yellow_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(X1) = k2_yellow_0(k3_yellow_1(X0),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(X1) = k2_yellow_0(k3_yellow_1(X0),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
        & ~ v1_xboole_0(X1) )
     => k1_setfam_1(X1) = k2_yellow_0(k3_yellow_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_yellow_1)).

fof(f638,plain,
    ( spl4_35
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f637,f134,f310])).

fof(f134,plain,
    ( spl4_7
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f637,plain,
    ( m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK1)))
    | ~ spl4_7 ),
    inference(resolution,[],[f136,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,u1_struct_0(k3_yellow_1(X1))) ) ),
    inference(definition_unfolding,[],[f84,f88])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f136,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f134])).

fof(f632,plain,
    ( sK0 != k8_setfam_1(sK0,k1_xboole_0)
    | k1_xboole_0 != sK2
    | r2_hidden(k8_setfam_1(sK0,sK2),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f629,plain,
    ( spl4_78
    | ~ spl4_52 ),
    inference(avatar_split_clause,[],[f615,f416,f626])).

fof(f626,plain,
    ( spl4_78
  <=> sK0 = k8_setfam_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_78])])).

fof(f416,plain,
    ( spl4_52
  <=> m1_subset_1(k1_xboole_0,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f615,plain,
    ( sK0 = k8_setfam_1(sK0,k1_xboole_0)
    | ~ spl4_52 ),
    inference(resolution,[],[f418,f104])).

fof(f104,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X0)))))
      | k8_setfam_1(X0,k1_xboole_0) = X0 ) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X0)))))
      | k1_xboole_0 != X1
      | k8_setfam_1(X0,X1) = X0 ) ),
    inference(definition_unfolding,[],[f81,f88,f88])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 != X1
      | k8_setfam_1(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

fof(f418,plain,
    ( m1_subset_1(k1_xboole_0,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(sK0)))))
    | ~ spl4_52 ),
    inference(avatar_component_clause,[],[f416])).

fof(f586,plain,
    ( spl4_52
    | ~ spl4_8
    | ~ spl4_37 ),
    inference(avatar_split_clause,[],[f578,f332,f139,f416])).

fof(f578,plain,
    ( m1_subset_1(k1_xboole_0,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(sK0)))))
    | ~ spl4_8
    | ~ spl4_37 ),
    inference(backward_demodulation,[],[f141,f334])).

fof(f334,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f332])).

fof(f574,plain,
    ( spl4_37
    | spl4_49
    | ~ spl4_8
    | ~ spl4_40 ),
    inference(avatar_split_clause,[],[f573,f346,f139,f392,f332])).

fof(f573,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | k1_xboole_0 = sK2
    | ~ spl4_8
    | ~ spl4_40 ),
    inference(forward_demodulation,[],[f564,f348])).

fof(f348,plain,
    ( k6_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f346])).

fof(f564,plain,
    ( k1_xboole_0 = sK2
    | k8_setfam_1(sK0,sK2) = k6_setfam_1(sK0,sK2)
    | ~ spl4_8 ),
    inference(resolution,[],[f141,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X0)))))
      | k1_xboole_0 = X1
      | k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f82,f88,f88])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 = X1
      | k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f563,plain,(
    ~ spl4_32 ),
    inference(avatar_contradiction_clause,[],[f562])).

fof(f562,plain,
    ( $false
    | ~ spl4_32 ),
    inference(resolution,[],[f296,f61])).

fof(f61,plain,(
    ! [X0] : ~ v2_struct_0(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v5_orders_2(k3_yellow_1(X0))
      & v4_orders_2(k3_yellow_1(X0))
      & v3_orders_2(k3_yellow_1(X0))
      & ~ v2_struct_0(k3_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v5_orders_2(k3_yellow_1(X0))
      & v4_orders_2(k3_yellow_1(X0))
      & v3_orders_2(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0))
      & ~ v2_struct_0(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_yellow_1)).

fof(f296,plain,
    ( v2_struct_0(k3_yellow_1(sK0))
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f294])).

fof(f294,plain,
    ( spl4_32
  <=> v2_struct_0(k3_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f561,plain,(
    spl4_33 ),
    inference(avatar_contradiction_clause,[],[f560])).

fof(f560,plain,
    ( $false
    | spl4_33 ),
    inference(resolution,[],[f300,f171])).

fof(f171,plain,(
    ! [X0] : v2_yellow_0(k3_yellow_1(X0)) ),
    inference(global_subsumption,[],[f61,f66,f170])).

fof(f170,plain,(
    ! [X0] :
      ( v2_struct_0(k3_yellow_1(X0))
      | ~ l1_orders_2(k3_yellow_1(X0))
      | v2_yellow_0(k3_yellow_1(X0)) ) ),
    inference(resolution,[],[f168,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v9_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | v2_yellow_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v2_yellow_0(X0)
        & ~ v2_struct_0(X0) )
      | ~ v9_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v2_yellow_0(X0)
        & ~ v2_struct_0(X0) )
      | ~ v9_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v9_waybel_1(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_yellow_0(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc7_waybel_1)).

fof(f168,plain,(
    ! [X0] : v9_waybel_1(k3_yellow_1(X0)) ),
    inference(global_subsumption,[],[f61,f66,f167])).

fof(f167,plain,(
    ! [X0] :
      ( v2_struct_0(k3_yellow_1(X0))
      | ~ l1_orders_2(k3_yellow_1(X0))
      | v9_waybel_1(k3_yellow_1(X0)) ) ),
    inference(resolution,[],[f68,f65])).

fof(f65,plain,(
    ! [X0] : v11_waybel_1(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] : v11_waybel_1(k3_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v11_waybel_1(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_waybel_7)).

fof(f68,plain,(
    ! [X0] :
      ( ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | v9_waybel_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v9_waybel_1(X0)
        & ~ v2_struct_0(X0) )
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v9_waybel_1(X0)
        & ~ v2_struct_0(X0) )
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v11_waybel_1(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_waybel_1(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc10_waybel_1)).

fof(f66,plain,(
    ! [X0] : l1_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] : l1_orders_2(k3_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_1)).

fof(f300,plain,
    ( ~ v2_yellow_0(k3_yellow_1(sK0))
    | spl4_33 ),
    inference(avatar_component_clause,[],[f298])).

fof(f298,plain,
    ( spl4_33
  <=> v2_yellow_0(k3_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f547,plain,
    ( spl4_4
    | ~ spl4_22
    | ~ spl4_1
    | ~ spl4_2
    | spl4_3
    | ~ spl4_23
    | ~ spl4_24
    | ~ spl4_25
    | ~ spl4_26
    | ~ spl4_73
    | ~ spl4_63 ),
    inference(avatar_split_clause,[],[f546,f492,f542,f244,f240,f236,f232,f116,f111,f106,f228,f121])).

fof(f121,plain,
    ( spl4_4
  <=> v2_waybel_0(sK1,k3_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f228,plain,
    ( spl4_22
  <=> v3_orders_2(k3_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f106,plain,
    ( spl4_1
  <=> m1_subset_1(sK1,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f111,plain,
    ( spl4_2
  <=> v13_waybel_0(sK1,k3_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f116,plain,
    ( spl4_3
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f232,plain,
    ( spl4_23
  <=> l1_orders_2(k3_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f236,plain,
    ( spl4_24
  <=> v2_lattice3(k3_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f240,plain,
    ( spl4_25
  <=> v5_orders_2(k3_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f244,plain,
    ( spl4_26
  <=> v4_orders_2(k3_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f542,plain,
    ( spl4_73
  <=> r2_hidden(k1_setfam_1(sK3(k3_yellow_1(sK0),sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_73])])).

fof(f492,plain,
    ( spl4_63
  <=> k1_setfam_1(sK3(k3_yellow_1(sK0),sK1)) = k2_yellow_0(k3_yellow_1(sK0),sK3(k3_yellow_1(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_63])])).

fof(f546,plain,
    ( ~ r2_hidden(k1_setfam_1(sK3(k3_yellow_1(sK0),sK1)),sK1)
    | ~ v4_orders_2(k3_yellow_1(sK0))
    | ~ v5_orders_2(k3_yellow_1(sK0))
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | v1_xboole_0(sK1)
    | ~ v13_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(sK0)))))
    | ~ v3_orders_2(k3_yellow_1(sK0))
    | v2_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ spl4_63 ),
    inference(superposition,[],[f93,f494])).

fof(f494,plain,
    ( k1_setfam_1(sK3(k3_yellow_1(sK0),sK1)) = k2_yellow_0(k3_yellow_1(sK0),sK3(k3_yellow_1(sK0),sK1))
    | ~ spl4_63 ),
    inference(avatar_component_clause,[],[f492])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k2_yellow_0(X0,sK3(X0,X1)),X1)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(u1_struct_0(X0))))
      | ~ v3_orders_2(X0)
      | v2_waybel_0(X1,X0) ) ),
    inference(definition_unfolding,[],[f79,f88])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(k2_yellow_0(X0,sK3(X0,X1)),X1)
      | v2_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k2_yellow_0(X0,X2),X1)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X2) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k2_yellow_0(X0,X2),X1)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X2) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
                  & v1_finset_1(X2) )
               => ( k1_xboole_0 != X2
                 => r2_hidden(k2_yellow_0(X0,X2),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_waybel_0)).

fof(f545,plain,
    ( spl4_73
    | ~ spl4_61
    | ~ spl4_72 ),
    inference(avatar_split_clause,[],[f540,f536,f482,f542])).

fof(f482,plain,
    ( spl4_61
  <=> r2_hidden(k8_setfam_1(sK0,sK3(k3_yellow_1(sK0),sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).

fof(f536,plain,
    ( spl4_72
  <=> k8_setfam_1(sK0,sK3(k3_yellow_1(sK0),sK1)) = k1_setfam_1(sK3(k3_yellow_1(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_72])])).

fof(f540,plain,
    ( r2_hidden(k1_setfam_1(sK3(k3_yellow_1(sK0),sK1)),sK1)
    | ~ spl4_61
    | ~ spl4_72 ),
    inference(backward_demodulation,[],[f484,f538])).

fof(f538,plain,
    ( k8_setfam_1(sK0,sK3(k3_yellow_1(sK0),sK1)) = k1_setfam_1(sK3(k3_yellow_1(sK0),sK1))
    | ~ spl4_72 ),
    inference(avatar_component_clause,[],[f536])).

fof(f484,plain,
    ( r2_hidden(k8_setfam_1(sK0,sK3(k3_yellow_1(sK0),sK1)),sK1)
    | ~ spl4_61 ),
    inference(avatar_component_clause,[],[f482])).

fof(f539,plain,
    ( spl4_72
    | ~ spl4_62
    | ~ spl4_64 ),
    inference(avatar_split_clause,[],[f534,f497,f487,f536])).

fof(f487,plain,
    ( spl4_62
  <=> k8_setfam_1(sK0,sK3(k3_yellow_1(sK0),sK1)) = k6_setfam_1(sK0,sK3(k3_yellow_1(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).

fof(f497,plain,
    ( spl4_64
  <=> k6_setfam_1(sK0,sK3(k3_yellow_1(sK0),sK1)) = k1_setfam_1(sK3(k3_yellow_1(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).

fof(f534,plain,
    ( k8_setfam_1(sK0,sK3(k3_yellow_1(sK0),sK1)) = k1_setfam_1(sK3(k3_yellow_1(sK0),sK1))
    | ~ spl4_62
    | ~ spl4_64 ),
    inference(forward_demodulation,[],[f489,f499])).

fof(f499,plain,
    ( k6_setfam_1(sK0,sK3(k3_yellow_1(sK0),sK1)) = k1_setfam_1(sK3(k3_yellow_1(sK0),sK1))
    | ~ spl4_64 ),
    inference(avatar_component_clause,[],[f497])).

fof(f489,plain,
    ( k8_setfam_1(sK0,sK3(k3_yellow_1(sK0),sK1)) = k6_setfam_1(sK0,sK3(k3_yellow_1(sK0),sK1))
    | ~ spl4_62 ),
    inference(avatar_component_clause,[],[f487])).

fof(f500,plain,
    ( spl4_64
    | ~ spl4_60 ),
    inference(avatar_split_clause,[],[f474,f467,f497])).

fof(f467,plain,
    ( spl4_60
  <=> m1_subset_1(sK3(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).

fof(f474,plain,
    ( k6_setfam_1(sK0,sK3(k3_yellow_1(sK0),sK1)) = k1_setfam_1(sK3(k3_yellow_1(sK0),sK1))
    | ~ spl4_60 ),
    inference(resolution,[],[f469,f98])).

fof(f469,plain,
    ( m1_subset_1(sK3(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(sK0)))))
    | ~ spl4_60 ),
    inference(avatar_component_clause,[],[f467])).

fof(f495,plain,
    ( spl4_63
    | spl4_29
    | ~ spl4_60 ),
    inference(avatar_split_clause,[],[f473,f467,f277,f492])).

fof(f277,plain,
    ( spl4_29
  <=> v1_xboole_0(sK3(k3_yellow_1(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f473,plain,
    ( v1_xboole_0(sK3(k3_yellow_1(sK0),sK1))
    | k1_setfam_1(sK3(k3_yellow_1(sK0),sK1)) = k2_yellow_0(k3_yellow_1(sK0),sK3(k3_yellow_1(sK0),sK1))
    | ~ spl4_60 ),
    inference(resolution,[],[f469,f101])).

fof(f490,plain,
    ( spl4_62
    | spl4_27
    | ~ spl4_60 ),
    inference(avatar_split_clause,[],[f472,f467,f254,f487])).

fof(f254,plain,
    ( spl4_27
  <=> k1_xboole_0 = sK3(k3_yellow_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f472,plain,
    ( k1_xboole_0 = sK3(k3_yellow_1(sK0),sK1)
    | k8_setfam_1(sK0,sK3(k3_yellow_1(sK0),sK1)) = k6_setfam_1(sK0,sK3(k3_yellow_1(sK0),sK1))
    | ~ spl4_60 ),
    inference(resolution,[],[f469,f99])).

fof(f485,plain,
    ( ~ spl4_21
    | ~ spl4_30
    | spl4_61
    | ~ spl4_5
    | ~ spl4_60 ),
    inference(avatar_split_clause,[],[f471,f467,f125,f482,f284,f224])).

fof(f224,plain,
    ( spl4_21
  <=> v1_finset_1(sK3(k3_yellow_1(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f284,plain,
    ( spl4_30
  <=> r1_tarski(sK3(k3_yellow_1(sK0),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f125,plain,
    ( spl4_5
  <=> ! [X2] :
        ( ~ v1_finset_1(X2)
        | r2_hidden(k8_setfam_1(sK0,X2),sK1)
        | ~ r1_tarski(X2,sK1)
        | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(sK0))))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f471,plain,
    ( r2_hidden(k8_setfam_1(sK0,sK3(k3_yellow_1(sK0),sK1)),sK1)
    | ~ r1_tarski(sK3(k3_yellow_1(sK0),sK1),sK1)
    | ~ v1_finset_1(sK3(k3_yellow_1(sK0),sK1))
    | ~ spl4_5
    | ~ spl4_60 ),
    inference(resolution,[],[f469,f126])).

fof(f126,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(sK0)))))
        | r2_hidden(k8_setfam_1(sK0,X2),sK1)
        | ~ r1_tarski(X2,sK1)
        | ~ v1_finset_1(X2) )
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f125])).

fof(f470,plain,
    ( spl4_60
    | ~ spl4_59 ),
    inference(avatar_split_clause,[],[f465,f460,f467])).

fof(f460,plain,
    ( spl4_59
  <=> r1_tarski(sK3(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).

fof(f465,plain,
    ( m1_subset_1(sK3(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(sK0)))))
    | ~ spl4_59 ),
    inference(resolution,[],[f462,f103])).

fof(f462,plain,
    ( r1_tarski(sK3(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | ~ spl4_59 ),
    inference(avatar_component_clause,[],[f460])).

fof(f463,plain,
    ( spl4_59
    | ~ spl4_13
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f458,f284,f178,f460])).

fof(f178,plain,
    ( spl4_13
  <=> r1_tarski(sK1,u1_struct_0(k3_yellow_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f458,plain,
    ( r1_tarski(sK3(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | ~ spl4_13
    | ~ spl4_30 ),
    inference(resolution,[],[f314,f180])).

fof(f180,plain,
    ( r1_tarski(sK1,u1_struct_0(k3_yellow_1(sK0)))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f178])).

fof(f314,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | r1_tarski(sK3(k3_yellow_1(sK0),sK1),X0) )
    | ~ spl4_30 ),
    inference(resolution,[],[f286,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f286,plain,
    ( r1_tarski(sK3(k3_yellow_1(sK0),sK1),sK1)
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f284])).

fof(f444,plain,
    ( ~ spl4_12
    | ~ spl4_39
    | spl4_37 ),
    inference(avatar_split_clause,[],[f442,f332,f341,f161])).

fof(f161,plain,
    ( spl4_12
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f442,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ v1_xboole_0(k1_xboole_0)
    | spl4_37 ),
    inference(extensionality_resolution,[],[f86,f333])).

fof(f333,plain,
    ( k1_xboole_0 != sK2
    | spl4_37 ),
    inference(avatar_component_clause,[],[f332])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(f306,plain,
    ( spl4_30
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f282,f269,f284])).

fof(f269,plain,
    ( spl4_28
  <=> m1_subset_1(sK3(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f282,plain,
    ( r1_tarski(sK3(k3_yellow_1(sK0),sK1),sK1)
    | ~ spl4_28 ),
    inference(resolution,[],[f271,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f85,f88])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f271,plain,
    ( m1_subset_1(sK3(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK1)))
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f269])).

fof(f305,plain,
    ( spl4_32
    | ~ spl4_2
    | ~ spl4_4
    | spl4_3
    | ~ spl4_23
    | ~ spl4_33
    | ~ spl4_25
    | ~ spl4_26
    | ~ spl4_22
    | spl4_34
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f292,f106,f302,f228,f244,f240,f298,f232,f116,f121,f111,f294])).

fof(f302,plain,
    ( spl4_34
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f292,plain,
    ( r2_hidden(sK0,sK1)
    | ~ v3_orders_2(k3_yellow_1(sK0))
    | ~ v4_orders_2(k3_yellow_1(sK0))
    | ~ v5_orders_2(k3_yellow_1(sK0))
    | ~ v2_yellow_0(k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | v1_xboole_0(sK1)
    | ~ v2_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ v13_waybel_0(sK1,k3_yellow_1(sK0))
    | v2_struct_0(k3_yellow_1(sK0))
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f260,f59])).

fof(f59,plain,(
    ! [X0] : k4_yellow_0(k3_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k4_yellow_0(k3_yellow_1(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_yellow_1)).

fof(f260,plain,
    ( ~ v3_orders_2(k3_yellow_1(sK0))
    | ~ v4_orders_2(k3_yellow_1(sK0))
    | ~ v5_orders_2(k3_yellow_1(sK0))
    | ~ v2_yellow_0(k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | v1_xboole_0(sK1)
    | ~ v2_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ v13_waybel_0(sK1,k3_yellow_1(sK0))
    | v2_struct_0(k3_yellow_1(sK0))
    | r2_hidden(k4_yellow_0(k3_yellow_1(sK0)),sK1)
    | ~ spl4_1 ),
    inference(resolution,[],[f92,f108])).

fof(f108,plain,
    ( m1_subset_1(sK1,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(sK0)))))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f106])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(u1_struct_0(X0))))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v2_waybel_0(X1,X0)
      | ~ v13_waybel_0(X1,X0)
      | v2_struct_0(X0)
      | r2_hidden(k4_yellow_0(X0),X1) ) ),
    inference(definition_unfolding,[],[f74,f88])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v2_waybel_0(X1,X0)
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(k4_yellow_0(X0),X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(k4_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(k4_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => r2_hidden(k4_yellow_0(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_waybel_4)).

fof(f291,plain,
    ( ~ spl4_4
    | spl4_31
    | ~ spl4_22
    | ~ spl4_2
    | spl4_3
    | ~ spl4_23
    | ~ spl4_24
    | ~ spl4_25
    | ~ spl4_26
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f273,f106,f244,f240,f236,f232,f116,f111,f228,f289,f121])).

fof(f273,plain,
    ( ! [X0] :
        ( ~ v4_orders_2(k3_yellow_1(sK0))
        | ~ v5_orders_2(k3_yellow_1(sK0))
        | ~ v2_lattice3(k3_yellow_1(sK0))
        | ~ l1_orders_2(k3_yellow_1(sK0))
        | v1_xboole_0(sK1)
        | ~ v13_waybel_0(sK1,k3_yellow_1(sK0))
        | ~ v3_orders_2(k3_yellow_1(sK0))
        | ~ v1_finset_1(X0)
        | ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(sK1)))
        | k1_xboole_0 = X0
        | r2_hidden(k2_yellow_0(k3_yellow_1(sK0),X0),sK1)
        | ~ v2_waybel_0(sK1,k3_yellow_1(sK0)) )
    | ~ spl4_1 ),
    inference(resolution,[],[f97,f108])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(u1_struct_0(X0))))
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v13_waybel_0(X1,X0)
      | ~ v3_orders_2(X0)
      | ~ v1_finset_1(X2)
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | k1_xboole_0 = X2
      | r2_hidden(k2_yellow_0(X0,X2),X1)
      | ~ v2_waybel_0(X1,X0) ) ),
    inference(definition_unfolding,[],[f75,f88,f88])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_finset_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | k1_xboole_0 = X2
      | r2_hidden(k2_yellow_0(X0,X2),X1)
      | ~ v2_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f281,plain,
    ( ~ spl4_12
    | ~ spl4_29
    | spl4_27 ),
    inference(avatar_split_clause,[],[f275,f254,f277,f161])).

fof(f275,plain,
    ( ~ v1_xboole_0(sK3(k3_yellow_1(sK0),sK1))
    | ~ v1_xboole_0(k1_xboole_0)
    | spl4_27 ),
    inference(extensionality_resolution,[],[f86,f256])).

fof(f256,plain,
    ( k1_xboole_0 != sK3(k3_yellow_1(sK0),sK1)
    | spl4_27 ),
    inference(avatar_component_clause,[],[f254])).

fof(f272,plain,
    ( spl4_4
    | spl4_28
    | ~ spl4_22
    | ~ spl4_2
    | spl4_3
    | ~ spl4_23
    | ~ spl4_24
    | ~ spl4_25
    | ~ spl4_26
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f267,f106,f244,f240,f236,f232,f116,f111,f228,f269,f121])).

fof(f267,plain,
    ( ~ v4_orders_2(k3_yellow_1(sK0))
    | ~ v5_orders_2(k3_yellow_1(sK0))
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | v1_xboole_0(sK1)
    | ~ v13_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ v3_orders_2(k3_yellow_1(sK0))
    | m1_subset_1(sK3(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK1)))
    | v2_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ spl4_1 ),
    inference(resolution,[],[f95,f108])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(u1_struct_0(X0))))
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v13_waybel_0(X1,X0)
      | ~ v3_orders_2(X0)
      | m1_subset_1(sK3(X0,X1),u1_struct_0(k3_yellow_1(X1)))
      | v2_waybel_0(X1,X0) ) ),
    inference(definition_unfolding,[],[f77,f88,f88])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(X1))
      | v2_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f266,plain,(
    spl4_26 ),
    inference(avatar_contradiction_clause,[],[f265])).

fof(f265,plain,
    ( $false
    | spl4_26 ),
    inference(resolution,[],[f246,f63])).

fof(f63,plain,(
    ! [X0] : v4_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f246,plain,
    ( ~ v4_orders_2(k3_yellow_1(sK0))
    | spl4_26 ),
    inference(avatar_component_clause,[],[f244])).

fof(f264,plain,(
    spl4_25 ),
    inference(avatar_contradiction_clause,[],[f263])).

fof(f263,plain,
    ( $false
    | spl4_25 ),
    inference(resolution,[],[f242,f64])).

fof(f64,plain,(
    ! [X0] : v5_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f242,plain,
    ( ~ v5_orders_2(k3_yellow_1(sK0))
    | spl4_25 ),
    inference(avatar_component_clause,[],[f240])).

fof(f262,plain,(
    spl4_24 ),
    inference(avatar_contradiction_clause,[],[f261])).

fof(f261,plain,
    ( $false
    | spl4_24 ),
    inference(resolution,[],[f238,f175])).

fof(f175,plain,(
    ! [X0] : v2_lattice3(k3_yellow_1(X0)) ),
    inference(global_subsumption,[],[f61,f66,f174])).

fof(f174,plain,(
    ! [X0] :
      ( v2_struct_0(k3_yellow_1(X0))
      | ~ l1_orders_2(k3_yellow_1(X0))
      | v2_lattice3(k3_yellow_1(X0)) ) ),
    inference(resolution,[],[f72,f65])).

fof(f72,plain,(
    ! [X0] :
      ( ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | v2_lattice3(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( v2_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v2_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v11_waybel_1(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v11_waybel_1(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v11_waybel_1(X0)
          & ~ v2_struct_0(X0) )
       => ( v3_yellow_0(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v11_waybel_1(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_waybel_1(X0)
          & v3_yellow_0(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v11_waybel_1(X0)
          & ~ v2_struct_0(X0) )
       => ( v10_waybel_1(X0)
          & v2_waybel_1(X0)
          & v3_yellow_0(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc8_waybel_1)).

fof(f238,plain,
    ( ~ v2_lattice3(k3_yellow_1(sK0))
    | spl4_24 ),
    inference(avatar_component_clause,[],[f236])).

fof(f259,plain,(
    spl4_23 ),
    inference(avatar_contradiction_clause,[],[f258])).

fof(f258,plain,
    ( $false
    | spl4_23 ),
    inference(resolution,[],[f234,f66])).

fof(f234,plain,
    ( ~ l1_orders_2(k3_yellow_1(sK0))
    | spl4_23 ),
    inference(avatar_component_clause,[],[f232])).

fof(f257,plain,
    ( spl4_4
    | ~ spl4_27
    | ~ spl4_22
    | ~ spl4_2
    | spl4_3
    | ~ spl4_23
    | ~ spl4_24
    | ~ spl4_25
    | ~ spl4_26
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f252,f106,f244,f240,f236,f232,f116,f111,f228,f254,f121])).

fof(f252,plain,
    ( ~ v4_orders_2(k3_yellow_1(sK0))
    | ~ v5_orders_2(k3_yellow_1(sK0))
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | v1_xboole_0(sK1)
    | ~ v13_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ v3_orders_2(k3_yellow_1(sK0))
    | k1_xboole_0 != sK3(k3_yellow_1(sK0),sK1)
    | v2_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ spl4_1 ),
    inference(resolution,[],[f94,f108])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(u1_struct_0(X0))))
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v13_waybel_0(X1,X0)
      | ~ v3_orders_2(X0)
      | k1_xboole_0 != sK3(X0,X1)
      | v2_waybel_0(X1,X0) ) ),
    inference(definition_unfolding,[],[f78,f88])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 != sK3(X0,X1)
      | v2_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f251,plain,(
    spl4_22 ),
    inference(avatar_contradiction_clause,[],[f250])).

fof(f250,plain,
    ( $false
    | spl4_22 ),
    inference(resolution,[],[f230,f62])).

fof(f62,plain,(
    ! [X0] : v3_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f230,plain,
    ( ~ v3_orders_2(k3_yellow_1(sK0))
    | spl4_22 ),
    inference(avatar_component_clause,[],[f228])).

fof(f247,plain,
    ( spl4_4
    | spl4_21
    | ~ spl4_22
    | ~ spl4_2
    | spl4_3
    | ~ spl4_23
    | ~ spl4_24
    | ~ spl4_25
    | ~ spl4_26
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f222,f106,f244,f240,f236,f232,f116,f111,f228,f224,f121])).

fof(f222,plain,
    ( ~ v4_orders_2(k3_yellow_1(sK0))
    | ~ v5_orders_2(k3_yellow_1(sK0))
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | v1_xboole_0(sK1)
    | ~ v13_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ v3_orders_2(k3_yellow_1(sK0))
    | v1_finset_1(sK3(k3_yellow_1(sK0),sK1))
    | v2_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ spl4_1 ),
    inference(resolution,[],[f96,f108])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(u1_struct_0(X0))))
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v13_waybel_0(X1,X0)
      | ~ v3_orders_2(X0)
      | v1_finset_1(sK3(X0,X1))
      | v2_waybel_0(X1,X0) ) ),
    inference(definition_unfolding,[],[f76,f88])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_finset_1(sK3(X0,X1))
      | v2_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f181,plain,
    ( spl4_13
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f176,f106,f178])).

fof(f176,plain,
    ( r1_tarski(sK1,u1_struct_0(k3_yellow_1(sK0)))
    | ~ spl4_1 ),
    inference(resolution,[],[f102,f108])).

fof(f164,plain,
    ( spl4_12
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f159,f155,f149,f161])).

fof(f149,plain,
    ( spl4_10
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f155,plain,
    ( spl4_11
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f159,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(backward_demodulation,[],[f151,f157])).

fof(f157,plain,
    ( k1_xboole_0 = o_0_0_xboole_0
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f155])).

fof(f151,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f149])).

fof(f158,plain,
    ( spl4_11
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f153,f149,f155])).

fof(f153,plain,
    ( k1_xboole_0 = o_0_0_xboole_0
    | ~ spl4_10 ),
    inference(resolution,[],[f73,f151])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(f152,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f57,f149])).

fof(f57,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f147,plain,
    ( ~ spl4_4
    | spl4_9 ),
    inference(avatar_split_clause,[],[f49,f144,f121])).

fof(f49,plain,
    ( v1_finset_1(sK2)
    | ~ v2_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ? [X0,X1] :
      ( ( v2_waybel_0(X1,k3_yellow_1(X0))
      <~> ! [X2] :
            ( r2_hidden(k8_setfam_1(X0,X2),X1)
            | ~ r1_tarski(X2,X1)
            | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
            | ~ v1_finset_1(X2) ) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      & v13_waybel_0(X1,k3_yellow_1(X0))
      & ~ v1_xboole_0(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0,X1] :
      ( ( v2_waybel_0(X1,k3_yellow_1(X0))
      <~> ! [X2] :
            ( r2_hidden(k8_setfam_1(X0,X2),X1)
            | ~ r1_tarski(X2,X1)
            | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
            | ~ v1_finset_1(X2) ) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      & v13_waybel_0(X1,k3_yellow_1(X0))
      & ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          & v13_waybel_0(X1,k3_yellow_1(X0))
          & ~ v1_xboole_0(X1) )
       => ( v2_waybel_0(X1,k3_yellow_1(X0))
        <=> ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
                & v1_finset_1(X2) )
             => ( r1_tarski(X2,X1)
               => r2_hidden(k8_setfam_1(X0,X2),X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
        & v13_waybel_0(X1,k3_yellow_1(X0))
        & ~ v1_xboole_0(X1) )
     => ( v2_waybel_0(X1,k3_yellow_1(X0))
      <=> ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
              & v1_finset_1(X2) )
           => ( r1_tarski(X2,X1)
             => r2_hidden(k8_setfam_1(X0,X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_waybel_7)).

fof(f142,plain,
    ( ~ spl4_4
    | spl4_8 ),
    inference(avatar_split_clause,[],[f91,f139,f121])).

fof(f91,plain,
    ( m1_subset_1(sK2,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(sK0)))))
    | ~ v2_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(definition_unfolding,[],[f50,f88,f88])).

fof(f50,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ v2_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f30])).

fof(f137,plain,
    ( ~ spl4_4
    | spl4_7 ),
    inference(avatar_split_clause,[],[f51,f134,f121])).

fof(f51,plain,
    ( r1_tarski(sK2,sK1)
    | ~ v2_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f30])).

fof(f132,plain,
    ( ~ spl4_4
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f52,f129,f121])).

fof(f52,plain,
    ( ~ r2_hidden(k8_setfam_1(sK0,sK2),sK1)
    | ~ v2_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f30])).

fof(f127,plain,
    ( spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f90,f125,f121])).

fof(f90,plain,(
    ! [X2] :
      ( ~ v1_finset_1(X2)
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(sK0)))))
      | ~ r1_tarski(X2,sK1)
      | r2_hidden(k8_setfam_1(sK0,X2),sK1)
      | v2_waybel_0(sK1,k3_yellow_1(sK0)) ) ),
    inference(definition_unfolding,[],[f53,f88,f88])).

fof(f53,plain,(
    ! [X2] :
      ( ~ v1_finset_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | ~ r1_tarski(X2,sK1)
      | r2_hidden(k8_setfam_1(sK0,X2),sK1)
      | v2_waybel_0(sK1,k3_yellow_1(sK0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f119,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f54,f116])).

fof(f54,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f114,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f55,f111])).

fof(f55,plain,(
    v13_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f30])).

fof(f109,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f89,f106])).

fof(f89,plain,(
    m1_subset_1(sK1,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(sK0))))) ),
    inference(definition_unfolding,[],[f56,f88])).

fof(f56,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0)))) ),
    inference(cnf_transformation,[],[f30])).

%------------------------------------------------------------------------------
