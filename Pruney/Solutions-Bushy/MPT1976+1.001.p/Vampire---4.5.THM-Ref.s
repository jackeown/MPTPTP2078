%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1976+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:00 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  185 ( 833 expanded)
%              Number of leaves         :   37 ( 282 expanded)
%              Depth                    :   22
%              Number of atoms          :  990 (3792 expanded)
%              Number of equality atoms :   32 ( 374 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f257,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f104,f108,f112,f117,f121,f125,f129,f133,f150,f187,f200,f204,f208,f219,f228,f230,f232,f234,f236,f238,f249,f256])).

% (21916)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
fof(f256,plain,
    ( spl4_3
    | ~ spl4_4
    | spl4_2
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f254,f247,f102,f110,f106])).

fof(f106,plain,
    ( spl4_3
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f110,plain,
    ( spl4_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f102,plain,
    ( spl4_2
  <=> r2_hidden(k6_subset_1(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f247,plain,
    ( spl4_21
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | r2_hidden(k7_waybel_1(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))),X0),sK1)
        | r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f254,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | r2_hidden(sK2,sK1)
    | spl4_2
    | ~ spl4_21 ),
    inference(resolution,[],[f253,f103])).

fof(f103,plain,
    ( ~ r2_hidden(k6_subset_1(sK0,sK2),sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f102])).

fof(f253,plain,
    ( ! [X0] :
        ( r2_hidden(k6_subset_1(sK0,X0),sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | r2_hidden(X0,sK1) )
    | ~ spl4_21 ),
    inference(duplicate_literal_removal,[],[f252])).

fof(f252,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | r2_hidden(k6_subset_1(sK0,X0),sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | r2_hidden(X0,sK1) )
    | ~ spl4_21 ),
    inference(forward_demodulation,[],[f251,f144])).

fof(f144,plain,(
    ! [X0] : u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))) = X0 ),
    inference(equality_resolution,[],[f141])).

fof(f141,plain,(
    ! [X0,X1] :
      ( g1_orders_2(X0,k1_yellow_1(X0)) != g1_orders_2(X1,k1_yellow_1(X1))
      | u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))) = X1 ) ),
    inference(global_subsumption,[],[f94,f140])).

fof(f140,plain,(
    ! [X0,X1] :
      ( u1_struct_0(g1_orders_2(X0,k1_yellow_1(X0))) = X1
      | ~ v1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))
      | g1_orders_2(X0,k1_yellow_1(X0)) != g1_orders_2(X1,k1_yellow_1(X1)) ) ),
    inference(resolution,[],[f136,f93])).

fof(f93,plain,(
    ! [X0] : l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(definition_unfolding,[],[f62,f54])).

fof(f54,plain,(
    ! [X0] : k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_yellow_1(X0) = g1_orders_2(X0,k1_yellow_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_yellow_1)).

fof(f62,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f136,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | u1_struct_0(X0) = X1
      | ~ v1_orders_2(X0)
      | g1_orders_2(X1,k1_yellow_1(X1)) != X0 ) ),
    inference(superposition,[],[f134,f65])).

fof(f65,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_orders_2(X0)
       => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

% (21918)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
fof(f134,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(X0,k1_yellow_1(X0)) != g1_orders_2(X1,X2)
      | X0 = X1 ) ),
    inference(resolution,[],[f77,f60])).

fof(f60,plain,(
    ! [X0] : m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] : m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_relat_2(k1_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v4_relat_2(k1_yellow_1(X0))
      & v1_relat_2(k1_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v8_relat_2(k1_yellow_1(X0))
      & v4_relat_2(k1_yellow_1(X0))
      & v1_relat_2(k1_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( m1_subset_1(k1_yellow_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k1_yellow_1(X0),X0)
      & v8_relat_2(k1_yellow_1(X0))
      & v4_relat_2(k1_yellow_1(X0))
      & v1_relat_2(k1_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_1)).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(f94,plain,(
    ! [X0] : v1_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ),
    inference(definition_unfolding,[],[f61,f54])).

fof(f61,plain,(
    ! [X0] : v1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f251,plain,
    ( ! [X0] :
        ( r2_hidden(k6_subset_1(sK0,X0),sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))) )
    | ~ spl4_21 ),
    inference(superposition,[],[f248,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k6_subset_1(X0,X1) = k7_waybel_1(g1_orders_2(k1_zfmisc_1(X0),k1_yellow_1(k1_zfmisc_1(X0))),X1)
      | ~ m1_subset_1(X1,u1_struct_0(g1_orders_2(k1_zfmisc_1(X0),k1_yellow_1(k1_zfmisc_1(X0))))) ) ),
    inference(definition_unfolding,[],[f76,f80,f80])).

fof(f80,plain,(
    ! [X0] : k3_yellow_1(X0) = g1_orders_2(k1_zfmisc_1(X0),k1_yellow_1(k1_zfmisc_1(X0))) ),
    inference(definition_unfolding,[],[f53,f54,f52])).

fof(f52,plain,(
    ! [X0] : k9_setfam_1(X0) = k1_zfmisc_1(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k9_setfam_1(X0) = k1_zfmisc_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(f53,plain,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).

fof(f76,plain,(
    ! [X0,X1] :
      ( k7_waybel_1(k3_yellow_1(X0),X1) = k6_subset_1(X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k7_waybel_1(k3_yellow_1(X0),X1) = k6_subset_1(X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
     => k7_waybel_1(k3_yellow_1(X0),X1) = k6_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_waybel_7)).

fof(f248,plain,
    ( ! [X0] :
        ( r2_hidden(k7_waybel_1(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))),X0),sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | r2_hidden(X0,sK1) )
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f247])).

fof(f249,plain,
    ( ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13
    | ~ spl4_17
    | ~ spl4_19
    | ~ spl4_20
    | ~ spl4_15
    | spl4_9
    | ~ spl4_8
    | ~ spl4_7
    | spl4_21
    | ~ spl4_10
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f245,f99,f148,f247,f123,f127,f131,f192,f226,f223,f198,f180,f177,f174])).

fof(f174,plain,
    ( spl4_11
  <=> v3_orders_2(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f177,plain,
    ( spl4_12
  <=> v4_orders_2(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f180,plain,
    ( spl4_13
  <=> v5_orders_2(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f198,plain,
    ( spl4_17
  <=> v11_waybel_1(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f223,plain,
    ( spl4_19
  <=> v1_lattice3(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f226,plain,
    ( spl4_20
  <=> v2_lattice3(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

% (21916)Refutation not found, incomplete strategy% (21916)------------------------------
% (21916)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (21916)Termination reason: Refutation not found, incomplete strategy

% (21916)Memory used [KB]: 10746
% (21916)Time elapsed: 0.137 s
% (21916)------------------------------
% (21916)------------------------------
fof(f192,plain,
    ( spl4_15
  <=> l1_orders_2(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f131,plain,
    ( spl4_9
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f127,plain,
    ( spl4_8
  <=> v2_waybel_0(sK1,g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f123,plain,
    ( spl4_7
  <=> v13_waybel_0(sK1,g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f148,plain,
    ( spl4_10
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f99,plain,
    ( spl4_1
  <=> v2_waybel_7(sK1,g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f245,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | r2_hidden(X0,sK1)
        | r2_hidden(k7_waybel_1(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))),X0),sK1)
        | ~ v13_waybel_0(sK1,g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
        | ~ v2_waybel_0(sK1,g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
        | v1_xboole_0(sK1)
        | ~ l1_orders_2(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
        | ~ v2_lattice3(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
        | ~ v1_lattice3(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
        | ~ v11_waybel_1(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
        | ~ v5_orders_2(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
        | ~ v4_orders_2(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
        | ~ v3_orders_2(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0)))) )
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f244,f144])).

fof(f244,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | r2_hidden(X0,sK1)
        | r2_hidden(k7_waybel_1(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))),X0),sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))))
        | ~ v13_waybel_0(sK1,g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
        | ~ v2_waybel_0(sK1,g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
        | v1_xboole_0(sK1)
        | ~ l1_orders_2(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
        | ~ v2_lattice3(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
        | ~ v1_lattice3(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
        | ~ v11_waybel_1(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
        | ~ v5_orders_2(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
        | ~ v4_orders_2(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
        | ~ v3_orders_2(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0)))) )
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f243,f144])).

fof(f243,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0)))))
        | r2_hidden(k7_waybel_1(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))),X0),sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))))
        | ~ v13_waybel_0(sK1,g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
        | ~ v2_waybel_0(sK1,g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
        | v1_xboole_0(sK1)
        | ~ l1_orders_2(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
        | ~ v2_lattice3(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
        | ~ v1_lattice3(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
        | ~ v11_waybel_1(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
        | ~ v5_orders_2(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
        | ~ v4_orders_2(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
        | ~ v3_orders_2(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0)))) )
    | ~ spl4_1 ),
    inference(resolution,[],[f113,f72])).

fof(f72,plain,(
    ! [X0,X3,X1] :
      ( ~ v2_waybel_7(X1,X0)
      | r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r2_hidden(k7_waybel_1(X0,X3),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_7(X1,X0)
              | ( ~ r2_hidden(k7_waybel_1(X0,sK3(X0,X1)),X1)
                & ~ r2_hidden(sK3(X0,X1),X1)
                & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( r2_hidden(k7_waybel_1(X0,X3),X1)
                  | r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ v2_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f41,f42])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k7_waybel_1(X0,X2),X1)
          & ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ~ r2_hidden(k7_waybel_1(X0,sK3(X0,X1)),X1)
        & ~ r2_hidden(sK3(X0,X1),X1)
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_7(X1,X0)
              | ? [X2] :
                  ( ~ r2_hidden(k7_waybel_1(X0,X2),X1)
                  & ~ r2_hidden(X2,X1)
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( r2_hidden(k7_waybel_1(X0,X3),X1)
                  | r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ v2_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_7(X1,X0)
              | ? [X2] :
                  ( ~ r2_hidden(k7_waybel_1(X0,X2),X1)
                  & ~ r2_hidden(X2,X1)
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( r2_hidden(k7_waybel_1(X0,X2),X1)
                  | r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v2_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_7(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k7_waybel_1(X0,X2),X1)
                | r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_7(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k7_waybel_1(X0,X2),X1)
                | r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v11_waybel_1(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v2_waybel_7(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(k7_waybel_1(X0,X2),X1)
                  | r2_hidden(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_waybel_7)).

fof(f113,plain,
    ( v2_waybel_7(sK1,g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f99])).

fof(f238,plain,
    ( ~ spl4_15
    | spl4_16
    | ~ spl4_17
    | spl4_20 ),
    inference(avatar_split_clause,[],[f237,f226,f198,f195,f192])).

fof(f195,plain,
    ( spl4_16
  <=> v2_struct_0(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f237,plain,
    ( ~ v11_waybel_1(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
    | v2_struct_0(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
    | ~ l1_orders_2(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
    | spl4_20 ),
    inference(resolution,[],[f227,f71])).

fof(f71,plain,(
    ! [X0] :
      ( v2_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(pure_predicate_removal,[],[f21])).

fof(f21,plain,(
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
    inference(pure_predicate_removal,[],[f20])).

fof(f20,plain,(
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
    inference(pure_predicate_removal,[],[f2])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc8_waybel_1)).

fof(f227,plain,
    ( ~ v2_lattice3(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
    | spl4_20 ),
    inference(avatar_component_clause,[],[f226])).

fof(f236,plain,(
    ~ spl4_16 ),
    inference(avatar_contradiction_clause,[],[f235])).

fof(f235,plain,
    ( $false
    | ~ spl4_16 ),
    inference(resolution,[],[f196,f92])).

fof(f92,plain,(
    ! [X0] : ~ v2_struct_0(g1_orders_2(k1_zfmisc_1(X0),k1_yellow_1(k1_zfmisc_1(X0)))) ),
    inference(definition_unfolding,[],[f55,f80])).

fof(f55,plain,(
    ! [X0] : ~ v2_struct_0(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v5_orders_2(k3_yellow_1(X0))
      & v4_orders_2(k3_yellow_1(X0))
      & v3_orders_2(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0))
      & ~ v2_struct_0(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_yellow_1)).

fof(f196,plain,
    ( v2_struct_0(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f195])).

fof(f234,plain,
    ( ~ spl4_15
    | spl4_16
    | ~ spl4_17
    | spl4_19 ),
    inference(avatar_split_clause,[],[f233,f223,f198,f195,f192])).

fof(f233,plain,
    ( ~ v11_waybel_1(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
    | v2_struct_0(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
    | ~ l1_orders_2(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
    | spl4_19 ),
    inference(resolution,[],[f224,f70])).

fof(f70,plain,(
    ! [X0] :
      ( v1_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f224,plain,
    ( ~ v1_lattice3(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
    | spl4_19 ),
    inference(avatar_component_clause,[],[f223])).

fof(f232,plain,(
    spl4_17 ),
    inference(avatar_contradiction_clause,[],[f231])).

fof(f231,plain,
    ( $false
    | spl4_17 ),
    inference(resolution,[],[f199,f95])).

fof(f95,plain,(
    ! [X0] : v11_waybel_1(g1_orders_2(k1_zfmisc_1(X0),k1_yellow_1(k1_zfmisc_1(X0)))) ),
    inference(definition_unfolding,[],[f64,f80])).

fof(f64,plain,(
    ! [X0] : v11_waybel_1(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v11_waybel_1(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_waybel_7)).

fof(f199,plain,
    ( ~ v11_waybel_1(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
    | spl4_17 ),
    inference(avatar_component_clause,[],[f198])).

fof(f230,plain,(
    spl4_15 ),
    inference(avatar_contradiction_clause,[],[f229])).

fof(f229,plain,
    ( $false
    | spl4_15 ),
    inference(resolution,[],[f193,f93])).

fof(f193,plain,
    ( ~ l1_orders_2(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
    | spl4_15 ),
    inference(avatar_component_clause,[],[f192])).

fof(f228,plain,
    ( ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13
    | ~ spl4_17
    | ~ spl4_19
    | ~ spl4_20
    | ~ spl4_15
    | spl4_9
    | ~ spl4_8
    | ~ spl4_7
    | spl4_1
    | ~ spl4_10
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f221,f215,f148,f99,f123,f127,f131,f192,f226,f223,f198,f180,f177,f174])).

% (21905)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
fof(f215,plain,
    ( spl4_18
  <=> r2_hidden(sK3(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f221,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | v2_waybel_7(sK1,g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
    | ~ v13_waybel_0(sK1,g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
    | ~ v2_waybel_0(sK1,g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
    | ~ v2_lattice3(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
    | ~ v1_lattice3(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
    | ~ v11_waybel_1(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
    | ~ v5_orders_2(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
    | ~ v4_orders_2(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
    | ~ v3_orders_2(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
    | ~ spl4_18 ),
    inference(forward_demodulation,[],[f220,f144])).

fof(f220,plain,
    ( v2_waybel_7(sK1,g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))))
    | ~ v13_waybel_0(sK1,g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
    | ~ v2_waybel_0(sK1,g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
    | ~ v2_lattice3(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
    | ~ v1_lattice3(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
    | ~ v11_waybel_1(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
    | ~ v5_orders_2(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
    | ~ v4_orders_2(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
    | ~ v3_orders_2(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
    | ~ spl4_18 ),
    inference(resolution,[],[f216,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | v2_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f216,plain,
    ( r2_hidden(sK3(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))),sK1),sK1)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f215])).

fof(f219,plain,
    ( spl4_18
    | ~ spl4_14
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13
    | ~ spl4_8
    | spl4_1
    | ~ spl4_7
    | spl4_9
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f213,f115,f131,f123,f99,f127,f180,f177,f174,f148,f184,f215])).

fof(f184,plain,
    ( spl4_14
  <=> m1_subset_1(sK3(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))),sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f115,plain,
    ( spl4_5
  <=> ! [X3] :
        ( r2_hidden(k6_subset_1(sK0,X3),sK1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(sK0))
        | r2_hidden(X3,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f213,plain,
    ( v1_xboole_0(sK1)
    | ~ v13_waybel_0(sK1,g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
    | v2_waybel_7(sK1,g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
    | ~ v2_waybel_0(sK1,g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
    | ~ v5_orders_2(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
    | ~ v4_orders_2(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
    | ~ v3_orders_2(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK3(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))),sK1),k1_zfmisc_1(sK0))
    | r2_hidden(sK3(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))),sK1),sK1)
    | ~ spl4_5 ),
    inference(resolution,[],[f212,f116])).

fof(f116,plain,
    ( ! [X3] :
        ( r2_hidden(k6_subset_1(sK0,X3),sK1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(sK0))
        | r2_hidden(X3,sK1) )
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f115])).

fof(f212,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k6_subset_1(X0,sK3(g1_orders_2(k1_zfmisc_1(X0),k1_yellow_1(k1_zfmisc_1(X0))),X1)),X1)
      | v1_xboole_0(X1)
      | ~ v13_waybel_0(X1,g1_orders_2(k1_zfmisc_1(X0),k1_yellow_1(k1_zfmisc_1(X0))))
      | v2_waybel_7(X1,g1_orders_2(k1_zfmisc_1(X0),k1_yellow_1(k1_zfmisc_1(X0))))
      | ~ v2_waybel_0(X1,g1_orders_2(k1_zfmisc_1(X0),k1_yellow_1(k1_zfmisc_1(X0))))
      | ~ v5_orders_2(g1_orders_2(k1_zfmisc_1(X0),k1_yellow_1(k1_zfmisc_1(X0))))
      | ~ v4_orders_2(g1_orders_2(k1_zfmisc_1(X0),k1_yellow_1(k1_zfmisc_1(X0))))
      | ~ v3_orders_2(g1_orders_2(k1_zfmisc_1(X0),k1_yellow_1(k1_zfmisc_1(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(global_subsumption,[],[f170,f211])).

fof(f211,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK3(g1_orders_2(k1_zfmisc_1(X0),k1_yellow_1(k1_zfmisc_1(X0))),X1),k1_zfmisc_1(X0))
      | ~ r2_hidden(k6_subset_1(X0,sK3(g1_orders_2(k1_zfmisc_1(X0),k1_yellow_1(k1_zfmisc_1(X0))),X1)),X1)
      | v1_xboole_0(X1)
      | ~ v13_waybel_0(X1,g1_orders_2(k1_zfmisc_1(X0),k1_yellow_1(k1_zfmisc_1(X0))))
      | v2_waybel_7(X1,g1_orders_2(k1_zfmisc_1(X0),k1_yellow_1(k1_zfmisc_1(X0))))
      | ~ v2_waybel_0(X1,g1_orders_2(k1_zfmisc_1(X0),k1_yellow_1(k1_zfmisc_1(X0))))
      | ~ v5_orders_2(g1_orders_2(k1_zfmisc_1(X0),k1_yellow_1(k1_zfmisc_1(X0))))
      | ~ v4_orders_2(g1_orders_2(k1_zfmisc_1(X0),k1_yellow_1(k1_zfmisc_1(X0))))
      | ~ v3_orders_2(g1_orders_2(k1_zfmisc_1(X0),k1_yellow_1(k1_zfmisc_1(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(forward_demodulation,[],[f210,f144])).

fof(f210,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k6_subset_1(X0,sK3(g1_orders_2(k1_zfmisc_1(X0),k1_yellow_1(k1_zfmisc_1(X0))),X1)),X1)
      | v1_xboole_0(X1)
      | ~ v13_waybel_0(X1,g1_orders_2(k1_zfmisc_1(X0),k1_yellow_1(k1_zfmisc_1(X0))))
      | v2_waybel_7(X1,g1_orders_2(k1_zfmisc_1(X0),k1_yellow_1(k1_zfmisc_1(X0))))
      | ~ v2_waybel_0(X1,g1_orders_2(k1_zfmisc_1(X0),k1_yellow_1(k1_zfmisc_1(X0))))
      | ~ v5_orders_2(g1_orders_2(k1_zfmisc_1(X0),k1_yellow_1(k1_zfmisc_1(X0))))
      | ~ v4_orders_2(g1_orders_2(k1_zfmisc_1(X0),k1_yellow_1(k1_zfmisc_1(X0))))
      | ~ v3_orders_2(g1_orders_2(k1_zfmisc_1(X0),k1_yellow_1(k1_zfmisc_1(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(sK3(g1_orders_2(k1_zfmisc_1(X0),k1_yellow_1(k1_zfmisc_1(X0))),X1),u1_struct_0(g1_orders_2(k1_zfmisc_1(X0),k1_yellow_1(k1_zfmisc_1(X0))))) ) ),
    inference(superposition,[],[f209,f97])).

fof(f209,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k7_waybel_1(g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))),sK3(g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))),X0)),X0)
      | v1_xboole_0(X0)
      | ~ v13_waybel_0(X0,g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))))
      | v2_waybel_7(X0,g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))))
      | ~ v2_waybel_0(X0,g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))))
      | ~ v5_orders_2(g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))))
      | ~ v4_orders_2(g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))))
      | ~ v3_orders_2(g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) ) ),
    inference(resolution,[],[f169,f93])).

fof(f169,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))))
      | ~ v2_waybel_0(X0,g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))))
      | v1_xboole_0(X0)
      | ~ v13_waybel_0(X0,g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))))
      | v2_waybel_7(X0,g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))))
      | ~ r2_hidden(k7_waybel_1(g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))),sK3(g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))),X0)),X0)
      | ~ v5_orders_2(g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))))
      | ~ v4_orders_2(g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))))
      | ~ v3_orders_2(g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) ) ),
    inference(resolution,[],[f162,f92])).

fof(f162,plain,(
    ! [X0,X1] :
      ( v2_struct_0(g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))))
      | ~ v13_waybel_0(X0,g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))))
      | ~ v2_waybel_0(X0,g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))))
      | v1_xboole_0(X0)
      | ~ l1_orders_2(g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))))
      | v2_waybel_7(X0,g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))))
      | ~ r2_hidden(k7_waybel_1(g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))),sK3(g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))),X0)),X0)
      | ~ v5_orders_2(g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))))
      | ~ v4_orders_2(g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))))
      | ~ v3_orders_2(g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) ) ),
    inference(forward_demodulation,[],[f161,f144])).

fof(f161,plain,(
    ! [X0,X1] :
      ( ~ v13_waybel_0(X0,g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))))
      | ~ v2_waybel_0(X0,g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))))
      | v1_xboole_0(X0)
      | ~ l1_orders_2(g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))))
      | v2_waybel_7(X0,g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))))
      | ~ r2_hidden(k7_waybel_1(g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))),sK3(g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))),X0)),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))))))
      | ~ v5_orders_2(g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))))
      | ~ v4_orders_2(g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))))
      | ~ v3_orders_2(g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))))
      | v2_struct_0(g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1)))) ) ),
    inference(resolution,[],[f160,f95])).

fof(f160,plain,(
    ! [X0,X1] :
      ( ~ v11_waybel_1(X1)
      | ~ v13_waybel_0(X0,X1)
      | ~ v2_waybel_0(X0,X1)
      | v1_xboole_0(X0)
      | ~ l1_orders_2(X1)
      | v2_waybel_7(X0,X1)
      | ~ r2_hidden(k7_waybel_1(X1,sK3(X1,X0)),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f159])).

fof(f159,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v13_waybel_0(X0,X1)
      | ~ v2_waybel_0(X0,X1)
      | v1_xboole_0(X0)
      | ~ l1_orders_2(X1)
      | v2_waybel_7(X0,X1)
      | ~ r2_hidden(k7_waybel_1(X1,sK3(X1,X0)),X0)
      | ~ v11_waybel_1(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1)
      | ~ v11_waybel_1(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X1) ) ),
    inference(resolution,[],[f158,f70])).

fof(f158,plain,(
    ! [X0,X1] :
      ( ~ v1_lattice3(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | v2_waybel_7(X1,X0)
      | ~ r2_hidden(k7_waybel_1(X0,sK3(X0,X1)),X1)
      | ~ v11_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f157])).

fof(f157,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k7_waybel_1(X0,sK3(X0,X1)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | v2_waybel_7(X1,X0)
      | ~ v1_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f75,f71])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ v2_lattice3(X0)
      | ~ r2_hidden(k7_waybel_1(X0,sK3(X0,X1)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | v2_waybel_7(X1,X0)
      | ~ v1_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f170,plain,(
    ! [X0,X1] :
      ( ~ v13_waybel_0(X0,g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))))
      | ~ v2_waybel_0(X0,g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))))
      | m1_subset_1(sK3(g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))),X0),k1_zfmisc_1(X1))
      | v2_waybel_7(X0,g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ v5_orders_2(g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))))
      | ~ v4_orders_2(g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))))
      | ~ v3_orders_2(g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f168,f93])).

fof(f168,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))))
      | v1_xboole_0(X0)
      | ~ v2_waybel_0(X0,g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))))
      | m1_subset_1(sK3(g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))),X0),k1_zfmisc_1(X1))
      | v2_waybel_7(X0,g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ v5_orders_2(g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))))
      | ~ v4_orders_2(g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))))
      | ~ v3_orders_2(g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))))
      | ~ v13_waybel_0(X0,g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1)))) ) ),
    inference(resolution,[],[f167,f92])).

fof(f167,plain,(
    ! [X0,X1] :
      ( v2_struct_0(g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))))
      | ~ v2_waybel_0(X0,g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))))
      | v1_xboole_0(X0)
      | ~ l1_orders_2(g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))))
      | m1_subset_1(sK3(g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))),X0),k1_zfmisc_1(X1))
      | v2_waybel_7(X0,g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ v5_orders_2(g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))))
      | ~ v4_orders_2(g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))))
      | ~ v3_orders_2(g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1))))
      | ~ v13_waybel_0(X0,g1_orders_2(k1_zfmisc_1(X1),k1_yellow_1(k1_zfmisc_1(X1)))) ) ),
    inference(resolution,[],[f166,f95])).

fof(f166,plain,(
    ! [X0,X1] :
      ( ~ v11_waybel_1(g1_orders_2(X1,k1_yellow_1(X1)))
      | ~ v13_waybel_0(X0,g1_orders_2(X1,k1_yellow_1(X1)))
      | ~ v2_waybel_0(X0,g1_orders_2(X1,k1_yellow_1(X1)))
      | v1_xboole_0(X0)
      | ~ l1_orders_2(g1_orders_2(X1,k1_yellow_1(X1)))
      | m1_subset_1(sK3(g1_orders_2(X1,k1_yellow_1(X1)),X0),X1)
      | v2_waybel_7(X0,g1_orders_2(X1,k1_yellow_1(X1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ v5_orders_2(g1_orders_2(X1,k1_yellow_1(X1)))
      | ~ v4_orders_2(g1_orders_2(X1,k1_yellow_1(X1)))
      | ~ v3_orders_2(g1_orders_2(X1,k1_yellow_1(X1)))
      | v2_struct_0(g1_orders_2(X1,k1_yellow_1(X1))) ) ),
    inference(duplicate_literal_removal,[],[f165])).

fof(f165,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ v13_waybel_0(X0,g1_orders_2(X1,k1_yellow_1(X1)))
      | ~ v2_waybel_0(X0,g1_orders_2(X1,k1_yellow_1(X1)))
      | v1_xboole_0(X0)
      | ~ l1_orders_2(g1_orders_2(X1,k1_yellow_1(X1)))
      | m1_subset_1(sK3(g1_orders_2(X1,k1_yellow_1(X1)),X0),X1)
      | v2_waybel_7(X0,g1_orders_2(X1,k1_yellow_1(X1)))
      | ~ v11_waybel_1(g1_orders_2(X1,k1_yellow_1(X1)))
      | ~ v5_orders_2(g1_orders_2(X1,k1_yellow_1(X1)))
      | ~ v4_orders_2(g1_orders_2(X1,k1_yellow_1(X1)))
      | ~ v3_orders_2(g1_orders_2(X1,k1_yellow_1(X1)))
      | v2_struct_0(g1_orders_2(X1,k1_yellow_1(X1)))
      | ~ v11_waybel_1(g1_orders_2(X1,k1_yellow_1(X1)))
      | v2_struct_0(g1_orders_2(X1,k1_yellow_1(X1)))
      | ~ l1_orders_2(g1_orders_2(X1,k1_yellow_1(X1))) ) ),
    inference(resolution,[],[f164,f70])).

fof(f164,plain,(
    ! [X0,X1] :
      ( ~ v1_lattice3(g1_orders_2(X1,k1_yellow_1(X1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ v13_waybel_0(X0,g1_orders_2(X1,k1_yellow_1(X1)))
      | ~ v2_waybel_0(X0,g1_orders_2(X1,k1_yellow_1(X1)))
      | v1_xboole_0(X0)
      | ~ l1_orders_2(g1_orders_2(X1,k1_yellow_1(X1)))
      | m1_subset_1(sK3(g1_orders_2(X1,k1_yellow_1(X1)),X0),X1)
      | v2_waybel_7(X0,g1_orders_2(X1,k1_yellow_1(X1)))
      | ~ v11_waybel_1(g1_orders_2(X1,k1_yellow_1(X1)))
      | ~ v5_orders_2(g1_orders_2(X1,k1_yellow_1(X1)))
      | ~ v4_orders_2(g1_orders_2(X1,k1_yellow_1(X1)))
      | ~ v3_orders_2(g1_orders_2(X1,k1_yellow_1(X1)))
      | v2_struct_0(g1_orders_2(X1,k1_yellow_1(X1))) ) ),
    inference(duplicate_literal_removal,[],[f163])).

fof(f163,plain,(
    ! [X0,X1] :
      ( v2_waybel_7(X0,g1_orders_2(X1,k1_yellow_1(X1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ v13_waybel_0(X0,g1_orders_2(X1,k1_yellow_1(X1)))
      | ~ v2_waybel_0(X0,g1_orders_2(X1,k1_yellow_1(X1)))
      | v1_xboole_0(X0)
      | ~ l1_orders_2(g1_orders_2(X1,k1_yellow_1(X1)))
      | m1_subset_1(sK3(g1_orders_2(X1,k1_yellow_1(X1)),X0),X1)
      | ~ v1_lattice3(g1_orders_2(X1,k1_yellow_1(X1)))
      | ~ v11_waybel_1(g1_orders_2(X1,k1_yellow_1(X1)))
      | ~ v5_orders_2(g1_orders_2(X1,k1_yellow_1(X1)))
      | ~ v4_orders_2(g1_orders_2(X1,k1_yellow_1(X1)))
      | ~ v3_orders_2(g1_orders_2(X1,k1_yellow_1(X1)))
      | ~ v11_waybel_1(g1_orders_2(X1,k1_yellow_1(X1)))
      | v2_struct_0(g1_orders_2(X1,k1_yellow_1(X1)))
      | ~ l1_orders_2(g1_orders_2(X1,k1_yellow_1(X1))) ) ),
    inference(resolution,[],[f156,f71])).

fof(f156,plain,(
    ! [X0,X1] :
      ( ~ v2_lattice3(g1_orders_2(X0,k1_yellow_1(X0)))
      | v2_waybel_7(X1,g1_orders_2(X0,k1_yellow_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v13_waybel_0(X1,g1_orders_2(X0,k1_yellow_1(X0)))
      | ~ v2_waybel_0(X1,g1_orders_2(X0,k1_yellow_1(X0)))
      | v1_xboole_0(X1)
      | ~ l1_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))
      | m1_subset_1(sK3(g1_orders_2(X0,k1_yellow_1(X0)),X1),X0)
      | ~ v1_lattice3(g1_orders_2(X0,k1_yellow_1(X0)))
      | ~ v11_waybel_1(g1_orders_2(X0,k1_yellow_1(X0)))
      | ~ v5_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))
      | ~ v4_orders_2(g1_orders_2(X0,k1_yellow_1(X0)))
      | ~ v3_orders_2(g1_orders_2(X0,k1_yellow_1(X0))) ) ),
    inference(superposition,[],[f73,f144])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | v2_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f208,plain,
    ( ~ spl4_15
    | spl4_16
    | ~ spl4_17
    | spl4_13 ),
    inference(avatar_split_clause,[],[f206,f180,f198,f195,f192])).

fof(f206,plain,
    ( ~ v11_waybel_1(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
    | v2_struct_0(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
    | ~ l1_orders_2(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
    | spl4_13 ),
    inference(resolution,[],[f181,f69])).

fof(f69,plain,(
    ! [X0] :
      ( v5_orders_2(X0)
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f181,plain,
    ( ~ v5_orders_2(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
    | spl4_13 ),
    inference(avatar_component_clause,[],[f180])).

fof(f204,plain,
    ( ~ spl4_15
    | spl4_16
    | ~ spl4_17
    | spl4_12 ),
    inference(avatar_split_clause,[],[f202,f177,f198,f195,f192])).

fof(f202,plain,
    ( ~ v11_waybel_1(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
    | v2_struct_0(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
    | ~ l1_orders_2(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
    | spl4_12 ),
    inference(resolution,[],[f178,f68])).

fof(f68,plain,(
    ! [X0] :
      ( v4_orders_2(X0)
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f178,plain,
    ( ~ v4_orders_2(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
    | spl4_12 ),
    inference(avatar_component_clause,[],[f177])).

fof(f200,plain,
    ( ~ spl4_15
    | spl4_16
    | ~ spl4_17
    | spl4_11 ),
    inference(avatar_split_clause,[],[f189,f174,f198,f195,f192])).

fof(f189,plain,
    ( ~ v11_waybel_1(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
    | v2_struct_0(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
    | ~ l1_orders_2(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
    | spl4_11 ),
    inference(resolution,[],[f175,f67])).

fof(f67,plain,(
    ! [X0] :
      ( v3_orders_2(X0)
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f175,plain,
    ( ~ v3_orders_2(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
    | spl4_11 ),
    inference(avatar_component_clause,[],[f174])).

fof(f187,plain,
    ( spl4_9
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13
    | ~ spl4_10
    | spl4_1
    | spl4_14
    | ~ spl4_8
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f171,f123,f127,f184,f99,f148,f180,f177,f174,f131])).

fof(f171,plain,
    ( ~ v2_waybel_0(sK1,g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
    | m1_subset_1(sK3(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))),sK1),k1_zfmisc_1(sK0))
    | v2_waybel_7(sK1,g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ v5_orders_2(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
    | ~ v4_orders_2(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
    | ~ v3_orders_2(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
    | v1_xboole_0(sK1)
    | ~ spl4_7 ),
    inference(resolution,[],[f170,f124])).

fof(f124,plain,
    ( v13_waybel_0(sK1,g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f123])).

fof(f150,plain,
    ( spl4_10
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f145,f119,f148])).

fof(f119,plain,
    ( spl4_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f145,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl4_6 ),
    inference(superposition,[],[f120,f144])).

fof(f120,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0))))))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f119])).

fof(f133,plain,(
    ~ spl4_9 ),
    inference(avatar_split_clause,[],[f44,f131])).

fof(f44,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ( ( ~ r2_hidden(k6_subset_1(sK0,sK2),sK1)
        & ~ r2_hidden(sK2,sK1)
        & m1_subset_1(sK2,k1_zfmisc_1(sK0)) )
      | ~ v2_waybel_7(sK1,k3_yellow_1(sK0)) )
    & ( ! [X3] :
          ( r2_hidden(k6_subset_1(sK0,X3),sK1)
          | r2_hidden(X3,sK1)
          | ~ m1_subset_1(X3,k1_zfmisc_1(sK0)) )
      | v2_waybel_7(sK1,k3_yellow_1(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    & v13_waybel_0(sK1,k3_yellow_1(sK0))
    & v2_waybel_0(sK1,k3_yellow_1(sK0))
    & ~ v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f38,f37])).

% (21912)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
fof(f37,plain,
    ( ? [X0,X1] :
        ( ( ? [X2] :
              ( ~ r2_hidden(k6_subset_1(X0,X2),X1)
              & ~ r2_hidden(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(X0)) )
          | ~ v2_waybel_7(X1,k3_yellow_1(X0)) )
        & ( ! [X3] :
              ( r2_hidden(k6_subset_1(X0,X3),X1)
              | r2_hidden(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
          | v2_waybel_7(X1,k3_yellow_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
        & v13_waybel_0(X1,k3_yellow_1(X0))
        & v2_waybel_0(X1,k3_yellow_1(X0))
        & ~ v1_xboole_0(X1) )
   => ( ( ? [X2] :
            ( ~ r2_hidden(k6_subset_1(sK0,X2),sK1)
            & ~ r2_hidden(X2,sK1)
            & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
        | ~ v2_waybel_7(sK1,k3_yellow_1(sK0)) )
      & ( ! [X3] :
            ( r2_hidden(k6_subset_1(sK0,X3),sK1)
            | r2_hidden(X3,sK1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(sK0)) )
        | v2_waybel_7(sK1,k3_yellow_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
      & v13_waybel_0(sK1,k3_yellow_1(sK0))
      & v2_waybel_0(sK1,k3_yellow_1(sK0))
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X2] :
        ( ~ r2_hidden(k6_subset_1(sK0,X2),sK1)
        & ~ r2_hidden(X2,sK1)
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ~ r2_hidden(k6_subset_1(sK0,sK2),sK1)
      & ~ r2_hidden(sK2,sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ? [X0,X1] :
      ( ( ? [X2] :
            ( ~ r2_hidden(k6_subset_1(X0,X2),X1)
            & ~ r2_hidden(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        | ~ v2_waybel_7(X1,k3_yellow_1(X0)) )
      & ( ! [X3] :
            ( r2_hidden(k6_subset_1(X0,X3),X1)
            | r2_hidden(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
        | v2_waybel_7(X1,k3_yellow_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      & v13_waybel_0(X1,k3_yellow_1(X0))
      & v2_waybel_0(X1,k3_yellow_1(X0))
      & ~ v1_xboole_0(X1) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ? [X0,X1] :
      ( ( ? [X2] :
            ( ~ r2_hidden(k6_subset_1(X0,X2),X1)
            & ~ r2_hidden(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        | ~ v2_waybel_7(X1,k3_yellow_1(X0)) )
      & ( ! [X2] :
            ( r2_hidden(k6_subset_1(X0,X2),X1)
            | r2_hidden(X2,X1)
            | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
        | v2_waybel_7(X1,k3_yellow_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      & v13_waybel_0(X1,k3_yellow_1(X0))
      & v2_waybel_0(X1,k3_yellow_1(X0))
      & ~ v1_xboole_0(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ? [X0,X1] :
      ( ( ? [X2] :
            ( ~ r2_hidden(k6_subset_1(X0,X2),X1)
            & ~ r2_hidden(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        | ~ v2_waybel_7(X1,k3_yellow_1(X0)) )
      & ( ! [X2] :
            ( r2_hidden(k6_subset_1(X0,X2),X1)
            | r2_hidden(X2,X1)
            | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
        | v2_waybel_7(X1,k3_yellow_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      & v13_waybel_0(X1,k3_yellow_1(X0))
      & v2_waybel_0(X1,k3_yellow_1(X0))
      & ~ v1_xboole_0(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ( v2_waybel_7(X1,k3_yellow_1(X0))
      <~> ! [X2] :
            ( r2_hidden(k6_subset_1(X0,X2),X1)
            | r2_hidden(X2,X1)
            | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      & v13_waybel_0(X1,k3_yellow_1(X0))
      & v2_waybel_0(X1,k3_yellow_1(X0))
      & ~ v1_xboole_0(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ( v2_waybel_7(X1,k3_yellow_1(X0))
      <~> ! [X2] :
            ( r2_hidden(k6_subset_1(X0,X2),X1)
            | r2_hidden(X2,X1)
            | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      & v13_waybel_0(X1,k3_yellow_1(X0))
      & v2_waybel_0(X1,k3_yellow_1(X0))
      & ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f15])).

% (21905)Refutation not found, incomplete strategy% (21905)------------------------------
% (21905)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (21905)Termination reason: Refutation not found, incomplete strategy

% (21905)Memory used [KB]: 6268
% (21905)Time elapsed: 0.003 s
% (21905)------------------------------
% (21905)------------------------------
% (21898)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          & v13_waybel_0(X1,k3_yellow_1(X0))
          & v2_waybel_0(X1,k3_yellow_1(X0))
          & ~ v1_xboole_0(X1) )
       => ( v2_waybel_7(X1,k3_yellow_1(X0))
        <=> ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(X0))
             => ( r2_hidden(k6_subset_1(X0,X2),X1)
                | r2_hidden(X2,X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
        & v13_waybel_0(X1,k3_yellow_1(X0))
        & v2_waybel_0(X1,k3_yellow_1(X0))
        & ~ v1_xboole_0(X1) )
     => ( v2_waybel_7(X1,k3_yellow_1(X0))
      <=> ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r2_hidden(k6_subset_1(X0,X2),X1)
              | r2_hidden(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_waybel_7)).

fof(f129,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f87,f127])).

fof(f87,plain,(
    v2_waybel_0(sK1,g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0)))) ),
    inference(definition_unfolding,[],[f45,f80])).

fof(f45,plain,(
    v2_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f125,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f86,f123])).

fof(f86,plain,(
    v13_waybel_0(sK1,g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0)))) ),
    inference(definition_unfolding,[],[f46,f80])).

fof(f46,plain,(
    v13_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f121,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f85,f119])).

fof(f85,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0)))))) ),
    inference(definition_unfolding,[],[f47,f80])).

fof(f47,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0)))) ),
    inference(cnf_transformation,[],[f39])).

fof(f117,plain,
    ( spl4_1
    | spl4_5 ),
    inference(avatar_split_clause,[],[f84,f115,f99])).

fof(f84,plain,(
    ! [X3] :
      ( r2_hidden(k6_subset_1(sK0,X3),sK1)
      | r2_hidden(X3,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(sK0))
      | v2_waybel_7(sK1,g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0)))) ) ),
    inference(definition_unfolding,[],[f48,f80])).

% (21899)Refutation not found, incomplete strategy% (21899)------------------------------
% (21899)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (21899)Termination reason: Refutation not found, incomplete strategy

% (21899)Memory used [KB]: 10618
% (21899)Time elapsed: 0.135 s
% (21899)------------------------------
% (21899)------------------------------
fof(f48,plain,(
    ! [X3] :
      ( r2_hidden(k6_subset_1(sK0,X3),sK1)
      | r2_hidden(X3,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(sK0))
      | v2_waybel_7(sK1,k3_yellow_1(sK0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f112,plain,
    ( ~ spl4_1
    | spl4_4 ),
    inference(avatar_split_clause,[],[f83,f110,f99])).

fof(f83,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ v2_waybel_7(sK1,g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0)))) ),
    inference(definition_unfolding,[],[f49,f80])).

fof(f49,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ v2_waybel_7(sK1,k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f108,plain,
    ( ~ spl4_1
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f82,f106,f99])).

fof(f82,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ v2_waybel_7(sK1,g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0)))) ),
    inference(definition_unfolding,[],[f50,f80])).

fof(f50,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ v2_waybel_7(sK1,k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f104,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f81,f102,f99])).

fof(f81,plain,
    ( ~ r2_hidden(k6_subset_1(sK0,sK2),sK1)
    | ~ v2_waybel_7(sK1,g1_orders_2(k1_zfmisc_1(sK0),k1_yellow_1(k1_zfmisc_1(sK0)))) ),
    inference(definition_unfolding,[],[f51,f80])).

fof(f51,plain,
    ( ~ r2_hidden(k6_subset_1(sK0,sK2),sK1)
    | ~ v2_waybel_7(sK1,k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f39])).

%------------------------------------------------------------------------------
