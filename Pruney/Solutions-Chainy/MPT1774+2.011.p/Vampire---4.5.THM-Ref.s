%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.26s
% Verified   : 
% Statistics : Number of formulae       :  213 ( 689 expanded)
%              Number of leaves         :   58 ( 390 expanded)
%              Depth                    :    9
%              Number of atoms          : 1318 (11060 expanded)
%              Number of equality atoms :   57 ( 586 expanded)
%              Maximal formula depth    :   28 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f416,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f84,f87,f91,f95,f99,f103,f107,f111,f115,f119,f123,f127,f131,f135,f139,f143,f147,f151,f155,f159,f163,f167,f171,f176,f181,f191,f201,f208,f223,f228,f239,f247,f255,f264,f270,f276,f286,f295,f309,f316,f327,f381,f412,f415])).

fof(f415,plain,
    ( ~ spl8_25
    | ~ spl8_10
    | spl8_17
    | spl8_34
    | ~ spl8_4
    | ~ spl8_59 ),
    inference(avatar_split_clause,[],[f413,f410,f93,f245,f145,f117,f179])).

fof(f179,plain,
    ( spl8_25
  <=> m1_subset_1(sK6,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f117,plain,
    ( spl8_10
  <=> m1_pre_topc(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

% (25041)Refutation not found, incomplete strategy% (25041)------------------------------
% (25041)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f145,plain,
    ( spl8_17
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

% (25041)Termination reason: Refutation not found, incomplete strategy

fof(f245,plain,
    ( spl8_34
  <=> r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).

% (25041)Memory used [KB]: 10618
fof(f93,plain,
    ( spl8_4
  <=> r1_tarski(sK5,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

% (25041)Time elapsed: 0.078 s
% (25041)------------------------------
% (25041)------------------------------
fof(f410,plain,
    ( spl8_59
  <=> ! [X0] :
        ( r1_tmap_1(X0,sK0,k2_tmap_1(sK3,sK0,sK4,X0),sK6)
        | ~ r1_tarski(sK5,u1_struct_0(X0))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_subset_1(sK6,u1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_59])])).

fof(f413,plain,
    ( r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK6)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ spl8_4
    | ~ spl8_59 ),
    inference(resolution,[],[f411,f94])).

fof(f94,plain,
    ( r1_tarski(sK5,u1_struct_0(sK2))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f93])).

% (25053)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% (25058)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% (25051)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% (25059)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
fof(f411,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK5,u1_struct_0(X0))
        | r1_tmap_1(X0,sK0,k2_tmap_1(sK3,sK0,sK4,X0),sK6)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_subset_1(sK6,u1_struct_0(X0)) )
    | ~ spl8_59 ),
    inference(avatar_component_clause,[],[f410])).

fof(f412,plain,
    ( ~ spl8_37
    | ~ spl8_36
    | spl8_59
    | ~ spl8_5
    | ~ spl8_54 ),
    inference(avatar_split_clause,[],[f408,f379,f97,f410,f259,f262])).

fof(f262,plain,
    ( spl8_37
  <=> m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).

fof(f259,plain,
    ( spl8_36
  <=> v3_pre_topc(sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).

fof(f97,plain,
    ( spl8_5
  <=> r2_hidden(sK6,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f379,plain,
    ( spl8_54
  <=> ! [X1,X0] :
        ( r1_tmap_1(X0,sK0,k2_tmap_1(sK3,sK0,sK4,X0),sK6)
        | ~ r2_hidden(sK6,X1)
        | ~ v3_pre_topc(X1,sK3)
        | ~ m1_subset_1(sK6,u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(X0)
        | ~ r1_tarski(X1,u1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_54])])).

fof(f408,plain,
    ( ! [X0] :
        ( r1_tmap_1(X0,sK0,k2_tmap_1(sK3,sK0,sK4,X0),sK6)
        | ~ v3_pre_topc(sK5,sK3)
        | ~ m1_subset_1(sK6,u1_struct_0(X0))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(X0)
        | ~ r1_tarski(sK5,u1_struct_0(X0)) )
    | ~ spl8_5
    | ~ spl8_54 ),
    inference(resolution,[],[f380,f98])).

fof(f98,plain,
    ( r2_hidden(sK6,sK5)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f97])).

fof(f380,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK6,X1)
        | r1_tmap_1(X0,sK0,k2_tmap_1(sK3,sK0,sK4,X0),sK6)
        | ~ v3_pre_topc(X1,sK3)
        | ~ m1_subset_1(sK6,u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(X0)
        | ~ r1_tarski(X1,u1_struct_0(X0)) )
    | ~ spl8_54 ),
    inference(avatar_component_clause,[],[f379])).

fof(f381,plain,
    ( ~ spl8_8
    | spl8_54
    | ~ spl8_1
    | ~ spl8_46 ),
    inference(avatar_split_clause,[],[f377,f325,f79,f379,f109])).

fof(f109,plain,
    ( spl8_8
  <=> m1_subset_1(sK6,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f79,plain,
    ( spl8_1
  <=> r1_tmap_1(sK3,sK0,sK4,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f325,plain,
    ( spl8_46
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(X0,u1_struct_0(X1))
        | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X2)
        | ~ r1_tmap_1(sK3,sK0,sK4,X2)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ v3_pre_topc(X0,sK3)
        | ~ r2_hidden(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_46])])).

fof(f377,plain,
    ( ! [X0,X1] :
        ( r1_tmap_1(X0,sK0,k2_tmap_1(sK3,sK0,sK4,X0),sK6)
        | ~ r1_tarski(X1,u1_struct_0(X0))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(sK6,u1_struct_0(sK3))
        | ~ m1_subset_1(sK6,u1_struct_0(X0))
        | ~ v3_pre_topc(X1,sK3)
        | ~ r2_hidden(sK6,X1) )
    | ~ spl8_1
    | ~ spl8_46 ),
    inference(resolution,[],[f326,f85])).

fof(f85,plain,
    ( r1_tmap_1(sK3,sK0,sK4,sK6)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f79])).

fof(f326,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tmap_1(sK3,sK0,sK4,X2)
        | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X2)
        | ~ r1_tarski(X0,u1_struct_0(X1))
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ v3_pre_topc(X0,sK3)
        | ~ r2_hidden(X2,X0) )
    | ~ spl8_46 ),
    inference(avatar_component_clause,[],[f325])).

fof(f327,plain,
    ( spl8_23
    | ~ spl8_22
    | ~ spl8_21
    | spl8_15
    | ~ spl8_29
    | ~ spl8_30
    | ~ spl8_11
    | spl8_46
    | ~ spl8_12
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f323,f129,f125,f325,f121,f213,f210,f137,f161,f165,f169])).

fof(f169,plain,
    ( spl8_23
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f165,plain,
    ( spl8_22
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f161,plain,
    ( spl8_21
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f137,plain,
    ( spl8_15
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f210,plain,
    ( spl8_29
  <=> v2_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).

fof(f213,plain,
    ( spl8_30
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f121,plain,
    ( spl8_11
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f125,plain,
    ( spl8_12
  <=> v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f129,plain,
    ( spl8_13
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f323,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,u1_struct_0(X1))
        | ~ r2_hidden(X2,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | ~ m1_subset_1(X2,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(X1,sK3)
        | v2_struct_0(X1)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
        | ~ r1_tmap_1(sK3,sK0,sK4,X2)
        | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X2)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_12
    | ~ spl8_13 ),
    inference(resolution,[],[f265,f126])).

fof(f126,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f125])).

fof(f265,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
        | ~ r1_tarski(X3,u1_struct_0(X4))
        | ~ r2_hidden(X2,X3)
        | ~ v3_pre_topc(X3,X0)
        | ~ m1_subset_1(X2,u1_struct_0(X4))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(X4,X0)
        | v2_struct_0(X4)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ r1_tmap_1(X0,X1,sK4,X2)
        | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,sK4,X4),X2)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl8_13 ),
    inference(resolution,[],[f77,f130])).

% (25052)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% (25060)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% (25047)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
fof(f130,plain,
    ( v1_funct_1(sK4)
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f129])).

fof(f77,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r1_tmap_1(X1,X0,X2,X6)
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ r2_hidden(X6,X4)
      | ~ v3_pre_topc(X4,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | ~ r1_tmap_1(X1,X0,X2,X5)
      | X5 != X6
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ r2_hidden(X5,X4)
      | ~ v3_pre_topc(X4,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( ( r1_tmap_1(X1,X0,X2,X5)
                                  | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                                & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
                                  | ~ r1_tmap_1(X1,X0,X2,X5) ) )
                              | X5 != X6
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ r2_hidden(X5,X4)
                              | ~ v3_pre_topc(X4,X1)
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X1,X0,X2,X5)
                              <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                              | X5 != X6
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ r2_hidden(X5,X4)
                              | ~ v3_pre_topc(X4,X1)
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X1,X0,X2,X5)
                              <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                              | X5 != X6
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ r2_hidden(X5,X4)
                              | ~ v3_pre_topc(X4,X1)
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X3))
                             => ( ( X5 = X6
                                  & r1_tarski(X4,u1_struct_0(X3))
                                  & r2_hidden(X5,X4)
                                  & v3_pre_topc(X4,X1) )
                               => ( r1_tmap_1(X1,X0,X2,X5)
                                <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tmap_1)).

fof(f316,plain,
    ( ~ spl8_34
    | spl8_2
    | ~ spl8_3
    | ~ spl8_32 ),
    inference(avatar_split_clause,[],[f314,f236,f89,f82,f245])).

fof(f82,plain,
    ( spl8_2
  <=> r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f89,plain,
    ( spl8_3
  <=> sK6 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f236,plain,
    ( spl8_32
  <=> k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = k2_tmap_1(sK3,sK0,sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f314,plain,
    ( ~ r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK6)
    | spl8_2
    | ~ spl8_3
    | ~ spl8_32 ),
    inference(forward_demodulation,[],[f313,f237])).

fof(f237,plain,
    ( k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = k2_tmap_1(sK3,sK0,sK4,sK2)
    | ~ spl8_32 ),
    inference(avatar_component_clause,[],[f236])).

fof(f313,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | spl8_2
    | ~ spl8_3 ),
    inference(forward_demodulation,[],[f83,f90])).

fof(f90,plain,
    ( sK6 = sK7
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f89])).

fof(f83,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f82])).

fof(f309,plain,
    ( ~ spl8_4
    | spl8_41 ),
    inference(avatar_split_clause,[],[f301,f293,f93])).

fof(f293,plain,
    ( spl8_41
  <=> m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_41])])).

fof(f301,plain,
    ( ~ r1_tarski(sK5,u1_struct_0(sK2))
    | spl8_41 ),
    inference(resolution,[],[f294,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f294,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | spl8_41 ),
    inference(avatar_component_clause,[],[f293])).

fof(f295,plain,
    ( ~ spl8_41
    | ~ spl8_10
    | ~ spl8_39 ),
    inference(avatar_split_clause,[],[f290,f274,f117,f293])).

fof(f274,plain,
    ( spl8_39
  <=> ! [X0] :
        ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(X0,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).

fof(f290,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl8_10
    | ~ spl8_39 ),
    inference(resolution,[],[f275,f118])).

fof(f118,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f117])).

fof(f275,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) )
    | ~ spl8_39 ),
    inference(avatar_component_clause,[],[f274])).

fof(f286,plain,
    ( ~ spl8_14
    | ~ spl8_9
    | ~ spl8_18
    | ~ spl8_6
    | ~ spl8_38 ),
    inference(avatar_split_clause,[],[f281,f268,f101,f149,f113,f133])).

fof(f133,plain,
    ( spl8_14
  <=> m1_pre_topc(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f113,plain,
    ( spl8_9
  <=> m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f149,plain,
    ( spl8_18
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f101,plain,
    ( spl8_6
  <=> v3_pre_topc(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f268,plain,
    ( spl8_38
  <=> ! [X0] :
        ( ~ v3_pre_topc(sK5,X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(sK3,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).

fof(f281,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_pre_topc(sK3,sK1)
    | ~ spl8_6
    | ~ spl8_38 ),
    inference(resolution,[],[f269,f102])).

fof(f102,plain,
    ( v3_pre_topc(sK5,sK1)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f101])).

fof(f269,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(sK5,X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(sK3,X0) )
    | ~ spl8_38 ),
    inference(avatar_component_clause,[],[f268])).

fof(f276,plain,
    ( ~ spl8_30
    | spl8_39
    | spl8_37 ),
    inference(avatar_split_clause,[],[f271,f262,f274,f213])).

fof(f271,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(X0,sK3)
        | ~ l1_pre_topc(sK3) )
    | spl8_37 ),
    inference(resolution,[],[f263,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

fof(f263,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | spl8_37 ),
    inference(avatar_component_clause,[],[f262])).

fof(f270,plain,
    ( spl8_38
    | ~ spl8_37
    | spl8_36 ),
    inference(avatar_split_clause,[],[f266,f259,f262,f268])).

fof(f266,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ v3_pre_topc(sK5,X0)
        | ~ m1_pre_topc(sK3,X0)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | spl8_36 ),
    inference(resolution,[],[f260,f75])).

fof(f75,plain,(
    ! [X2,X0,X3] :
      ( v3_pre_topc(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X3,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v3_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v3_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v3_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v3_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tops_2)).

fof(f260,plain,
    ( ~ v3_pre_topc(sK5,sK3)
    | spl8_36 ),
    inference(avatar_component_clause,[],[f259])).

fof(f264,plain,
    ( ~ spl8_4
    | ~ spl8_36
    | ~ spl8_37
    | ~ spl8_5
    | ~ spl8_35 ),
    inference(avatar_split_clause,[],[f256,f253,f97,f262,f259,f93])).

fof(f253,plain,
    ( spl8_35
  <=> ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ v3_pre_topc(X0,sK3)
        | ~ r2_hidden(sK6,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).

fof(f256,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v3_pre_topc(sK5,sK3)
    | ~ r1_tarski(sK5,u1_struct_0(sK2))
    | ~ spl8_5
    | ~ spl8_35 ),
    inference(resolution,[],[f254,f98])).

fof(f254,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK6,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ v3_pre_topc(X0,sK3)
        | ~ r1_tarski(X0,u1_struct_0(sK2)) )
    | ~ spl8_35 ),
    inference(avatar_component_clause,[],[f253])).

fof(f255,plain,
    ( spl8_23
    | ~ spl8_22
    | ~ spl8_21
    | spl8_15
    | ~ spl8_29
    | ~ spl8_30
    | ~ spl8_13
    | ~ spl8_12
    | ~ spl8_11
    | spl8_17
    | ~ spl8_10
    | ~ spl8_8
    | ~ spl8_25
    | spl8_35
    | spl8_1
    | ~ spl8_34 ),
    inference(avatar_split_clause,[],[f248,f245,f79,f253,f179,f109,f117,f145,f121,f125,f129,f213,f210,f137,f161,f165,f169])).

fof(f248,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK3,sK0,sK4,sK6)
        | ~ r1_tarski(X0,u1_struct_0(sK2))
        | ~ r2_hidden(sK6,X0)
        | ~ v3_pre_topc(X0,sK3)
        | ~ m1_subset_1(sK6,u1_struct_0(sK2))
        | ~ m1_subset_1(sK6,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_pre_topc(sK2,sK3)
        | v2_struct_0(sK2)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
        | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
        | ~ v1_funct_1(sK4)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_34 ),
    inference(resolution,[],[f246,f76])).

fof(f76,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | r1_tmap_1(X1,X0,X2,X6)
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ r2_hidden(X6,X4)
      | ~ v3_pre_topc(X4,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X1,X0,X2,X5)
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | X5 != X6
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ r2_hidden(X5,X4)
      | ~ v3_pre_topc(X4,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f246,plain,
    ( r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK6)
    | ~ spl8_34 ),
    inference(avatar_component_clause,[],[f245])).

fof(f247,plain,
    ( spl8_34
    | ~ spl8_24
    | ~ spl8_32 ),
    inference(avatar_split_clause,[],[f243,f236,f174,f245])).

fof(f174,plain,
    ( spl8_24
  <=> r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f243,plain,
    ( r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK6)
    | ~ spl8_24
    | ~ spl8_32 ),
    inference(superposition,[],[f175,f237])).

fof(f175,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f174])).

fof(f239,plain,
    ( spl8_15
    | ~ spl8_29
    | ~ spl8_30
    | spl8_23
    | ~ spl8_22
    | ~ spl8_21
    | ~ spl8_13
    | ~ spl8_12
    | ~ spl8_11
    | ~ spl8_10
    | spl8_32
    | ~ spl8_28 ),
    inference(avatar_split_clause,[],[f230,f206,f236,f117,f121,f125,f129,f161,f165,f169,f213,f210,f137])).

fof(f206,plain,
    ( spl8_28
  <=> k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f230,plain,
    ( k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = k2_tmap_1(sK3,sK0,sK4,sK2)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ spl8_28 ),
    inference(superposition,[],[f68,f207])).

fof(f207,plain,
    ( k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2))
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f206])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f228,plain,
    ( ~ spl8_18
    | ~ spl8_14
    | spl8_30 ),
    inference(avatar_split_clause,[],[f225,f213,f133,f149])).

fof(f225,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ spl8_14
    | spl8_30 ),
    inference(resolution,[],[f224,f134])).

fof(f134,plain,
    ( m1_pre_topc(sK3,sK1)
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f133])).

fof(f224,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK3,X0)
        | ~ l1_pre_topc(X0) )
    | spl8_30 ),
    inference(resolution,[],[f214,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f214,plain,
    ( ~ l1_pre_topc(sK3)
    | spl8_30 ),
    inference(avatar_component_clause,[],[f213])).

fof(f223,plain,
    ( ~ spl8_19
    | ~ spl8_18
    | ~ spl8_14
    | spl8_29 ),
    inference(avatar_split_clause,[],[f220,f210,f133,f149,f153])).

fof(f153,plain,
    ( spl8_19
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f220,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl8_14
    | spl8_29 ),
    inference(resolution,[],[f219,f134])).

fof(f219,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK3,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | spl8_29 ),
    inference(resolution,[],[f211,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f211,plain,
    ( ~ v2_pre_topc(sK3)
    | spl8_29 ),
    inference(avatar_component_clause,[],[f210])).

fof(f208,plain,
    ( ~ spl8_16
    | spl8_28
    | ~ spl8_10
    | ~ spl8_27 ),
    inference(avatar_split_clause,[],[f202,f196,f117,f206,f141])).

fof(f141,plain,
    ( spl8_16
  <=> m1_pre_topc(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f196,plain,
    ( spl8_27
  <=> ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) = k3_tmap_1(sK1,sK0,sK3,X0,sK4)
        | ~ m1_pre_topc(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f202,plain,
    ( k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK1)
    | ~ spl8_10
    | ~ spl8_27 ),
    inference(resolution,[],[f197,f118])).

fof(f197,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) = k3_tmap_1(sK1,sK0,sK3,X0,sK4)
        | ~ m1_pre_topc(X0,sK1) )
    | ~ spl8_27 ),
    inference(avatar_component_clause,[],[f196])).

fof(f201,plain,
    ( spl8_27
    | ~ spl8_18
    | ~ spl8_19
    | spl8_20
    | ~ spl8_14
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f192,f188,f133,f157,f153,f149,f196])).

fof(f157,plain,
    ( spl8_20
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f188,plain,
    ( spl8_26
  <=> ! [X1,X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(sK3,X1)
        | ~ m1_pre_topc(X0,X1)
        | k3_tmap_1(X1,sK0,sK3,X0,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f192,plain,
    ( ! [X0] :
        ( v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(X0,sK1)
        | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) = k3_tmap_1(sK1,sK0,sK3,X0,sK4) )
    | ~ spl8_14
    | ~ spl8_26 ),
    inference(resolution,[],[f189,f134])).

fof(f189,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(X0,X1)
        | k3_tmap_1(X1,sK0,sK3,X0,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) )
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f188])).

fof(f191,plain,
    ( spl8_23
    | ~ spl8_22
    | ~ spl8_21
    | spl8_26
    | ~ spl8_11
    | ~ spl8_12
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f183,f129,f125,f121,f188,f161,f165,f169])).

fof(f183,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
        | ~ m1_pre_topc(X0,sK3)
        | k3_tmap_1(X1,sK0,sK3,X0,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(sK3,X1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl8_12
    | ~ spl8_13 ),
    inference(resolution,[],[f182,f126])).

fof(f182,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X2))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
        | ~ m1_pre_topc(X0,X1)
        | k3_tmap_1(X3,X2,X1,X0,sK4) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0))
        | ~ m1_pre_topc(X0,X3)
        | ~ m1_pre_topc(X1,X3)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(X3)
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3) )
    | ~ spl8_13 ),
    inference(resolution,[],[f67,f130])).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X3,X2)
                       => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

fof(f181,plain,
    ( spl8_25
    | ~ spl8_3
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f177,f105,f89,f179])).

fof(f105,plain,
    ( spl8_7
  <=> m1_subset_1(sK7,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f177,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ spl8_3
    | ~ spl8_7 ),
    inference(superposition,[],[f106,f90])).

fof(f106,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK2))
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f105])).

fof(f176,plain,
    ( spl8_24
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f172,f89,f82,f174])).

fof(f172,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(forward_demodulation,[],[f86,f90])).

fof(f86,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f82])).

fof(f171,plain,(
    ~ spl8_23 ),
    inference(avatar_split_clause,[],[f41,f169])).

fof(f41,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
      | ~ r1_tmap_1(sK3,sK0,sK4,sK6) )
    & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
      | r1_tmap_1(sK3,sK0,sK4,sK6) )
    & sK6 = sK7
    & r1_tarski(sK5,u1_struct_0(sK2))
    & r2_hidden(sK6,sK5)
    & v3_pre_topc(sK5,sK1)
    & m1_subset_1(sK7,u1_struct_0(sK2))
    & m1_subset_1(sK6,u1_struct_0(sK3))
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_pre_topc(sK2,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    & v1_funct_1(sK4)
    & m1_pre_topc(sK3,sK1)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK1)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f29,f37,f36,f35,f34,f33,f32,f31,f30])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ? [X7] :
                                    ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                      | ~ r1_tmap_1(X3,X0,X4,X6) )
                                    & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                      | r1_tmap_1(X3,X0,X4,X6) )
                                    & X6 = X7
                                    & r1_tarski(X5,u1_struct_0(X2))
                                    & r2_hidden(X6,X5)
                                    & v3_pre_topc(X5,X1)
                                    & m1_subset_1(X7,u1_struct_0(X2)) )
                                & m1_subset_1(X6,u1_struct_0(X3)) )
                            & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                        & m1_pre_topc(X2,X3)
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                    & m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( ~ r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,sK0,X4,X6) )
                                  & ( r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X7)
                                    | r1_tmap_1(X3,sK0,X4,X6) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X1)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ? [X7] :
                                ( ( ~ r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X7)
                                  | ~ r1_tmap_1(X3,sK0,X4,X6) )
                                & ( r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X7)
                                  | r1_tmap_1(X3,sK0,X4,X6) )
                                & X6 = X7
                                & r1_tarski(X5,u1_struct_0(X2))
                                & r2_hidden(X6,X5)
                                & v3_pre_topc(X5,X1)
                                & m1_subset_1(X7,u1_struct_0(X2)) )
                            & m1_subset_1(X6,u1_struct_0(X3)) )
                        & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                    & m1_pre_topc(X2,X3)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,X1)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X1)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ? [X7] :
                              ( ( ~ r1_tmap_1(X2,sK0,k3_tmap_1(sK1,sK0,X3,X2,X4),X7)
                                | ~ r1_tmap_1(X3,sK0,X4,X6) )
                              & ( r1_tmap_1(X2,sK0,k3_tmap_1(sK1,sK0,X3,X2,X4),X7)
                                | r1_tmap_1(X3,sK0,X4,X6) )
                              & X6 = X7
                              & r1_tarski(X5,u1_struct_0(X2))
                              & r2_hidden(X6,X5)
                              & v3_pre_topc(X5,sK1)
                              & m1_subset_1(X7,u1_struct_0(X2)) )
                          & m1_subset_1(X6,u1_struct_0(X3)) )
                      & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1))) )
                  & m1_pre_topc(X2,X3)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
                  & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,sK1)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK1)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ? [X7] :
                            ( ( ~ r1_tmap_1(X2,sK0,k3_tmap_1(sK1,sK0,X3,X2,X4),X7)
                              | ~ r1_tmap_1(X3,sK0,X4,X6) )
                            & ( r1_tmap_1(X2,sK0,k3_tmap_1(sK1,sK0,X3,X2,X4),X7)
                              | r1_tmap_1(X3,sK0,X4,X6) )
                            & X6 = X7
                            & r1_tarski(X5,u1_struct_0(X2))
                            & r2_hidden(X6,X5)
                            & v3_pre_topc(X5,sK1)
                            & m1_subset_1(X7,u1_struct_0(X2)) )
                        & m1_subset_1(X6,u1_struct_0(X3)) )
                    & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1))) )
                & m1_pre_topc(X2,X3)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,sK1)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK1)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ? [X7] :
                          ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,X3,sK2,X4),X7)
                            | ~ r1_tmap_1(X3,sK0,X4,X6) )
                          & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,X3,sK2,X4),X7)
                            | r1_tmap_1(X3,sK0,X4,X6) )
                          & X6 = X7
                          & r1_tarski(X5,u1_struct_0(sK2))
                          & r2_hidden(X6,X5)
                          & v3_pre_topc(X5,sK1)
                          & m1_subset_1(X7,u1_struct_0(sK2)) )
                      & m1_subset_1(X6,u1_struct_0(X3)) )
                  & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1))) )
              & m1_pre_topc(sK2,X3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
              & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,sK1)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK1)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ? [X7] :
                        ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,X3,sK2,X4),X7)
                          | ~ r1_tmap_1(X3,sK0,X4,X6) )
                        & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,X3,sK2,X4),X7)
                          | r1_tmap_1(X3,sK0,X4,X6) )
                        & X6 = X7
                        & r1_tarski(X5,u1_struct_0(sK2))
                        & r2_hidden(X6,X5)
                        & v3_pre_topc(X5,sK1)
                        & m1_subset_1(X7,u1_struct_0(sK2)) )
                    & m1_subset_1(X6,u1_struct_0(X3)) )
                & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1))) )
            & m1_pre_topc(sK2,X3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
            & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0))
            & v1_funct_1(X4) )
        & m1_pre_topc(X3,sK1)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ? [X7] :
                      ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X4),X7)
                        | ~ r1_tmap_1(sK3,sK0,X4,X6) )
                      & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X4),X7)
                        | r1_tmap_1(sK3,sK0,X4,X6) )
                      & X6 = X7
                      & r1_tarski(X5,u1_struct_0(sK2))
                      & r2_hidden(X6,X5)
                      & v3_pre_topc(X5,sK1)
                      & m1_subset_1(X7,u1_struct_0(sK2)) )
                  & m1_subset_1(X6,u1_struct_0(sK3)) )
              & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1))) )
          & m1_pre_topc(sK2,sK3)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
          & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK0))
          & v1_funct_1(X4) )
      & m1_pre_topc(sK3,sK1)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ? [X7] :
                    ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X4),X7)
                      | ~ r1_tmap_1(sK3,sK0,X4,X6) )
                    & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X4),X7)
                      | r1_tmap_1(sK3,sK0,X4,X6) )
                    & X6 = X7
                    & r1_tarski(X5,u1_struct_0(sK2))
                    & r2_hidden(X6,X5)
                    & v3_pre_topc(X5,sK1)
                    & m1_subset_1(X7,u1_struct_0(sK2)) )
                & m1_subset_1(X6,u1_struct_0(sK3)) )
            & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1))) )
        & m1_pre_topc(sK2,sK3)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
        & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK0))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7)
                    | ~ r1_tmap_1(sK3,sK0,sK4,X6) )
                  & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7)
                    | r1_tmap_1(sK3,sK0,sK4,X6) )
                  & X6 = X7
                  & r1_tarski(X5,u1_struct_0(sK2))
                  & r2_hidden(X6,X5)
                  & v3_pre_topc(X5,sK1)
                  & m1_subset_1(X7,u1_struct_0(sK2)) )
              & m1_subset_1(X6,u1_struct_0(sK3)) )
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1))) )
      & m1_pre_topc(sK2,sK3)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
      & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ? [X7] :
                ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7)
                  | ~ r1_tmap_1(sK3,sK0,sK4,X6) )
                & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7)
                  | r1_tmap_1(sK3,sK0,sK4,X6) )
                & X6 = X7
                & r1_tarski(X5,u1_struct_0(sK2))
                & r2_hidden(X6,X5)
                & v3_pre_topc(X5,sK1)
                & m1_subset_1(X7,u1_struct_0(sK2)) )
            & m1_subset_1(X6,u1_struct_0(sK3)) )
        & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1))) )
   => ( ? [X6] :
          ( ? [X7] :
              ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7)
                | ~ r1_tmap_1(sK3,sK0,sK4,X6) )
              & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7)
                | r1_tmap_1(sK3,sK0,sK4,X6) )
              & X6 = X7
              & r1_tarski(sK5,u1_struct_0(sK2))
              & r2_hidden(X6,sK5)
              & v3_pre_topc(sK5,sK1)
              & m1_subset_1(X7,u1_struct_0(sK2)) )
          & m1_subset_1(X6,u1_struct_0(sK3)) )
      & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X6] :
        ( ? [X7] :
            ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7)
              | ~ r1_tmap_1(sK3,sK0,sK4,X6) )
            & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7)
              | r1_tmap_1(sK3,sK0,sK4,X6) )
            & X6 = X7
            & r1_tarski(sK5,u1_struct_0(sK2))
            & r2_hidden(X6,sK5)
            & v3_pre_topc(sK5,sK1)
            & m1_subset_1(X7,u1_struct_0(sK2)) )
        & m1_subset_1(X6,u1_struct_0(sK3)) )
   => ( ? [X7] :
          ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7)
            | ~ r1_tmap_1(sK3,sK0,sK4,sK6) )
          & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7)
            | r1_tmap_1(sK3,sK0,sK4,sK6) )
          & sK6 = X7
          & r1_tarski(sK5,u1_struct_0(sK2))
          & r2_hidden(sK6,sK5)
          & v3_pre_topc(sK5,sK1)
          & m1_subset_1(X7,u1_struct_0(sK2)) )
      & m1_subset_1(sK6,u1_struct_0(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X7] :
        ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7)
          | ~ r1_tmap_1(sK3,sK0,sK4,sK6) )
        & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7)
          | r1_tmap_1(sK3,sK0,sK4,sK6) )
        & sK6 = X7
        & r1_tarski(sK5,u1_struct_0(sK2))
        & r2_hidden(sK6,sK5)
        & v3_pre_topc(sK5,sK1)
        & m1_subset_1(X7,u1_struct_0(sK2)) )
   => ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
        | ~ r1_tmap_1(sK3,sK0,sK4,sK6) )
      & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
        | r1_tmap_1(sK3,sK0,sK4,sK6) )
      & sK6 = sK7
      & r1_tarski(sK5,u1_struct_0(sK2))
      & r2_hidden(sK6,sK5)
      & v3_pre_topc(sK5,sK1)
      & m1_subset_1(sK7,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,X0,X4,X6) )
                                  & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                    | r1_tmap_1(X3,X0,X4,X6) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X1)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                    | ~ r1_tmap_1(X3,X0,X4,X6) )
                                  & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)
                                    | r1_tmap_1(X3,X0,X4,X6) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X1)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( r1_tmap_1(X3,X0,X4,X6)
                                  <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X1)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ( r1_tmap_1(X3,X0,X4,X6)
                                  <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) )
                                  & X6 = X7
                                  & r1_tarski(X5,u1_struct_0(X2))
                                  & r2_hidden(X6,X5)
                                  & v3_pre_topc(X5,X1)
                                  & m1_subset_1(X7,u1_struct_0(X2)) )
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X1)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X1)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                          & v1_funct_1(X4) )
                       => ( m1_pre_topc(X2,X3)
                         => ! [X5] :
                              ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X3))
                                 => ! [X7] :
                                      ( m1_subset_1(X7,u1_struct_0(X2))
                                     => ( ( X6 = X7
                                          & r1_tarski(X5,u1_struct_0(X2))
                                          & r2_hidden(X6,X5)
                                          & v3_pre_topc(X5,X1) )
                                       => ( r1_tmap_1(X3,X0,X4,X6)
                                        <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X2,X3)
                       => ! [X5] :
                            ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X3))
                               => ! [X7] :
                                    ( m1_subset_1(X7,u1_struct_0(X2))
                                   => ( ( X6 = X7
                                        & r1_tarski(X5,u1_struct_0(X2))
                                        & r2_hidden(X6,X5)
                                        & v3_pre_topc(X5,X1) )
                                     => ( r1_tmap_1(X3,X0,X4,X6)
                                      <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_tmap_1)).

fof(f167,plain,(
    spl8_22 ),
    inference(avatar_split_clause,[],[f42,f165])).

fof(f42,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f163,plain,(
    spl8_21 ),
    inference(avatar_split_clause,[],[f43,f161])).

fof(f43,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f159,plain,(
    ~ spl8_20 ),
    inference(avatar_split_clause,[],[f44,f157])).

fof(f44,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f155,plain,(
    spl8_19 ),
    inference(avatar_split_clause,[],[f45,f153])).

fof(f45,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f151,plain,(
    spl8_18 ),
    inference(avatar_split_clause,[],[f46,f149])).

fof(f46,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f147,plain,(
    ~ spl8_17 ),
    inference(avatar_split_clause,[],[f47,f145])).

fof(f47,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f143,plain,(
    spl8_16 ),
    inference(avatar_split_clause,[],[f48,f141])).

fof(f48,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f139,plain,(
    ~ spl8_15 ),
    inference(avatar_split_clause,[],[f49,f137])).

fof(f49,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f135,plain,(
    spl8_14 ),
    inference(avatar_split_clause,[],[f50,f133])).

fof(f50,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f131,plain,(
    spl8_13 ),
    inference(avatar_split_clause,[],[f51,f129])).

fof(f51,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f127,plain,(
    spl8_12 ),
    inference(avatar_split_clause,[],[f52,f125])).

fof(f52,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f38])).

fof(f123,plain,(
    spl8_11 ),
    inference(avatar_split_clause,[],[f53,f121])).

fof(f53,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f38])).

fof(f119,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f54,f117])).

fof(f54,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f115,plain,(
    spl8_9 ),
    inference(avatar_split_clause,[],[f55,f113])).

fof(f55,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f38])).

fof(f111,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f56,f109])).

fof(f56,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f38])).

fof(f107,plain,(
    spl8_7 ),
    inference(avatar_split_clause,[],[f57,f105])).

fof(f57,plain,(
    m1_subset_1(sK7,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f38])).

fof(f103,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f58,f101])).

fof(f58,plain,(
    v3_pre_topc(sK5,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f99,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f59,f97])).

fof(f59,plain,(
    r2_hidden(sK6,sK5) ),
    inference(cnf_transformation,[],[f38])).

fof(f95,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f60,f93])).

fof(f60,plain,(
    r1_tarski(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f38])).

fof(f91,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f61,f89])).

fof(f61,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f38])).

fof(f87,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f62,f82,f79])).

fof(f62,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
    | r1_tmap_1(sK3,sK0,sK4,sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f84,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f63,f82,f79])).

fof(f63,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK6) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:59:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (25054)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (25046)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (25041)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (25042)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (25040)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (25049)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % (25045)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (25043)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (25044)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  % (25050)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.50  % (25048)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.50  % (25057)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.50  % (25046)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f416,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f84,f87,f91,f95,f99,f103,f107,f111,f115,f119,f123,f127,f131,f135,f139,f143,f147,f151,f155,f159,f163,f167,f171,f176,f181,f191,f201,f208,f223,f228,f239,f247,f255,f264,f270,f276,f286,f295,f309,f316,f327,f381,f412,f415])).
% 0.21/0.50  fof(f415,plain,(
% 0.21/0.50    ~spl8_25 | ~spl8_10 | spl8_17 | spl8_34 | ~spl8_4 | ~spl8_59),
% 0.21/0.50    inference(avatar_split_clause,[],[f413,f410,f93,f245,f145,f117,f179])).
% 0.21/0.50  fof(f179,plain,(
% 0.21/0.50    spl8_25 <=> m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).
% 0.21/0.50  fof(f117,plain,(
% 0.21/0.50    spl8_10 <=> m1_pre_topc(sK2,sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.21/0.50  % (25041)Refutation not found, incomplete strategy% (25041)------------------------------
% 0.21/0.50  % (25041)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  fof(f145,plain,(
% 0.21/0.50    spl8_17 <=> v2_struct_0(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 0.21/0.50  % (25041)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  fof(f245,plain,(
% 0.21/0.50    spl8_34 <=> r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK6)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).
% 0.21/0.50  % (25041)Memory used [KB]: 10618
% 0.21/0.50  fof(f93,plain,(
% 0.21/0.50    spl8_4 <=> r1_tarski(sK5,u1_struct_0(sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.50  % (25041)Time elapsed: 0.078 s
% 0.21/0.50  % (25041)------------------------------
% 0.21/0.50  % (25041)------------------------------
% 0.21/0.50  fof(f410,plain,(
% 0.21/0.50    spl8_59 <=> ! [X0] : (r1_tmap_1(X0,sK0,k2_tmap_1(sK3,sK0,sK4,X0),sK6) | ~r1_tarski(sK5,u1_struct_0(X0)) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(sK6,u1_struct_0(X0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_59])])).
% 0.21/0.50  fof(f413,plain,(
% 0.21/0.50    r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK6) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | (~spl8_4 | ~spl8_59)),
% 0.21/0.50    inference(resolution,[],[f411,f94])).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    r1_tarski(sK5,u1_struct_0(sK2)) | ~spl8_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f93])).
% 0.21/0.50  % (25053)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.50  % (25058)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.51  % (25051)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.51  % (25059)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.51  fof(f411,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(sK5,u1_struct_0(X0)) | r1_tmap_1(X0,sK0,k2_tmap_1(sK3,sK0,sK4,X0),sK6) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(sK6,u1_struct_0(X0))) ) | ~spl8_59),
% 0.21/0.51    inference(avatar_component_clause,[],[f410])).
% 0.21/0.51  fof(f412,plain,(
% 0.21/0.51    ~spl8_37 | ~spl8_36 | spl8_59 | ~spl8_5 | ~spl8_54),
% 0.21/0.51    inference(avatar_split_clause,[],[f408,f379,f97,f410,f259,f262])).
% 0.21/0.51  fof(f262,plain,(
% 0.21/0.51    spl8_37 <=> m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).
% 0.21/0.51  fof(f259,plain,(
% 0.21/0.51    spl8_36 <=> v3_pre_topc(sK5,sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    spl8_5 <=> r2_hidden(sK6,sK5)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.51  fof(f379,plain,(
% 0.21/0.51    spl8_54 <=> ! [X1,X0] : (r1_tmap_1(X0,sK0,k2_tmap_1(sK3,sK0,sK4,X0),sK6) | ~r2_hidden(sK6,X1) | ~v3_pre_topc(X1,sK3) | ~m1_subset_1(sK6,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(X0,sK3) | v2_struct_0(X0) | ~r1_tarski(X1,u1_struct_0(X0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_54])])).
% 0.21/0.51  fof(f408,plain,(
% 0.21/0.51    ( ! [X0] : (r1_tmap_1(X0,sK0,k2_tmap_1(sK3,sK0,sK4,X0),sK6) | ~v3_pre_topc(sK5,sK3) | ~m1_subset_1(sK6,u1_struct_0(X0)) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(X0,sK3) | v2_struct_0(X0) | ~r1_tarski(sK5,u1_struct_0(X0))) ) | (~spl8_5 | ~spl8_54)),
% 0.21/0.51    inference(resolution,[],[f380,f98])).
% 0.21/0.51  fof(f98,plain,(
% 0.21/0.51    r2_hidden(sK6,sK5) | ~spl8_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f97])).
% 0.21/0.51  fof(f380,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(sK6,X1) | r1_tmap_1(X0,sK0,k2_tmap_1(sK3,sK0,sK4,X0),sK6) | ~v3_pre_topc(X1,sK3) | ~m1_subset_1(sK6,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(X0,sK3) | v2_struct_0(X0) | ~r1_tarski(X1,u1_struct_0(X0))) ) | ~spl8_54),
% 0.21/0.51    inference(avatar_component_clause,[],[f379])).
% 0.21/0.51  fof(f381,plain,(
% 0.21/0.51    ~spl8_8 | spl8_54 | ~spl8_1 | ~spl8_46),
% 0.21/0.51    inference(avatar_split_clause,[],[f377,f325,f79,f379,f109])).
% 0.21/0.51  fof(f109,plain,(
% 0.21/0.51    spl8_8 <=> m1_subset_1(sK6,u1_struct_0(sK3))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    spl8_1 <=> r1_tmap_1(sK3,sK0,sK4,sK6)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.51  fof(f325,plain,(
% 0.21/0.51    spl8_46 <=> ! [X1,X0,X2] : (~r1_tarski(X0,u1_struct_0(X1)) | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X2) | ~r1_tmap_1(sK3,sK0,sK4,X2) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~v3_pre_topc(X0,sK3) | ~r2_hidden(X2,X0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_46])])).
% 0.21/0.51  fof(f377,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tmap_1(X0,sK0,k2_tmap_1(sK3,sK0,sK4,X0),sK6) | ~r1_tarski(X1,u1_struct_0(X0)) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK3) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(sK6,u1_struct_0(X0)) | ~v3_pre_topc(X1,sK3) | ~r2_hidden(sK6,X1)) ) | (~spl8_1 | ~spl8_46)),
% 0.21/0.51    inference(resolution,[],[f326,f85])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    r1_tmap_1(sK3,sK0,sK4,sK6) | ~spl8_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f79])).
% 0.21/0.51  fof(f326,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r1_tmap_1(sK3,sK0,sK4,X2) | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X2) | ~r1_tarski(X0,u1_struct_0(X1)) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~v3_pre_topc(X0,sK3) | ~r2_hidden(X2,X0)) ) | ~spl8_46),
% 0.21/0.51    inference(avatar_component_clause,[],[f325])).
% 0.21/0.51  fof(f327,plain,(
% 0.21/0.51    spl8_23 | ~spl8_22 | ~spl8_21 | spl8_15 | ~spl8_29 | ~spl8_30 | ~spl8_11 | spl8_46 | ~spl8_12 | ~spl8_13),
% 0.21/0.51    inference(avatar_split_clause,[],[f323,f129,f125,f325,f121,f213,f210,f137,f161,f165,f169])).
% 0.21/0.51  fof(f169,plain,(
% 0.21/0.51    spl8_23 <=> v2_struct_0(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).
% 0.21/0.51  fof(f165,plain,(
% 0.21/0.51    spl8_22 <=> v2_pre_topc(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).
% 0.21/0.51  fof(f161,plain,(
% 0.21/0.51    spl8_21 <=> l1_pre_topc(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 0.21/0.51  fof(f137,plain,(
% 0.21/0.51    spl8_15 <=> v2_struct_0(sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.21/0.51  fof(f210,plain,(
% 0.21/0.51    spl8_29 <=> v2_pre_topc(sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).
% 0.21/0.51  fof(f213,plain,(
% 0.21/0.51    spl8_30 <=> l1_pre_topc(sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).
% 0.21/0.51  fof(f121,plain,(
% 0.21/0.51    spl8_11 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.21/0.51  fof(f125,plain,(
% 0.21/0.51    spl8_12 <=> v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.21/0.51  fof(f129,plain,(
% 0.21/0.51    spl8_13 <=> v1_funct_1(sK4)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.21/0.51  fof(f323,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r1_tarski(X0,u1_struct_0(X1)) | ~r2_hidden(X2,X0) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(X1,sK3) | v2_struct_0(X1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~r1_tmap_1(sK3,sK0,sK4,X2) | r1_tmap_1(X1,sK0,k2_tmap_1(sK3,sK0,sK4,X1),X2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl8_12 | ~spl8_13)),
% 0.21/0.51    inference(resolution,[],[f265,f126])).
% 0.21/0.51  fof(f126,plain,(
% 0.21/0.51    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~spl8_12),
% 0.21/0.51    inference(avatar_component_clause,[],[f125])).
% 0.21/0.51  fof(f265,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tarski(X3,u1_struct_0(X4)) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X2,u1_struct_0(X4)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~r1_tmap_1(X0,X1,sK4,X2) | r1_tmap_1(X4,X1,k2_tmap_1(X0,X1,sK4,X4),X2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | ~spl8_13),
% 0.21/0.51    inference(resolution,[],[f77,f130])).
% 0.21/0.51  % (25052)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (25060)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (25047)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 1.26/0.52  fof(f130,plain,(
% 1.26/0.52    v1_funct_1(sK4) | ~spl8_13),
% 1.26/0.52    inference(avatar_component_clause,[],[f129])).
% 1.26/0.52  fof(f77,plain,(
% 1.26/0.52    ( ! [X6,X4,X2,X0,X3,X1] : (~v1_funct_1(X2) | ~r1_tmap_1(X1,X0,X2,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X6,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.26/0.52    inference(equality_resolution,[],[f69])).
% 1.26/0.52  fof(f69,plain,(
% 1.26/0.52    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5) | X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f39])).
% 1.26/0.52  fof(f39,plain,(
% 1.26/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) & (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~r1_tmap_1(X1,X0,X2,X5))) | X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.26/0.52    inference(nnf_transformation,[],[f23])).
% 1.26/0.52  fof(f23,plain,(
% 1.26/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.26/0.52    inference(flattening,[],[f22])).
% 1.26/0.52  fof(f22,plain,(
% 1.26/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.26/0.52    inference(ennf_transformation,[],[f8])).
% 1.26/0.52  fof(f8,axiom,(
% 1.26/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & r1_tarski(X4,u1_struct_0(X3)) & r2_hidden(X5,X4) & v3_pre_topc(X4,X1)) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 1.26/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tmap_1)).
% 1.26/0.52  fof(f316,plain,(
% 1.26/0.52    ~spl8_34 | spl8_2 | ~spl8_3 | ~spl8_32),
% 1.26/0.52    inference(avatar_split_clause,[],[f314,f236,f89,f82,f245])).
% 1.26/0.52  fof(f82,plain,(
% 1.26/0.52    spl8_2 <=> r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7)),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.26/0.52  fof(f89,plain,(
% 1.26/0.52    spl8_3 <=> sK6 = sK7),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.26/0.52  fof(f236,plain,(
% 1.26/0.52    spl8_32 <=> k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = k2_tmap_1(sK3,sK0,sK4,sK2)),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).
% 1.26/0.52  fof(f314,plain,(
% 1.26/0.52    ~r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK6) | (spl8_2 | ~spl8_3 | ~spl8_32)),
% 1.26/0.52    inference(forward_demodulation,[],[f313,f237])).
% 1.26/0.52  fof(f237,plain,(
% 1.26/0.52    k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = k2_tmap_1(sK3,sK0,sK4,sK2) | ~spl8_32),
% 1.26/0.52    inference(avatar_component_clause,[],[f236])).
% 1.26/0.52  fof(f313,plain,(
% 1.26/0.52    ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | (spl8_2 | ~spl8_3)),
% 1.26/0.52    inference(forward_demodulation,[],[f83,f90])).
% 1.26/0.52  fof(f90,plain,(
% 1.26/0.52    sK6 = sK7 | ~spl8_3),
% 1.26/0.52    inference(avatar_component_clause,[],[f89])).
% 1.26/0.52  fof(f83,plain,(
% 1.26/0.52    ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | spl8_2),
% 1.26/0.52    inference(avatar_component_clause,[],[f82])).
% 1.26/0.52  fof(f309,plain,(
% 1.26/0.52    ~spl8_4 | spl8_41),
% 1.26/0.52    inference(avatar_split_clause,[],[f301,f293,f93])).
% 1.26/0.52  fof(f293,plain,(
% 1.26/0.52    spl8_41 <=> m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_41])])).
% 1.26/0.52  fof(f301,plain,(
% 1.26/0.52    ~r1_tarski(sK5,u1_struct_0(sK2)) | spl8_41),
% 1.26/0.52    inference(resolution,[],[f294,f74])).
% 1.26/0.52  fof(f74,plain,(
% 1.26/0.52    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f40])).
% 1.26/0.52  fof(f40,plain,(
% 1.26/0.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.26/0.52    inference(nnf_transformation,[],[f1])).
% 1.26/0.52  fof(f1,axiom,(
% 1.26/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.26/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.26/0.52  fof(f294,plain,(
% 1.26/0.52    ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) | spl8_41),
% 1.26/0.52    inference(avatar_component_clause,[],[f293])).
% 1.26/0.52  fof(f295,plain,(
% 1.26/0.52    ~spl8_41 | ~spl8_10 | ~spl8_39),
% 1.26/0.52    inference(avatar_split_clause,[],[f290,f274,f117,f293])).
% 1.26/0.52  fof(f274,plain,(
% 1.26/0.52    spl8_39 <=> ! [X0] : (~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X0,sK3))),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).
% 1.26/0.52  fof(f290,plain,(
% 1.26/0.52    ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) | (~spl8_10 | ~spl8_39)),
% 1.26/0.52    inference(resolution,[],[f275,f118])).
% 1.26/0.52  fof(f118,plain,(
% 1.26/0.52    m1_pre_topc(sK2,sK3) | ~spl8_10),
% 1.26/0.52    inference(avatar_component_clause,[],[f117])).
% 1.26/0.52  fof(f275,plain,(
% 1.26/0.52    ( ! [X0] : (~m1_pre_topc(X0,sK3) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))) ) | ~spl8_39),
% 1.26/0.52    inference(avatar_component_clause,[],[f274])).
% 1.26/0.52  fof(f286,plain,(
% 1.26/0.52    ~spl8_14 | ~spl8_9 | ~spl8_18 | ~spl8_6 | ~spl8_38),
% 1.26/0.52    inference(avatar_split_clause,[],[f281,f268,f101,f149,f113,f133])).
% 1.26/0.52  fof(f133,plain,(
% 1.26/0.52    spl8_14 <=> m1_pre_topc(sK3,sK1)),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 1.26/0.52  fof(f113,plain,(
% 1.26/0.52    spl8_9 <=> m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 1.26/0.52  fof(f149,plain,(
% 1.26/0.52    spl8_18 <=> l1_pre_topc(sK1)),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 1.26/0.52  fof(f101,plain,(
% 1.26/0.52    spl8_6 <=> v3_pre_topc(sK5,sK1)),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 1.26/0.52  fof(f268,plain,(
% 1.26/0.52    spl8_38 <=> ! [X0] : (~v3_pre_topc(sK5,X0) | ~l1_pre_topc(X0) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(sK3,X0))),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).
% 1.26/0.52  fof(f281,plain,(
% 1.26/0.52    ~l1_pre_topc(sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_pre_topc(sK3,sK1) | (~spl8_6 | ~spl8_38)),
% 1.26/0.52    inference(resolution,[],[f269,f102])).
% 1.26/0.52  fof(f102,plain,(
% 1.26/0.52    v3_pre_topc(sK5,sK1) | ~spl8_6),
% 1.26/0.52    inference(avatar_component_clause,[],[f101])).
% 1.26/0.52  fof(f269,plain,(
% 1.26/0.52    ( ! [X0] : (~v3_pre_topc(sK5,X0) | ~l1_pre_topc(X0) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(sK3,X0)) ) | ~spl8_38),
% 1.26/0.52    inference(avatar_component_clause,[],[f268])).
% 1.26/0.52  fof(f276,plain,(
% 1.26/0.52    ~spl8_30 | spl8_39 | spl8_37),
% 1.26/0.52    inference(avatar_split_clause,[],[f271,f262,f274,f213])).
% 1.26/0.52  fof(f271,plain,(
% 1.26/0.52    ( ! [X0] : (~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X0,sK3) | ~l1_pre_topc(sK3)) ) | spl8_37),
% 1.26/0.52    inference(resolution,[],[f263,f65])).
% 1.26/0.52  fof(f65,plain,(
% 1.26/0.52    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f15])).
% 1.26/0.52  fof(f15,plain,(
% 1.26/0.52    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.26/0.52    inference(ennf_transformation,[],[f4])).
% 1.26/0.52  fof(f4,axiom,(
% 1.26/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 1.26/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).
% 1.26/0.52  fof(f263,plain,(
% 1.26/0.52    ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) | spl8_37),
% 1.26/0.52    inference(avatar_component_clause,[],[f262])).
% 1.26/0.52  fof(f270,plain,(
% 1.26/0.52    spl8_38 | ~spl8_37 | spl8_36),
% 1.26/0.52    inference(avatar_split_clause,[],[f266,f259,f262,f268])).
% 1.26/0.52  fof(f266,plain,(
% 1.26/0.52    ( ! [X0] : (~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) | ~v3_pre_topc(sK5,X0) | ~m1_pre_topc(sK3,X0) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | spl8_36),
% 1.26/0.52    inference(resolution,[],[f260,f75])).
% 1.26/0.52  fof(f75,plain,(
% 1.26/0.52    ( ! [X2,X0,X3] : (v3_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v3_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.26/0.52    inference(equality_resolution,[],[f66])).
% 1.26/0.52  fof(f66,plain,(
% 1.26/0.52    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f17])).
% 1.26/0.52  fof(f17,plain,(
% 1.26/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.26/0.52    inference(flattening,[],[f16])).
% 1.26/0.52  fof(f16,plain,(
% 1.26/0.52    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v3_pre_topc(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.26/0.52    inference(ennf_transformation,[],[f5])).
% 1.26/0.52  fof(f5,axiom,(
% 1.26/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v3_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v3_pre_topc(X3,X2)))))))),
% 1.26/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tops_2)).
% 1.26/0.52  fof(f260,plain,(
% 1.26/0.52    ~v3_pre_topc(sK5,sK3) | spl8_36),
% 1.26/0.52    inference(avatar_component_clause,[],[f259])).
% 1.26/0.52  fof(f264,plain,(
% 1.26/0.52    ~spl8_4 | ~spl8_36 | ~spl8_37 | ~spl8_5 | ~spl8_35),
% 1.26/0.52    inference(avatar_split_clause,[],[f256,f253,f97,f262,f259,f93])).
% 1.26/0.52  fof(f253,plain,(
% 1.26/0.52    spl8_35 <=> ! [X0] : (~r1_tarski(X0,u1_struct_0(sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~v3_pre_topc(X0,sK3) | ~r2_hidden(sK6,X0))),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).
% 1.26/0.52  fof(f256,plain,(
% 1.26/0.52    ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) | ~v3_pre_topc(sK5,sK3) | ~r1_tarski(sK5,u1_struct_0(sK2)) | (~spl8_5 | ~spl8_35)),
% 1.26/0.52    inference(resolution,[],[f254,f98])).
% 1.26/0.52  fof(f254,plain,(
% 1.26/0.52    ( ! [X0] : (~r2_hidden(sK6,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~v3_pre_topc(X0,sK3) | ~r1_tarski(X0,u1_struct_0(sK2))) ) | ~spl8_35),
% 1.26/0.52    inference(avatar_component_clause,[],[f253])).
% 1.26/0.52  fof(f255,plain,(
% 1.26/0.52    spl8_23 | ~spl8_22 | ~spl8_21 | spl8_15 | ~spl8_29 | ~spl8_30 | ~spl8_13 | ~spl8_12 | ~spl8_11 | spl8_17 | ~spl8_10 | ~spl8_8 | ~spl8_25 | spl8_35 | spl8_1 | ~spl8_34),
% 1.26/0.52    inference(avatar_split_clause,[],[f248,f245,f79,f253,f179,f109,f117,f145,f121,f125,f129,f213,f210,f137,f161,f165,f169])).
% 1.26/0.52  fof(f248,plain,(
% 1.26/0.52    ( ! [X0] : (r1_tmap_1(sK3,sK0,sK4,sK6) | ~r1_tarski(X0,u1_struct_0(sK2)) | ~r2_hidden(sK6,X0) | ~v3_pre_topc(X0,sK3) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_subset_1(sK6,u1_struct_0(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_pre_topc(sK2,sK3) | v2_struct_0(sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl8_34),
% 1.26/0.52    inference(resolution,[],[f246,f76])).
% 1.26/0.52  fof(f76,plain,(
% 1.26/0.52    ( ! [X6,X4,X2,X0,X3,X1] : (~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X6) | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X6,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.26/0.52    inference(equality_resolution,[],[f70])).
% 1.26/0.52  fof(f70,plain,(
% 1.26/0.52    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,X2,X5) | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | X5 != X6 | ~r1_tarski(X4,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f39])).
% 1.26/0.52  fof(f246,plain,(
% 1.26/0.52    r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK6) | ~spl8_34),
% 1.26/0.52    inference(avatar_component_clause,[],[f245])).
% 1.26/0.52  fof(f247,plain,(
% 1.26/0.52    spl8_34 | ~spl8_24 | ~spl8_32),
% 1.26/0.52    inference(avatar_split_clause,[],[f243,f236,f174,f245])).
% 1.26/0.52  fof(f174,plain,(
% 1.26/0.52    spl8_24 <=> r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).
% 1.26/0.52  fof(f243,plain,(
% 1.26/0.52    r1_tmap_1(sK2,sK0,k2_tmap_1(sK3,sK0,sK4,sK2),sK6) | (~spl8_24 | ~spl8_32)),
% 1.26/0.52    inference(superposition,[],[f175,f237])).
% 1.26/0.52  fof(f175,plain,(
% 1.26/0.52    r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | ~spl8_24),
% 1.26/0.52    inference(avatar_component_clause,[],[f174])).
% 1.26/0.52  fof(f239,plain,(
% 1.26/0.52    spl8_15 | ~spl8_29 | ~spl8_30 | spl8_23 | ~spl8_22 | ~spl8_21 | ~spl8_13 | ~spl8_12 | ~spl8_11 | ~spl8_10 | spl8_32 | ~spl8_28),
% 1.26/0.52    inference(avatar_split_clause,[],[f230,f206,f236,f117,f121,f125,f129,f161,f165,f169,f213,f210,f137])).
% 1.26/0.52  fof(f206,plain,(
% 1.26/0.52    spl8_28 <=> k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2))),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).
% 1.26/0.52  fof(f230,plain,(
% 1.26/0.52    k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = k2_tmap_1(sK3,sK0,sK4,sK2) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~spl8_28),
% 1.26/0.52    inference(superposition,[],[f68,f207])).
% 1.26/0.52  fof(f207,plain,(
% 1.26/0.52    k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)) | ~spl8_28),
% 1.26/0.52    inference(avatar_component_clause,[],[f206])).
% 1.26/0.52  fof(f68,plain,(
% 1.26/0.52    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f21])).
% 1.26/0.52  fof(f21,plain,(
% 1.26/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.26/0.52    inference(flattening,[],[f20])).
% 1.26/0.52  fof(f20,plain,(
% 1.26/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.26/0.52    inference(ennf_transformation,[],[f6])).
% 1.26/0.52  fof(f6,axiom,(
% 1.26/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 1.26/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).
% 1.26/0.52  fof(f228,plain,(
% 1.26/0.52    ~spl8_18 | ~spl8_14 | spl8_30),
% 1.26/0.52    inference(avatar_split_clause,[],[f225,f213,f133,f149])).
% 1.26/0.52  fof(f225,plain,(
% 1.26/0.52    ~l1_pre_topc(sK1) | (~spl8_14 | spl8_30)),
% 1.26/0.52    inference(resolution,[],[f224,f134])).
% 1.26/0.52  fof(f134,plain,(
% 1.26/0.52    m1_pre_topc(sK3,sK1) | ~spl8_14),
% 1.26/0.52    inference(avatar_component_clause,[],[f133])).
% 1.26/0.52  fof(f224,plain,(
% 1.26/0.52    ( ! [X0] : (~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0)) ) | spl8_30),
% 1.26/0.52    inference(resolution,[],[f214,f64])).
% 1.26/0.52  fof(f64,plain,(
% 1.26/0.52    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f14])).
% 1.26/0.52  fof(f14,plain,(
% 1.26/0.52    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.26/0.52    inference(ennf_transformation,[],[f3])).
% 1.26/0.52  fof(f3,axiom,(
% 1.26/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.26/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.26/0.52  fof(f214,plain,(
% 1.26/0.52    ~l1_pre_topc(sK3) | spl8_30),
% 1.26/0.52    inference(avatar_component_clause,[],[f213])).
% 1.26/0.52  fof(f223,plain,(
% 1.26/0.52    ~spl8_19 | ~spl8_18 | ~spl8_14 | spl8_29),
% 1.26/0.52    inference(avatar_split_clause,[],[f220,f210,f133,f149,f153])).
% 1.26/0.52  fof(f153,plain,(
% 1.26/0.52    spl8_19 <=> v2_pre_topc(sK1)),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 1.26/0.52  fof(f220,plain,(
% 1.26/0.52    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl8_14 | spl8_29)),
% 1.26/0.52    inference(resolution,[],[f219,f134])).
% 1.26/0.52  fof(f219,plain,(
% 1.26/0.52    ( ! [X0] : (~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | spl8_29),
% 1.26/0.52    inference(resolution,[],[f211,f71])).
% 1.26/0.52  fof(f71,plain,(
% 1.26/0.52    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f25])).
% 1.26/0.52  fof(f25,plain,(
% 1.26/0.52    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.26/0.52    inference(flattening,[],[f24])).
% 1.26/0.52  fof(f24,plain,(
% 1.26/0.52    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.26/0.52    inference(ennf_transformation,[],[f2])).
% 1.26/0.52  fof(f2,axiom,(
% 1.26/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 1.26/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).
% 1.26/0.52  fof(f211,plain,(
% 1.26/0.52    ~v2_pre_topc(sK3) | spl8_29),
% 1.26/0.52    inference(avatar_component_clause,[],[f210])).
% 1.26/0.52  fof(f208,plain,(
% 1.26/0.52    ~spl8_16 | spl8_28 | ~spl8_10 | ~spl8_27),
% 1.26/0.52    inference(avatar_split_clause,[],[f202,f196,f117,f206,f141])).
% 1.26/0.52  fof(f141,plain,(
% 1.26/0.52    spl8_16 <=> m1_pre_topc(sK2,sK1)),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 1.26/0.52  fof(f196,plain,(
% 1.26/0.52    spl8_27 <=> ! [X0] : (~m1_pre_topc(X0,sK3) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) = k3_tmap_1(sK1,sK0,sK3,X0,sK4) | ~m1_pre_topc(X0,sK1))),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).
% 1.26/0.52  fof(f202,plain,(
% 1.26/0.52    k3_tmap_1(sK1,sK0,sK3,sK2,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK1) | (~spl8_10 | ~spl8_27)),
% 1.26/0.52    inference(resolution,[],[f197,f118])).
% 1.26/0.52  fof(f197,plain,(
% 1.26/0.52    ( ! [X0] : (~m1_pre_topc(X0,sK3) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) = k3_tmap_1(sK1,sK0,sK3,X0,sK4) | ~m1_pre_topc(X0,sK1)) ) | ~spl8_27),
% 1.26/0.52    inference(avatar_component_clause,[],[f196])).
% 1.26/0.52  fof(f201,plain,(
% 1.26/0.52    spl8_27 | ~spl8_18 | ~spl8_19 | spl8_20 | ~spl8_14 | ~spl8_26),
% 1.26/0.52    inference(avatar_split_clause,[],[f192,f188,f133,f157,f153,f149,f196])).
% 1.26/0.52  fof(f157,plain,(
% 1.26/0.52    spl8_20 <=> v2_struct_0(sK1)),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 1.26/0.52  fof(f188,plain,(
% 1.26/0.52    spl8_26 <=> ! [X1,X0] : (~m1_pre_topc(X0,sK3) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(sK3,X1) | ~m1_pre_topc(X0,X1) | k3_tmap_1(X1,sK0,sK3,X0,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)))),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).
% 1.26/0.52  fof(f192,plain,(
% 1.26/0.52    ( ! [X0] : (v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_pre_topc(X0,sK3) | ~m1_pre_topc(X0,sK1) | k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) = k3_tmap_1(sK1,sK0,sK3,X0,sK4)) ) | (~spl8_14 | ~spl8_26)),
% 1.26/0.52    inference(resolution,[],[f189,f134])).
% 1.26/0.52  fof(f189,plain,(
% 1.26/0.52    ( ! [X0,X1] : (~m1_pre_topc(sK3,X1) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X0,sK3) | ~m1_pre_topc(X0,X1) | k3_tmap_1(X1,sK0,sK3,X0,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0))) ) | ~spl8_26),
% 1.26/0.52    inference(avatar_component_clause,[],[f188])).
% 1.26/0.52  fof(f191,plain,(
% 1.26/0.52    spl8_23 | ~spl8_22 | ~spl8_21 | spl8_26 | ~spl8_11 | ~spl8_12 | ~spl8_13),
% 1.26/0.52    inference(avatar_split_clause,[],[f183,f129,f125,f121,f188,f161,f165,f169])).
% 1.26/0.52  fof(f183,plain,(
% 1.26/0.52    ( ! [X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~m1_pre_topc(X0,sK3) | k3_tmap_1(X1,sK0,sK3,X0,sK4) = k2_partfun1(u1_struct_0(sK3),u1_struct_0(sK0),sK4,u1_struct_0(X0)) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK3,X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | (~spl8_12 | ~spl8_13)),
% 1.26/0.52    inference(resolution,[],[f182,f126])).
% 1.26/0.52  fof(f182,plain,(
% 1.26/0.52    ( ! [X2,X0,X3,X1] : (~v1_funct_2(sK4,u1_struct_0(X1),u1_struct_0(X2)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X0,X1) | k3_tmap_1(X3,X2,X1,X0,sK4) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),sK4,u1_struct_0(X0)) | ~m1_pre_topc(X0,X3) | ~m1_pre_topc(X1,X3) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3)) ) | ~spl8_13),
% 1.26/0.52    inference(resolution,[],[f67,f130])).
% 1.26/0.52  fof(f67,plain,(
% 1.26/0.52    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f19])).
% 1.26/0.52  fof(f19,plain,(
% 1.26/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.26/0.52    inference(flattening,[],[f18])).
% 1.26/0.52  fof(f18,plain,(
% 1.26/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.26/0.52    inference(ennf_transformation,[],[f7])).
% 1.26/0.52  fof(f7,axiom,(
% 1.26/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 1.26/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).
% 1.26/0.52  fof(f181,plain,(
% 1.26/0.52    spl8_25 | ~spl8_3 | ~spl8_7),
% 1.26/0.52    inference(avatar_split_clause,[],[f177,f105,f89,f179])).
% 1.26/0.52  fof(f105,plain,(
% 1.26/0.52    spl8_7 <=> m1_subset_1(sK7,u1_struct_0(sK2))),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 1.26/0.52  fof(f177,plain,(
% 1.26/0.52    m1_subset_1(sK6,u1_struct_0(sK2)) | (~spl8_3 | ~spl8_7)),
% 1.26/0.52    inference(superposition,[],[f106,f90])).
% 1.26/0.52  fof(f106,plain,(
% 1.26/0.52    m1_subset_1(sK7,u1_struct_0(sK2)) | ~spl8_7),
% 1.26/0.52    inference(avatar_component_clause,[],[f105])).
% 1.26/0.52  fof(f176,plain,(
% 1.26/0.52    spl8_24 | ~spl8_2 | ~spl8_3),
% 1.26/0.52    inference(avatar_split_clause,[],[f172,f89,f82,f174])).
% 1.26/0.52  fof(f172,plain,(
% 1.26/0.52    r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | (~spl8_2 | ~spl8_3)),
% 1.26/0.52    inference(forward_demodulation,[],[f86,f90])).
% 1.26/0.52  fof(f86,plain,(
% 1.26/0.52    r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | ~spl8_2),
% 1.26/0.52    inference(avatar_component_clause,[],[f82])).
% 1.26/0.52  fof(f171,plain,(
% 1.26/0.52    ~spl8_23),
% 1.26/0.52    inference(avatar_split_clause,[],[f41,f169])).
% 1.26/0.52  fof(f41,plain,(
% 1.26/0.52    ~v2_struct_0(sK0)),
% 1.26/0.52    inference(cnf_transformation,[],[f38])).
% 1.26/0.52  fof(f38,plain,(
% 1.26/0.52    ((((((((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK0,sK4,sK6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | r1_tmap_1(sK3,sK0,sK4,sK6)) & sK6 = sK7 & r1_tarski(sK5,u1_struct_0(sK2)) & r2_hidden(sK6,sK5) & v3_pre_topc(sK5,sK1) & m1_subset_1(sK7,u1_struct_0(sK2))) & m1_subset_1(sK6,u1_struct_0(sK3))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.26/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f29,f37,f36,f35,f34,f33,f32,f31,f30])).
% 1.26/0.52  fof(f30,plain,(
% 1.26/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X7) | ~r1_tmap_1(X3,sK0,X4,X6)) & (r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X7) | r1_tmap_1(X3,sK0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.26/0.52    introduced(choice_axiom,[])).
% 1.26/0.52  fof(f31,plain,(
% 1.26/0.52    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X7) | ~r1_tmap_1(X3,sK0,X4,X6)) & (r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X7) | r1_tmap_1(X3,sK0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,sK0,k3_tmap_1(sK1,sK0,X3,X2,X4),X7) | ~r1_tmap_1(X3,sK0,X4,X6)) & (r1_tmap_1(X2,sK0,k3_tmap_1(sK1,sK0,X3,X2,X4),X7) | r1_tmap_1(X3,sK0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 1.26/0.52    introduced(choice_axiom,[])).
% 1.26/0.52  fof(f32,plain,(
% 1.26/0.52    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,sK0,k3_tmap_1(sK1,sK0,X3,X2,X4),X7) | ~r1_tmap_1(X3,sK0,X4,X6)) & (r1_tmap_1(X2,sK0,k3_tmap_1(sK1,sK0,X3,X2,X4),X7) | r1_tmap_1(X3,sK0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,X3,sK2,X4),X7) | ~r1_tmap_1(X3,sK0,X4,X6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,X3,sK2,X4),X7) | r1_tmap_1(X3,sK0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(sK2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK1) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2))),
% 1.26/0.52    introduced(choice_axiom,[])).
% 1.26/0.52  fof(f33,plain,(
% 1.26/0.52    ? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,X3,sK2,X4),X7) | ~r1_tmap_1(X3,sK0,X4,X6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,X3,sK2,X4),X7) | r1_tmap_1(X3,sK0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(sK2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK1) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(sK2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X4),X7) | ~r1_tmap_1(sK3,sK0,X4,X6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X4),X7) | r1_tmap_1(sK3,sK0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(sK2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK1) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(sK2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3))),
% 1.26/0.52    introduced(choice_axiom,[])).
% 1.26/0.52  fof(f34,plain,(
% 1.26/0.52    ? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X4),X7) | ~r1_tmap_1(sK3,sK0,X4,X6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X4),X7) | r1_tmap_1(sK3,sK0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(sK2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK1) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(sK2,sK3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK0)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK0,sK4,X6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7) | r1_tmap_1(sK3,sK0,sK4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(sK2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK1) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_pre_topc(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) & v1_funct_1(sK4))),
% 1.26/0.52    introduced(choice_axiom,[])).
% 1.26/0.52  fof(f35,plain,(
% 1.26/0.52    ? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK0,sK4,X6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7) | r1_tmap_1(sK3,sK0,sK4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(sK2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,sK1) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK1)))) => (? [X6] : (? [X7] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK0,sK4,X6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7) | r1_tmap_1(sK3,sK0,sK4,X6)) & X6 = X7 & r1_tarski(sK5,u1_struct_0(sK2)) & r2_hidden(X6,sK5) & v3_pre_topc(sK5,sK1) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(sK3))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1))))),
% 1.26/0.52    introduced(choice_axiom,[])).
% 1.26/0.52  fof(f36,plain,(
% 1.26/0.52    ? [X6] : (? [X7] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK0,sK4,X6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7) | r1_tmap_1(sK3,sK0,sK4,X6)) & X6 = X7 & r1_tarski(sK5,u1_struct_0(sK2)) & r2_hidden(X6,sK5) & v3_pre_topc(sK5,sK1) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(X6,u1_struct_0(sK3))) => (? [X7] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK0,sK4,sK6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7) | r1_tmap_1(sK3,sK0,sK4,sK6)) & sK6 = X7 & r1_tarski(sK5,u1_struct_0(sK2)) & r2_hidden(sK6,sK5) & v3_pre_topc(sK5,sK1) & m1_subset_1(X7,u1_struct_0(sK2))) & m1_subset_1(sK6,u1_struct_0(sK3)))),
% 1.26/0.52    introduced(choice_axiom,[])).
% 1.26/0.52  fof(f37,plain,(
% 1.26/0.52    ? [X7] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7) | ~r1_tmap_1(sK3,sK0,sK4,sK6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X7) | r1_tmap_1(sK3,sK0,sK4,sK6)) & sK6 = X7 & r1_tarski(sK5,u1_struct_0(sK2)) & r2_hidden(sK6,sK5) & v3_pre_topc(sK5,sK1) & m1_subset_1(X7,u1_struct_0(sK2))) => ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK0,sK4,sK6)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | r1_tmap_1(sK3,sK0,sK4,sK6)) & sK6 = sK7 & r1_tarski(sK5,u1_struct_0(sK2)) & r2_hidden(sK6,sK5) & v3_pre_topc(sK5,sK1) & m1_subset_1(sK7,u1_struct_0(sK2)))),
% 1.26/0.52    introduced(choice_axiom,[])).
% 1.26/0.52  fof(f29,plain,(
% 1.26/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.26/0.52    inference(flattening,[],[f28])).
% 1.26/0.52  fof(f28,plain,(
% 1.26/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : (((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | ~r1_tmap_1(X3,X0,X4,X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7) | r1_tmap_1(X3,X0,X4,X6))) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.26/0.52    inference(nnf_transformation,[],[f13])).
% 1.26/0.52  fof(f13,plain,(
% 1.26/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (? [X7] : ((r1_tmap_1(X3,X0,X4,X6) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)) & X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.26/0.52    inference(flattening,[],[f12])).
% 1.26/0.52  fof(f12,plain,(
% 1.26/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (? [X7] : (((r1_tmap_1(X3,X0,X4,X6) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7)) & (X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1))) & m1_subset_1(X7,u1_struct_0(X2))) & m1_subset_1(X6,u1_struct_0(X3))) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & m1_pre_topc(X2,X3)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X1) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.26/0.52    inference(ennf_transformation,[],[f11])).
% 1.26/0.52  fof(f11,negated_conjecture,(
% 1.26/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1)) => (r1_tmap_1(X3,X0,X4,X6) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7))))))))))))),
% 1.26/0.52    inference(negated_conjecture,[],[f10])).
% 1.26/0.52  fof(f10,conjecture,(
% 1.26/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => (m1_pre_topc(X2,X3) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X2)) => ((X6 = X7 & r1_tarski(X5,u1_struct_0(X2)) & r2_hidden(X6,X5) & v3_pre_topc(X5,X1)) => (r1_tmap_1(X3,X0,X4,X6) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X7))))))))))))),
% 1.26/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_tmap_1)).
% 1.26/0.52  fof(f167,plain,(
% 1.26/0.52    spl8_22),
% 1.26/0.52    inference(avatar_split_clause,[],[f42,f165])).
% 1.26/0.52  fof(f42,plain,(
% 1.26/0.52    v2_pre_topc(sK0)),
% 1.26/0.52    inference(cnf_transformation,[],[f38])).
% 1.26/0.52  fof(f163,plain,(
% 1.26/0.52    spl8_21),
% 1.26/0.52    inference(avatar_split_clause,[],[f43,f161])).
% 1.26/0.52  fof(f43,plain,(
% 1.26/0.52    l1_pre_topc(sK0)),
% 1.26/0.52    inference(cnf_transformation,[],[f38])).
% 1.26/0.52  fof(f159,plain,(
% 1.26/0.52    ~spl8_20),
% 1.26/0.52    inference(avatar_split_clause,[],[f44,f157])).
% 1.26/0.52  fof(f44,plain,(
% 1.26/0.52    ~v2_struct_0(sK1)),
% 1.26/0.52    inference(cnf_transformation,[],[f38])).
% 1.26/0.52  fof(f155,plain,(
% 1.26/0.52    spl8_19),
% 1.26/0.52    inference(avatar_split_clause,[],[f45,f153])).
% 1.26/0.52  fof(f45,plain,(
% 1.26/0.52    v2_pre_topc(sK1)),
% 1.26/0.52    inference(cnf_transformation,[],[f38])).
% 1.26/0.52  fof(f151,plain,(
% 1.26/0.52    spl8_18),
% 1.26/0.52    inference(avatar_split_clause,[],[f46,f149])).
% 1.26/0.52  fof(f46,plain,(
% 1.26/0.52    l1_pre_topc(sK1)),
% 1.26/0.52    inference(cnf_transformation,[],[f38])).
% 1.26/0.52  fof(f147,plain,(
% 1.26/0.52    ~spl8_17),
% 1.26/0.52    inference(avatar_split_clause,[],[f47,f145])).
% 1.26/0.52  fof(f47,plain,(
% 1.26/0.52    ~v2_struct_0(sK2)),
% 1.26/0.52    inference(cnf_transformation,[],[f38])).
% 1.26/0.52  fof(f143,plain,(
% 1.26/0.52    spl8_16),
% 1.26/0.52    inference(avatar_split_clause,[],[f48,f141])).
% 1.26/0.52  fof(f48,plain,(
% 1.26/0.52    m1_pre_topc(sK2,sK1)),
% 1.26/0.52    inference(cnf_transformation,[],[f38])).
% 1.26/0.52  fof(f139,plain,(
% 1.26/0.52    ~spl8_15),
% 1.26/0.52    inference(avatar_split_clause,[],[f49,f137])).
% 1.26/0.52  fof(f49,plain,(
% 1.26/0.52    ~v2_struct_0(sK3)),
% 1.26/0.52    inference(cnf_transformation,[],[f38])).
% 1.26/0.52  fof(f135,plain,(
% 1.26/0.52    spl8_14),
% 1.26/0.52    inference(avatar_split_clause,[],[f50,f133])).
% 1.26/0.52  fof(f50,plain,(
% 1.26/0.52    m1_pre_topc(sK3,sK1)),
% 1.26/0.52    inference(cnf_transformation,[],[f38])).
% 1.26/0.52  fof(f131,plain,(
% 1.26/0.52    spl8_13),
% 1.26/0.52    inference(avatar_split_clause,[],[f51,f129])).
% 1.26/0.52  fof(f51,plain,(
% 1.26/0.52    v1_funct_1(sK4)),
% 1.26/0.52    inference(cnf_transformation,[],[f38])).
% 1.26/0.52  fof(f127,plain,(
% 1.26/0.52    spl8_12),
% 1.26/0.52    inference(avatar_split_clause,[],[f52,f125])).
% 1.26/0.52  fof(f52,plain,(
% 1.26/0.52    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))),
% 1.26/0.52    inference(cnf_transformation,[],[f38])).
% 1.26/0.52  fof(f123,plain,(
% 1.26/0.52    spl8_11),
% 1.26/0.52    inference(avatar_split_clause,[],[f53,f121])).
% 1.26/0.52  fof(f53,plain,(
% 1.26/0.52    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))),
% 1.26/0.52    inference(cnf_transformation,[],[f38])).
% 1.26/0.52  fof(f119,plain,(
% 1.26/0.52    spl8_10),
% 1.26/0.52    inference(avatar_split_clause,[],[f54,f117])).
% 1.26/0.52  fof(f54,plain,(
% 1.26/0.52    m1_pre_topc(sK2,sK3)),
% 1.26/0.52    inference(cnf_transformation,[],[f38])).
% 1.26/0.52  fof(f115,plain,(
% 1.26/0.52    spl8_9),
% 1.26/0.52    inference(avatar_split_clause,[],[f55,f113])).
% 1.26/0.52  fof(f55,plain,(
% 1.26/0.52    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.26/0.52    inference(cnf_transformation,[],[f38])).
% 1.26/0.52  fof(f111,plain,(
% 1.26/0.52    spl8_8),
% 1.26/0.52    inference(avatar_split_clause,[],[f56,f109])).
% 1.26/0.52  fof(f56,plain,(
% 1.26/0.52    m1_subset_1(sK6,u1_struct_0(sK3))),
% 1.26/0.52    inference(cnf_transformation,[],[f38])).
% 1.26/0.52  fof(f107,plain,(
% 1.26/0.52    spl8_7),
% 1.26/0.52    inference(avatar_split_clause,[],[f57,f105])).
% 1.26/0.52  fof(f57,plain,(
% 1.26/0.52    m1_subset_1(sK7,u1_struct_0(sK2))),
% 1.26/0.52    inference(cnf_transformation,[],[f38])).
% 1.26/0.52  fof(f103,plain,(
% 1.26/0.52    spl8_6),
% 1.26/0.52    inference(avatar_split_clause,[],[f58,f101])).
% 1.26/0.52  fof(f58,plain,(
% 1.26/0.52    v3_pre_topc(sK5,sK1)),
% 1.26/0.52    inference(cnf_transformation,[],[f38])).
% 1.26/0.52  fof(f99,plain,(
% 1.26/0.52    spl8_5),
% 1.26/0.52    inference(avatar_split_clause,[],[f59,f97])).
% 1.26/0.52  fof(f59,plain,(
% 1.26/0.52    r2_hidden(sK6,sK5)),
% 1.26/0.52    inference(cnf_transformation,[],[f38])).
% 1.26/0.52  fof(f95,plain,(
% 1.26/0.52    spl8_4),
% 1.26/0.52    inference(avatar_split_clause,[],[f60,f93])).
% 1.26/0.52  fof(f60,plain,(
% 1.26/0.52    r1_tarski(sK5,u1_struct_0(sK2))),
% 1.26/0.52    inference(cnf_transformation,[],[f38])).
% 1.26/0.52  fof(f91,plain,(
% 1.26/0.52    spl8_3),
% 1.26/0.52    inference(avatar_split_clause,[],[f61,f89])).
% 1.26/0.52  fof(f61,plain,(
% 1.26/0.52    sK6 = sK7),
% 1.26/0.52    inference(cnf_transformation,[],[f38])).
% 1.26/0.52  fof(f87,plain,(
% 1.26/0.52    spl8_1 | spl8_2),
% 1.26/0.52    inference(avatar_split_clause,[],[f62,f82,f79])).
% 1.26/0.52  fof(f62,plain,(
% 1.26/0.52    r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | r1_tmap_1(sK3,sK0,sK4,sK6)),
% 1.26/0.52    inference(cnf_transformation,[],[f38])).
% 1.26/0.52  fof(f84,plain,(
% 1.26/0.52    ~spl8_1 | ~spl8_2),
% 1.26/0.52    inference(avatar_split_clause,[],[f63,f82,f79])).
% 1.26/0.52  fof(f63,plain,(
% 1.26/0.52    ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK7) | ~r1_tmap_1(sK3,sK0,sK4,sK6)),
% 1.26/0.52    inference(cnf_transformation,[],[f38])).
% 1.26/0.52  % SZS output end Proof for theBenchmark
% 1.26/0.52  % (25046)------------------------------
% 1.26/0.52  % (25046)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.52  % (25046)Termination reason: Refutation
% 1.26/0.52  
% 1.26/0.52  % (25046)Memory used [KB]: 11001
% 1.26/0.52  % (25046)Time elapsed: 0.046 s
% 1.26/0.52  % (25046)------------------------------
% 1.26/0.52  % (25046)------------------------------
% 1.26/0.52  % (25039)Success in time 0.161 s
%------------------------------------------------------------------------------
