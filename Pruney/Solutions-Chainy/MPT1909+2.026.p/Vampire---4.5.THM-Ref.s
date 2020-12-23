%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  175 ( 390 expanded)
%              Number of leaves         :   48 ( 160 expanded)
%              Depth                    :   11
%              Number of atoms          :  545 (1819 expanded)
%              Number of equality atoms :   66 ( 280 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f420,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f89,f94,f99,f104,f109,f114,f119,f124,f129,f134,f139,f144,f149,f154,f159,f172,f199,f244,f268,f273,f282,f287,f292,f293,f298,f301,f314,f333,f346,f351,f385,f392])).

fof(f392,plain,
    ( ~ spl7_44
    | spl7_45
    | ~ spl7_37
    | ~ spl7_49 ),
    inference(avatar_split_clause,[],[f386,f382,f296,f348,f343])).

fof(f343,plain,
    ( spl7_44
  <=> m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f348,plain,
    ( spl7_45
  <=> k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK0),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).

fof(f296,plain,
    ( spl7_37
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).

fof(f382,plain,
    ( spl7_49
  <=> m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_49])])).

fof(f386,plain,
    ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK0),sK4))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_37
    | ~ spl7_49 ),
    inference(resolution,[],[f384,f297])).

fof(f297,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_37 ),
    inference(avatar_component_clause,[],[f296])).

fof(f384,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_49 ),
    inference(avatar_component_clause,[],[f382])).

fof(f385,plain,
    ( spl7_49
    | ~ spl7_35
    | ~ spl7_36 ),
    inference(avatar_split_clause,[],[f380,f289,f284,f382])).

fof(f284,plain,
    ( spl7_35
  <=> m1_subset_1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f289,plain,
    ( spl7_36
  <=> k6_domain_1(u1_struct_0(sK0),sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f380,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_35
    | ~ spl7_36 ),
    inference(forward_demodulation,[],[f286,f291])).

fof(f291,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | ~ spl7_36 ),
    inference(avatar_component_clause,[],[f289])).

fof(f286,plain,
    ( m1_subset_1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_35 ),
    inference(avatar_component_clause,[],[f284])).

fof(f351,plain,
    ( ~ spl7_45
    | spl7_14
    | ~ spl7_42 ),
    inference(avatar_split_clause,[],[f336,f330,f151,f348])).

fof(f151,plain,
    ( spl7_14
  <=> k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f330,plain,
    ( spl7_42
  <=> k6_domain_1(u1_struct_0(sK0),sK4) = k6_domain_1(u1_struct_0(sK1),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).

fof(f336,plain,
    ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK0),sK4))
    | spl7_14
    | ~ spl7_42 ),
    inference(backward_demodulation,[],[f153,f332])).

fof(f332,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK4) = k6_domain_1(u1_struct_0(sK1),sK4)
    | ~ spl7_42 ),
    inference(avatar_component_clause,[],[f330])).

fof(f153,plain,
    ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK4))
    | spl7_14 ),
    inference(avatar_component_clause,[],[f151])).

fof(f346,plain,
    ( spl7_44
    | ~ spl7_39
    | ~ spl7_42 ),
    inference(avatar_split_clause,[],[f335,f330,f311,f343])).

fof(f311,plain,
    ( spl7_39
  <=> m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK4),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).

fof(f335,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_39
    | ~ spl7_42 ),
    inference(backward_demodulation,[],[f313,f332])).

fof(f313,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK4),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_39 ),
    inference(avatar_component_clause,[],[f311])).

fof(f333,plain,
    ( spl7_42
    | ~ spl7_33
    | ~ spl7_36 ),
    inference(avatar_split_clause,[],[f328,f289,f270,f330])).

fof(f270,plain,
    ( spl7_33
  <=> k6_domain_1(u1_struct_0(sK1),sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f328,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK4) = k6_domain_1(u1_struct_0(sK1),sK4)
    | ~ spl7_33
    | ~ spl7_36 ),
    inference(backward_demodulation,[],[f272,f291])).

fof(f272,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | ~ spl7_33 ),
    inference(avatar_component_clause,[],[f270])).

fof(f314,plain,
    ( spl7_39
    | ~ spl7_28
    | ~ spl7_33 ),
    inference(avatar_split_clause,[],[f309,f270,f235,f311])).

fof(f235,plain,
    ( spl7_28
  <=> m1_subset_1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f309,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK4),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_28
    | ~ spl7_33 ),
    inference(forward_demodulation,[],[f237,f272])).

fof(f237,plain,
    ( m1_subset_1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f235])).

fof(f301,plain,
    ( spl7_28
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f299,f174,f235])).

fof(f174,plain,
    ( spl7_18
  <=> r2_hidden(sK4,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f299,plain,
    ( m1_subset_1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_18 ),
    inference(resolution,[],[f176,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1)) ) ),
    inference(definition_unfolding,[],[f64,f78])).

fof(f78,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f52,f77])).

fof(f77,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f63,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f68,f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f69,f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f70,f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f71,f72])).

fof(f72,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f69,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f68,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f63,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f52,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

% (23425)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% (23426)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% (23427)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% (23442)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% (23435)Refutation not found, incomplete strategy% (23435)------------------------------
% (23435)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (23435)Termination reason: Refutation not found, incomplete strategy

% (23435)Memory used [KB]: 1791
% (23435)Time elapsed: 0.129 s
% (23435)------------------------------
% (23435)------------------------------
fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(f176,plain,
    ( r2_hidden(sK4,u1_struct_0(sK0))
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f174])).

fof(f298,plain,
    ( spl7_37
    | ~ spl7_8
    | spl7_4
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_5
    | ~ spl7_6
    | spl7_7
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f294,f126,f96,f91,f86,f116,f111,f106,f141,f136,f131,f101,f121,f296])).

fof(f121,plain,
    ( spl7_8
  <=> v3_borsuk_1(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f101,plain,
    ( spl7_4
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f131,plain,
    ( spl7_10
  <=> v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f136,plain,
    ( spl7_11
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f141,plain,
    ( spl7_12
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f106,plain,
    ( spl7_5
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f111,plain,
    ( spl7_6
  <=> v4_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f116,plain,
    ( spl7_7
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f86,plain,
    ( spl7_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f91,plain,
    ( spl7_2
  <=> v3_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f96,plain,
    ( spl7_3
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f126,plain,
    ( spl7_9
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f294,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ v3_tdlat_3(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v4_tex_2(sK1,sK0)
        | ~ m1_pre_topc(sK1,sK0)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | v2_struct_0(sK0)
        | ~ v3_borsuk_1(sK2,sK0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) )
    | ~ spl7_9 ),
    inference(resolution,[],[f83,f128])).

fof(f128,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f126])).

fof(f83,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v5_pre_topc(X2,X0,X1)
      | v2_struct_0(X0)
      | ~ v3_borsuk_1(X2,X0,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X4) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v3_borsuk_1(X2,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | X3 != X4
      | k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4)
                      | X3 != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ v3_borsuk_1(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v5_pre_topc(X2,X0,X1)
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v4_tex_2(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4)
                      | X3 != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ v3_borsuk_1(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v5_pre_topc(X2,X0,X1)
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v4_tex_2(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v4_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v5_pre_topc(X2,X0,X1)
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v3_borsuk_1(X2,X0,X1)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                       => ( X3 = X4
                         => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tex_2)).

fof(f293,plain,
    ( ~ spl7_19
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f192,f174,f178])).

fof(f178,plain,
    ( spl7_19
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f192,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl7_18 ),
    inference(resolution,[],[f176,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

% (23431)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
fof(f292,plain,
    ( spl7_36
    | spl7_19
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f259,f156,f178,f289])).

fof(f156,plain,
    ( spl7_15
  <=> m1_subset_1(sK4,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f259,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k6_domain_1(u1_struct_0(sK0),sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | ~ spl7_15 ),
    inference(resolution,[],[f82,f158])).

fof(f158,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f156])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | k6_domain_1(X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ) ),
    inference(definition_unfolding,[],[f67,f78])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f287,plain,
    ( spl7_35
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f280,f165,f284])).

fof(f165,plain,
    ( spl7_16
  <=> r2_hidden(sK4,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f280,plain,
    ( m1_subset_1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_16 ),
    inference(resolution,[],[f167,f81])).

fof(f167,plain,
    ( r2_hidden(sK4,u1_struct_0(sK1))
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f165])).

fof(f282,plain,
    ( spl7_18
    | ~ spl7_16
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f279,f196,f165,f174])).

fof(f196,plain,
    ( spl7_22
  <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f279,plain,
    ( r2_hidden(sK4,u1_struct_0(sK0))
    | ~ spl7_16
    | ~ spl7_22 ),
    inference(resolution,[],[f167,f200])).

fof(f200,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK1))
        | r2_hidden(X0,u1_struct_0(sK0)) )
    | ~ spl7_22 ),
    inference(resolution,[],[f198,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f198,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f196])).

fof(f273,plain,
    ( spl7_33
    | spl7_17
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f258,f146,f169,f270])).

fof(f169,plain,
    ( spl7_17
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f146,plain,
    ( spl7_13
  <=> m1_subset_1(sK4,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f258,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | k6_domain_1(u1_struct_0(sK1),sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | ~ spl7_13 ),
    inference(resolution,[],[f82,f148])).

fof(f148,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f146])).

fof(f268,plain,
    ( ~ spl7_6
    | spl7_29
    | spl7_4
    | ~ spl7_5
    | ~ spl7_1
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f267,f196,f86,f106,f101,f241,f111])).

fof(f241,plain,
    ( spl7_29
  <=> v3_tex_2(u1_struct_0(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f267,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | v3_tex_2(u1_struct_0(sK1),sK0)
    | ~ v4_tex_2(sK1,sK0)
    | ~ spl7_22 ),
    inference(resolution,[],[f84,f198])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0)
      | v3_tex_2(u1_struct_0(X1),X0)
      | ~ v4_tex_2(X1,X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | v3_tex_2(X2,X0)
      | ~ v4_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tex_2(X1,X0)
          <=> ! [X2] :
                ( v3_tex_2(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tex_2(X1,X0)
          <=> ! [X2] :
                ( v3_tex_2(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v4_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v3_tex_2(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_tex_2)).

fof(f244,plain,
    ( ~ spl7_29
    | spl7_4
    | ~ spl7_17
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f239,f196,f96,f86,f169,f101,f241])).

fof(f239,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | ~ v3_tex_2(u1_struct_0(sK1),sK0)
    | ~ spl7_22 ),
    inference(resolution,[],[f56,f198])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_xboole_0(X1)
      | v2_struct_0(X0)
      | ~ v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => ~ v3_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).

fof(f199,plain,
    ( spl7_22
    | ~ spl7_1
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f194,f106,f86,f196])).

% (23425)Refutation not found, incomplete strategy% (23425)------------------------------
% (23425)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (23425)Termination reason: Refutation not found, incomplete strategy

% (23425)Memory used [KB]: 10746
% (23425)Time elapsed: 0.130 s
% (23425)------------------------------
% (23425)------------------------------
fof(f194,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_5 ),
    inference(resolution,[],[f53,f108])).

fof(f108,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f106])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f172,plain,
    ( spl7_16
    | spl7_17
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f161,f146,f169,f165])).

fof(f161,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | r2_hidden(sK4,u1_struct_0(sK1))
    | ~ spl7_13 ),
    inference(resolution,[],[f65,f148])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f159,plain,(
    spl7_15 ),
    inference(avatar_split_clause,[],[f36,f156])).

fof(f36,plain,(
    m1_subset_1(sK4,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4))
                      & X3 = X4
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & v3_borsuk_1(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v5_pre_topc(X2,X0,X1)
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,X0)
          & v4_tex_2(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4))
                      & X3 = X4
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & v3_borsuk_1(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v5_pre_topc(X2,X0,X1)
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & m1_pre_topc(X1,X0)
          & v4_tex_2(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & v4_tex_2(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v5_pre_topc(X2,X0,X1)
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( v3_borsuk_1(X2,X0,X1)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X1))
                     => ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( X3 = X4
                           => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v4_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v5_pre_topc(X2,X0,X1)
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v3_borsuk_1(X2,X0,X1)
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ( X3 = X4
                         => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tex_2)).

fof(f154,plain,(
    ~ spl7_14 ),
    inference(avatar_split_clause,[],[f80,f151])).

fof(f80,plain,(
    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK4)) ),
    inference(definition_unfolding,[],[f38,f37])).

fof(f37,plain,(
    sK3 = sK4 ),
    inference(cnf_transformation,[],[f21])).

fof(f38,plain,(
    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) ),
    inference(cnf_transformation,[],[f21])).

fof(f149,plain,(
    spl7_13 ),
    inference(avatar_split_clause,[],[f79,f146])).

fof(f79,plain,(
    m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(definition_unfolding,[],[f39,f37])).

fof(f39,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f144,plain,(
    spl7_12 ),
    inference(avatar_split_clause,[],[f40,f141])).

fof(f40,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f139,plain,(
    spl7_11 ),
    inference(avatar_split_clause,[],[f41,f136])).

fof(f41,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f134,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f42,f131])).

fof(f42,plain,(
    v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f129,plain,(
    spl7_9 ),
    inference(avatar_split_clause,[],[f43,f126])).

fof(f43,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f21])).

fof(f124,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f44,f121])).

fof(f44,plain,(
    v3_borsuk_1(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f119,plain,(
    ~ spl7_7 ),
    inference(avatar_split_clause,[],[f45,f116])).

fof(f45,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f114,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f46,f111])).

fof(f46,plain,(
    v4_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f109,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f47,f106])).

fof(f47,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f104,plain,(
    ~ spl7_4 ),
    inference(avatar_split_clause,[],[f48,f101])).

fof(f48,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f99,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f49,f96])).

fof(f49,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f94,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f50,f91])).

fof(f50,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f89,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f51,f86])).

fof(f51,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:32:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (23422)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.50  % (23430)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.51  % (23430)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (23435)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.51  % (23416)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (23414)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (23420)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (23428)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (23436)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (23438)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.51  % (23433)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.52  % (23415)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (23417)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (23413)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (23418)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (23432)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.52  % (23419)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (23443)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.52  % (23421)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f420,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f89,f94,f99,f104,f109,f114,f119,f124,f129,f134,f139,f144,f149,f154,f159,f172,f199,f244,f268,f273,f282,f287,f292,f293,f298,f301,f314,f333,f346,f351,f385,f392])).
% 0.21/0.53  fof(f392,plain,(
% 0.21/0.53    ~spl7_44 | spl7_45 | ~spl7_37 | ~spl7_49),
% 0.21/0.53    inference(avatar_split_clause,[],[f386,f382,f296,f348,f343])).
% 0.21/0.53  fof(f343,plain,(
% 0.21/0.53    spl7_44 <=> m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).
% 0.21/0.53  fof(f348,plain,(
% 0.21/0.53    spl7_45 <=> k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK0),sK4))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).
% 0.21/0.53  fof(f296,plain,(
% 0.21/0.53    spl7_37 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).
% 0.21/0.53  fof(f382,plain,(
% 0.21/0.53    spl7_49 <=> m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_49])])).
% 0.21/0.53  fof(f386,plain,(
% 0.21/0.53    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK0),sK4)) | ~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl7_37 | ~spl7_49)),
% 0.21/0.53    inference(resolution,[],[f384,f297])).
% 0.21/0.53  fof(f297,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl7_37),
% 0.21/0.53    inference(avatar_component_clause,[],[f296])).
% 0.21/0.53  fof(f384,plain,(
% 0.21/0.53    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4),k1_zfmisc_1(u1_struct_0(sK1))) | ~spl7_49),
% 0.21/0.53    inference(avatar_component_clause,[],[f382])).
% 0.21/0.53  fof(f385,plain,(
% 0.21/0.53    spl7_49 | ~spl7_35 | ~spl7_36),
% 0.21/0.53    inference(avatar_split_clause,[],[f380,f289,f284,f382])).
% 0.21/0.53  fof(f284,plain,(
% 0.21/0.53    spl7_35 <=> m1_subset_1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).
% 0.21/0.53  fof(f289,plain,(
% 0.21/0.53    spl7_36 <=> k6_domain_1(u1_struct_0(sK0),sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).
% 0.21/0.53  fof(f380,plain,(
% 0.21/0.53    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4),k1_zfmisc_1(u1_struct_0(sK1))) | (~spl7_35 | ~spl7_36)),
% 0.21/0.53    inference(forward_demodulation,[],[f286,f291])).
% 0.21/0.53  fof(f291,plain,(
% 0.21/0.53    k6_domain_1(u1_struct_0(sK0),sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) | ~spl7_36),
% 0.21/0.53    inference(avatar_component_clause,[],[f289])).
% 0.21/0.53  fof(f286,plain,(
% 0.21/0.53    m1_subset_1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK1))) | ~spl7_35),
% 0.21/0.53    inference(avatar_component_clause,[],[f284])).
% 0.21/0.53  fof(f351,plain,(
% 0.21/0.53    ~spl7_45 | spl7_14 | ~spl7_42),
% 0.21/0.53    inference(avatar_split_clause,[],[f336,f330,f151,f348])).
% 0.21/0.53  fof(f151,plain,(
% 0.21/0.53    spl7_14 <=> k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK4))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.21/0.53  fof(f330,plain,(
% 0.21/0.53    spl7_42 <=> k6_domain_1(u1_struct_0(sK0),sK4) = k6_domain_1(u1_struct_0(sK1),sK4)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).
% 0.21/0.53  fof(f336,plain,(
% 0.21/0.53    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK0),sK4)) | (spl7_14 | ~spl7_42)),
% 0.21/0.53    inference(backward_demodulation,[],[f153,f332])).
% 0.21/0.53  fof(f332,plain,(
% 0.21/0.53    k6_domain_1(u1_struct_0(sK0),sK4) = k6_domain_1(u1_struct_0(sK1),sK4) | ~spl7_42),
% 0.21/0.53    inference(avatar_component_clause,[],[f330])).
% 0.21/0.53  fof(f153,plain,(
% 0.21/0.53    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK4)) | spl7_14),
% 0.21/0.53    inference(avatar_component_clause,[],[f151])).
% 0.21/0.53  fof(f346,plain,(
% 0.21/0.53    spl7_44 | ~spl7_39 | ~spl7_42),
% 0.21/0.53    inference(avatar_split_clause,[],[f335,f330,f311,f343])).
% 0.21/0.53  fof(f311,plain,(
% 0.21/0.53    spl7_39 <=> m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK4),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).
% 0.21/0.53  fof(f335,plain,(
% 0.21/0.53    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK4),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl7_39 | ~spl7_42)),
% 0.21/0.53    inference(backward_demodulation,[],[f313,f332])).
% 0.21/0.53  fof(f313,plain,(
% 0.21/0.53    m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK4),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl7_39),
% 0.21/0.53    inference(avatar_component_clause,[],[f311])).
% 0.21/0.53  fof(f333,plain,(
% 0.21/0.53    spl7_42 | ~spl7_33 | ~spl7_36),
% 0.21/0.53    inference(avatar_split_clause,[],[f328,f289,f270,f330])).
% 0.21/0.53  fof(f270,plain,(
% 0.21/0.53    spl7_33 <=> k6_domain_1(u1_struct_0(sK1),sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).
% 0.21/0.53  fof(f328,plain,(
% 0.21/0.53    k6_domain_1(u1_struct_0(sK0),sK4) = k6_domain_1(u1_struct_0(sK1),sK4) | (~spl7_33 | ~spl7_36)),
% 0.21/0.53    inference(backward_demodulation,[],[f272,f291])).
% 0.21/0.53  fof(f272,plain,(
% 0.21/0.53    k6_domain_1(u1_struct_0(sK1),sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) | ~spl7_33),
% 0.21/0.53    inference(avatar_component_clause,[],[f270])).
% 0.21/0.53  fof(f314,plain,(
% 0.21/0.53    spl7_39 | ~spl7_28 | ~spl7_33),
% 0.21/0.53    inference(avatar_split_clause,[],[f309,f270,f235,f311])).
% 0.21/0.53  fof(f235,plain,(
% 0.21/0.53    spl7_28 <=> m1_subset_1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).
% 0.21/0.53  fof(f309,plain,(
% 0.21/0.53    m1_subset_1(k6_domain_1(u1_struct_0(sK1),sK4),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl7_28 | ~spl7_33)),
% 0.21/0.53    inference(forward_demodulation,[],[f237,f272])).
% 0.21/0.53  fof(f237,plain,(
% 0.21/0.53    m1_subset_1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl7_28),
% 0.21/0.53    inference(avatar_component_clause,[],[f235])).
% 0.21/0.53  fof(f301,plain,(
% 0.21/0.53    spl7_28 | ~spl7_18),
% 0.21/0.53    inference(avatar_split_clause,[],[f299,f174,f235])).
% 0.21/0.53  fof(f174,plain,(
% 0.21/0.53    spl7_18 <=> r2_hidden(sK4,u1_struct_0(sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.21/0.53  fof(f299,plain,(
% 0.21/0.53    m1_subset_1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl7_18),
% 0.21/0.53    inference(resolution,[],[f176,f81])).
% 0.21/0.53  fof(f81,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f64,f78])).
% 0.21/0.53  fof(f78,plain,(
% 0.21/0.53    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f52,f77])).
% 0.21/0.53  fof(f77,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f63,f76])).
% 0.21/0.53  fof(f76,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f68,f75])).
% 0.21/0.53  fof(f75,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f69,f74])).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f70,f73])).
% 0.21/0.53  fof(f73,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f71,f72])).
% 0.21/0.53  fof(f72,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f30])).
% 0.21/0.53  % (23425)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (23426)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (23427)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (23442)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (23435)Refutation not found, incomplete strategy% (23435)------------------------------
% 0.21/0.53  % (23435)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (23435)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (23435)Memory used [KB]: 1791
% 0.21/0.53  % (23435)Time elapsed: 0.129 s
% 0.21/0.53  % (23435)------------------------------
% 0.21/0.53  % (23435)------------------------------
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).
% 0.21/0.53  fof(f176,plain,(
% 0.21/0.53    r2_hidden(sK4,u1_struct_0(sK0)) | ~spl7_18),
% 0.21/0.53    inference(avatar_component_clause,[],[f174])).
% 0.21/0.53  fof(f298,plain,(
% 0.21/0.53    spl7_37 | ~spl7_8 | spl7_4 | ~spl7_10 | ~spl7_11 | ~spl7_12 | ~spl7_5 | ~spl7_6 | spl7_7 | ~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_9),
% 0.21/0.53    inference(avatar_split_clause,[],[f294,f126,f96,f91,f86,f116,f111,f106,f141,f136,f131,f101,f121,f296])).
% 0.21/0.53  fof(f121,plain,(
% 0.21/0.53    spl7_8 <=> v3_borsuk_1(sK2,sK0,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.21/0.53  fof(f101,plain,(
% 0.21/0.53    spl7_4 <=> v2_struct_0(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.53  fof(f131,plain,(
% 0.21/0.53    spl7_10 <=> v5_pre_topc(sK2,sK0,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.21/0.53  fof(f136,plain,(
% 0.21/0.53    spl7_11 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.21/0.53  fof(f141,plain,(
% 0.21/0.53    spl7_12 <=> v1_funct_1(sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.21/0.53  fof(f106,plain,(
% 0.21/0.53    spl7_5 <=> m1_pre_topc(sK1,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.53  fof(f111,plain,(
% 0.21/0.53    spl7_6 <=> v4_tex_2(sK1,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.53  fof(f116,plain,(
% 0.21/0.53    spl7_7 <=> v2_struct_0(sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    spl7_1 <=> l1_pre_topc(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.53  fof(f91,plain,(
% 0.21/0.53    spl7_2 <=> v3_tdlat_3(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.53  fof(f96,plain,(
% 0.21/0.53    spl7_3 <=> v2_pre_topc(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.53  fof(f126,plain,(
% 0.21/0.53    spl7_9 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.21/0.53  fof(f294,plain,(
% 0.21/0.53    ( ! [X0] : (~v2_pre_topc(sK0) | ~v3_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v4_tex_2(sK1,sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1) | v2_struct_0(sK0) | ~v3_borsuk_1(sK2,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)) ) | ~spl7_9),
% 0.21/0.53    inference(resolution,[],[f83,f128])).
% 0.21/0.53  fof(f128,plain,(
% 0.21/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl7_9),
% 0.21/0.53    inference(avatar_component_clause,[],[f126])).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v5_pre_topc(X2,X0,X1) | v2_struct_0(X0) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X4) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) )),
% 0.21/0.53    inference(equality_resolution,[],[f55])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | X3 != X4 | k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : (! [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4) | X3 != X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v3_borsuk_1(X2,X0,X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~m1_pre_topc(X1,X0) | ~v4_tex_2(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k2_pre_topc(X0,X4))))))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tex_2)).
% 0.21/0.53  fof(f293,plain,(
% 0.21/0.53    ~spl7_19 | ~spl7_18),
% 0.21/0.53    inference(avatar_split_clause,[],[f192,f174,f178])).
% 0.21/0.53  fof(f178,plain,(
% 0.21/0.53    spl7_19 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.21/0.53  fof(f192,plain,(
% 0.21/0.53    ~v1_xboole_0(u1_struct_0(sK0)) | ~spl7_18),
% 0.21/0.53    inference(resolution,[],[f176,f62])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.53  % (23431)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  fof(f292,plain,(
% 0.21/0.53    spl7_36 | spl7_19 | ~spl7_15),
% 0.21/0.53    inference(avatar_split_clause,[],[f259,f156,f178,f289])).
% 0.21/0.53  fof(f156,plain,(
% 0.21/0.53    spl7_15 <=> m1_subset_1(sK4,u1_struct_0(sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.21/0.53  fof(f259,plain,(
% 0.21/0.53    v1_xboole_0(u1_struct_0(sK0)) | k6_domain_1(u1_struct_0(sK0),sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) | ~spl7_15),
% 0.21/0.53    inference(resolution,[],[f82,f158])).
% 0.21/0.53  fof(f158,plain,(
% 0.21/0.53    m1_subset_1(sK4,u1_struct_0(sK0)) | ~spl7_15),
% 0.21/0.53    inference(avatar_component_clause,[],[f156])).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X0) | k6_domain_1(X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f67,f78])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.53    inference(flattening,[],[f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,axiom,(
% 0.21/0.53    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.21/0.53  fof(f287,plain,(
% 0.21/0.53    spl7_35 | ~spl7_16),
% 0.21/0.53    inference(avatar_split_clause,[],[f280,f165,f284])).
% 0.21/0.53  fof(f165,plain,(
% 0.21/0.53    spl7_16 <=> r2_hidden(sK4,u1_struct_0(sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.21/0.53  fof(f280,plain,(
% 0.21/0.53    m1_subset_1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),k1_zfmisc_1(u1_struct_0(sK1))) | ~spl7_16),
% 0.21/0.53    inference(resolution,[],[f167,f81])).
% 0.21/0.53  fof(f167,plain,(
% 0.21/0.53    r2_hidden(sK4,u1_struct_0(sK1)) | ~spl7_16),
% 0.21/0.53    inference(avatar_component_clause,[],[f165])).
% 0.21/0.53  fof(f282,plain,(
% 0.21/0.53    spl7_18 | ~spl7_16 | ~spl7_22),
% 0.21/0.53    inference(avatar_split_clause,[],[f279,f196,f165,f174])).
% 0.21/0.53  fof(f196,plain,(
% 0.21/0.53    spl7_22 <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 0.21/0.53  fof(f279,plain,(
% 0.21/0.53    r2_hidden(sK4,u1_struct_0(sK0)) | (~spl7_16 | ~spl7_22)),
% 0.21/0.53    inference(resolution,[],[f167,f200])).
% 0.21/0.53  fof(f200,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(sK1)) | r2_hidden(X0,u1_struct_0(sK0))) ) | ~spl7_22),
% 0.21/0.53    inference(resolution,[],[f198,f66])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.53  fof(f198,plain,(
% 0.21/0.53    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl7_22),
% 0.21/0.53    inference(avatar_component_clause,[],[f196])).
% 0.21/0.53  fof(f273,plain,(
% 0.21/0.53    spl7_33 | spl7_17 | ~spl7_13),
% 0.21/0.53    inference(avatar_split_clause,[],[f258,f146,f169,f270])).
% 0.21/0.53  fof(f169,plain,(
% 0.21/0.53    spl7_17 <=> v1_xboole_0(u1_struct_0(sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 0.21/0.53  fof(f146,plain,(
% 0.21/0.53    spl7_13 <=> m1_subset_1(sK4,u1_struct_0(sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.21/0.53  fof(f258,plain,(
% 0.21/0.53    v1_xboole_0(u1_struct_0(sK1)) | k6_domain_1(u1_struct_0(sK1),sK4) = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) | ~spl7_13),
% 0.21/0.53    inference(resolution,[],[f82,f148])).
% 0.21/0.53  fof(f148,plain,(
% 0.21/0.53    m1_subset_1(sK4,u1_struct_0(sK1)) | ~spl7_13),
% 0.21/0.53    inference(avatar_component_clause,[],[f146])).
% 0.21/0.53  fof(f268,plain,(
% 0.21/0.53    ~spl7_6 | spl7_29 | spl7_4 | ~spl7_5 | ~spl7_1 | ~spl7_22),
% 0.21/0.53    inference(avatar_split_clause,[],[f267,f196,f86,f106,f101,f241,f111])).
% 0.21/0.53  fof(f241,plain,(
% 0.21/0.53    spl7_29 <=> v3_tex_2(u1_struct_0(sK1),sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).
% 0.21/0.53  fof(f267,plain,(
% 0.21/0.53    ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0) | v3_tex_2(u1_struct_0(sK1),sK0) | ~v4_tex_2(sK1,sK0) | ~spl7_22),
% 0.21/0.53    inference(resolution,[],[f84,f198])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0) | v3_tex_2(u1_struct_0(X1),X0) | ~v4_tex_2(X1,X0)) )),
% 0.21/0.53    inference(equality_resolution,[],[f57])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | v3_tex_2(X2,X0) | ~v4_tex_2(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((v4_tex_2(X1,X0) <=> ! [X2] : (v3_tex_2(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((v4_tex_2(X1,X0) <=> ! [X2] : ((v3_tex_2(X2,X0) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v4_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v3_tex_2(X2,X0))))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_tex_2)).
% 0.21/0.53  fof(f244,plain,(
% 0.21/0.53    ~spl7_29 | spl7_4 | ~spl7_17 | ~spl7_1 | ~spl7_3 | ~spl7_22),
% 0.21/0.53    inference(avatar_split_clause,[],[f239,f196,f96,f86,f169,f101,f241])).
% 0.21/0.53  fof(f239,plain,(
% 0.21/0.53    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_xboole_0(u1_struct_0(sK1)) | v2_struct_0(sK0) | ~v3_tex_2(u1_struct_0(sK1),sK0) | ~spl7_22),
% 0.21/0.53    inference(resolution,[],[f56,f198])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_xboole_0(X1) | v2_struct_0(X0) | ~v3_tex_2(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (~v3_tex_2(X1,X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).
% 0.21/0.54  fof(f199,plain,(
% 0.21/0.54    spl7_22 | ~spl7_1 | ~spl7_5),
% 0.21/0.54    inference(avatar_split_clause,[],[f194,f106,f86,f196])).
% 0.21/0.54  % (23425)Refutation not found, incomplete strategy% (23425)------------------------------
% 0.21/0.54  % (23425)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (23425)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (23425)Memory used [KB]: 10746
% 0.21/0.54  % (23425)Time elapsed: 0.130 s
% 0.21/0.54  % (23425)------------------------------
% 0.21/0.54  % (23425)------------------------------
% 0.21/0.54  fof(f194,plain,(
% 0.21/0.54    ~l1_pre_topc(sK0) | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl7_5),
% 0.21/0.54    inference(resolution,[],[f53,f108])).
% 0.21/0.54  fof(f108,plain,(
% 0.21/0.54    m1_pre_topc(sK1,sK0) | ~spl7_5),
% 0.21/0.54    inference(avatar_component_clause,[],[f106])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,axiom,(
% 0.21/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.21/0.54  fof(f172,plain,(
% 0.21/0.54    spl7_16 | spl7_17 | ~spl7_13),
% 0.21/0.54    inference(avatar_split_clause,[],[f161,f146,f169,f165])).
% 0.21/0.54  fof(f161,plain,(
% 0.21/0.54    v1_xboole_0(u1_struct_0(sK1)) | r2_hidden(sK4,u1_struct_0(sK1)) | ~spl7_13),
% 0.21/0.54    inference(resolution,[],[f65,f148])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.54    inference(flattening,[],[f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,axiom,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.54  fof(f159,plain,(
% 0.21/0.54    spl7_15),
% 0.21/0.54    inference(avatar_split_clause,[],[f36,f156])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    m1_subset_1(sK4,u1_struct_0(sK0))),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (? [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)) & X3 = X4) & m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X1))) & v3_borsuk_1(X2,X0,X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f19])).
% 0.21/0.54  fof(f19,negated_conjecture,(
% 0.21/0.54    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)))))))))),
% 0.21/0.54    inference(negated_conjecture,[],[f18])).
% 0.21/0.54  fof(f18,conjecture,(
% 0.21/0.54    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v4_tex_2(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_borsuk_1(X2,X0,X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (X3 = X4 => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k6_domain_1(u1_struct_0(X1),X3)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X4)))))))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tex_2)).
% 0.21/0.54  fof(f154,plain,(
% 0.21/0.54    ~spl7_14),
% 0.21/0.54    inference(avatar_split_clause,[],[f80,f151])).
% 0.21/0.54  fof(f80,plain,(
% 0.21/0.54    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4)) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK4))),
% 0.21/0.54    inference(definition_unfolding,[],[f38,f37])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    sK3 = sK4),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k6_domain_1(u1_struct_0(sK1),sK3)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK4))),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  fof(f149,plain,(
% 0.21/0.54    spl7_13),
% 0.21/0.54    inference(avatar_split_clause,[],[f79,f146])).
% 0.21/0.54  fof(f79,plain,(
% 0.21/0.54    m1_subset_1(sK4,u1_struct_0(sK1))),
% 0.21/0.54    inference(definition_unfolding,[],[f39,f37])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    m1_subset_1(sK3,u1_struct_0(sK1))),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  fof(f144,plain,(
% 0.21/0.54    spl7_12),
% 0.21/0.54    inference(avatar_split_clause,[],[f40,f141])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    v1_funct_1(sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  fof(f139,plain,(
% 0.21/0.54    spl7_11),
% 0.21/0.54    inference(avatar_split_clause,[],[f41,f136])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  fof(f134,plain,(
% 0.21/0.54    spl7_10),
% 0.21/0.54    inference(avatar_split_clause,[],[f42,f131])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    v5_pre_topc(sK2,sK0,sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  fof(f129,plain,(
% 0.21/0.54    spl7_9),
% 0.21/0.54    inference(avatar_split_clause,[],[f43,f126])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  fof(f124,plain,(
% 0.21/0.54    spl7_8),
% 0.21/0.54    inference(avatar_split_clause,[],[f44,f121])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    v3_borsuk_1(sK2,sK0,sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  fof(f119,plain,(
% 0.21/0.54    ~spl7_7),
% 0.21/0.54    inference(avatar_split_clause,[],[f45,f116])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ~v2_struct_0(sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  fof(f114,plain,(
% 0.21/0.54    spl7_6),
% 0.21/0.54    inference(avatar_split_clause,[],[f46,f111])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    v4_tex_2(sK1,sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  fof(f109,plain,(
% 0.21/0.54    spl7_5),
% 0.21/0.54    inference(avatar_split_clause,[],[f47,f106])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    m1_pre_topc(sK1,sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  fof(f104,plain,(
% 0.21/0.54    ~spl7_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f48,f101])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    ~v2_struct_0(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  fof(f99,plain,(
% 0.21/0.54    spl7_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f49,f96])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    v2_pre_topc(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  fof(f94,plain,(
% 0.21/0.54    spl7_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f50,f91])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    v3_tdlat_3(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  fof(f89,plain,(
% 0.21/0.54    spl7_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f51,f86])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    l1_pre_topc(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (23430)------------------------------
% 0.21/0.54  % (23430)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (23430)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (23430)Memory used [KB]: 11129
% 0.21/0.54  % (23430)Time elapsed: 0.104 s
% 0.21/0.54  % (23430)------------------------------
% 0.21/0.54  % (23430)------------------------------
% 0.21/0.54  % (23412)Success in time 0.18 s
%------------------------------------------------------------------------------
