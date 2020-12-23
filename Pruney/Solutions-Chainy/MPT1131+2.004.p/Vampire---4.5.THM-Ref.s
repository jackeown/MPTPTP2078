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
% DateTime   : Thu Dec  3 13:09:25 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 553 expanded)
%              Number of leaves         :   39 ( 257 expanded)
%              Depth                    :   11
%              Number of atoms          :  764 (3699 expanded)
%              Number of equality atoms :   24 ( 201 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f421,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f71,f72,f77,f82,f87,f97,f102,f107,f112,f122,f127,f135,f140,f146,f153,f166,f178,f179,f192,f198,f206,f239,f255,f265,f301,f335,f355,f415])).

fof(f415,plain,
    ( ~ spl5_33
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_13
    | spl5_24 ),
    inference(avatar_split_clause,[],[f412,f203,f124,f119,f104,f94,f295])).

fof(f295,plain,
    ( spl5_33
  <=> v4_pre_topc(k10_relat_1(sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

% (27905)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
fof(f94,plain,
    ( spl5_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

% (27912)Refutation not found, incomplete strategy% (27912)------------------------------
% (27912)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (27912)Termination reason: Refutation not found, incomplete strategy

% (27912)Memory used [KB]: 10618
% (27912)Time elapsed: 0.071 s
% (27912)------------------------------
% (27912)------------------------------
fof(f104,plain,
    ( spl5_9
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f119,plain,
    ( spl5_12
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f124,plain,
    ( spl5_13
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f203,plain,
    ( spl5_24
  <=> v4_pre_topc(k10_relat_1(sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f412,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2)),sK0)
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_13
    | spl5_24 ),
    inference(unit_resulting_resolution,[],[f126,f121,f172,f205,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v4_pre_topc(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v4_pre_topc(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v4_pre_topc(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v4_pre_topc(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v4_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v4_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v4_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_pre_topc)).

fof(f205,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl5_24 ),
    inference(avatar_component_clause,[],[f203])).

fof(f172,plain,
    ( ! [X0] : m1_subset_1(k10_relat_1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_7
    | ~ spl5_9 ),
    inference(unit_resulting_resolution,[],[f171,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f171,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(sK2,X0),u1_struct_0(sK0))
    | ~ spl5_7
    | ~ spl5_9 ),
    inference(forward_demodulation,[],[f167,f159])).

fof(f159,plain,
    ( ! [X0] : k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k10_relat_1(sK2,X0)
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f96,f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f96,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f94])).

fof(f167,plain,
    ( ! [X0] : r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),u1_struct_0(sK0))
    | ~ spl5_7
    | ~ spl5_9 ),
    inference(unit_resulting_resolution,[],[f106,f96,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r1_tarski(k8_relset_1(X0,X1,X3,X2),X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k8_relset_1(X0,X1,X3,X2),X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k8_relset_1(X0,X1,X3,X2),X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X3) )
     => r1_tarski(k8_relset_1(X0,X1,X3,X2),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_funct_2)).

fof(f106,plain,
    ( v1_funct_1(sK2)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f104])).

fof(f121,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f119])).

fof(f126,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f124])).

fof(f355,plain,
    ( ~ spl5_36
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14
    | spl5_30 ),
    inference(avatar_split_clause,[],[f352,f258,f132,f124,f119,f104,f330])).

fof(f330,plain,
    ( spl5_36
  <=> v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f132,plain,
    ( spl5_14
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f258,plain,
    ( spl5_30
  <=> v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f352,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14
    | spl5_30 ),
    inference(unit_resulting_resolution,[],[f126,f121,f220,f260,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f260,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0)
    | spl5_30 ),
    inference(avatar_component_clause,[],[f258])).

fof(f220,plain,
    ( ! [X0] : m1_subset_1(k10_relat_1(sK2,X0),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ spl5_9
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f170,f62])).

fof(f170,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(sK2,X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl5_9
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f168,f160])).

fof(f160,plain,
    ( ! [X0] : k10_relat_1(sK2,X0) = k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1),sK2,X0)
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f134,f54])).

fof(f134,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f132])).

fof(f168,plain,
    ( ! [X0] : r1_tarski(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1),sK2,X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl5_9
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f106,f134,f61])).

fof(f335,plain,
    ( spl5_36
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_14
    | ~ spl5_15
    | ~ spl5_16
    | ~ spl5_19
    | ~ spl5_20
    | ~ spl5_29 ),
    inference(avatar_split_clause,[],[f334,f252,f175,f163,f143,f137,f132,f109,f104,f330])).

fof(f109,plain,
    ( spl5_10
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f137,plain,
    ( spl5_15
  <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f143,plain,
    ( spl5_16
  <=> v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f163,plain,
    ( spl5_19
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f175,plain,
    ( spl5_20
  <=> v4_pre_topc(sK4(sK0,sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f252,plain,
    ( spl5_29
  <=> m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f334,plain,
    ( v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_14
    | ~ spl5_15
    | ~ spl5_16
    | ~ spl5_19
    | ~ spl5_20
    | ~ spl5_29 ),
    inference(forward_demodulation,[],[f314,f160])).

fof(f314,plain,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_14
    | ~ spl5_15
    | ~ spl5_16
    | ~ spl5_19
    | ~ spl5_20
    | ~ spl5_29 ),
    inference(unit_resulting_resolution,[],[f111,f165,f177,f145,f139,f134,f254,f207])).

fof(f207,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(sK2,u1_struct_0(X2),u1_struct_0(X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ v5_pre_topc(sK2,X2,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        | ~ v4_pre_topc(X0,X1)
        | v4_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),sK2,X0),X2)
        | ~ l1_pre_topc(X1)
        | ~ l1_pre_topc(X2) )
    | ~ spl5_9 ),
    inference(resolution,[],[f50,f106])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v4_pre_topc(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X0)
                    & v4_pre_topc(sK4(X0,X1,X2),X1)
                    & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v4_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f33])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v4_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X0)
        & v4_pre_topc(sK4(X0,X1,X2),X1)
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v4_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v4_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v4_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X3] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      | ~ v4_pre_topc(X3,X1)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v4_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v4_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( v4_pre_topc(X3,X1)
                     => v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_pre_topc)).

fof(f254,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl5_29 ),
    inference(avatar_component_clause,[],[f252])).

fof(f139,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f137])).

fof(f145,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f143])).

fof(f177,plain,
    ( v4_pre_topc(sK4(sK0,sK1,sK2),sK1)
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f175])).

fof(f165,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f163])).

fof(f111,plain,
    ( l1_pre_topc(sK1)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f109])).

fof(f301,plain,
    ( spl5_33
    | ~ spl5_22
    | ~ spl5_23
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f278,f237,f195,f189,f295])).

fof(f189,plain,
    ( spl5_22
  <=> v4_pre_topc(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f195,plain,
    ( spl5_23
  <=> m1_subset_1(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f237,plain,
    ( spl5_27
  <=> ! [X0] :
        ( v4_pre_topc(k10_relat_1(sK2,X0),sK0)
        | ~ v4_pre_topc(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f278,plain,
    ( v4_pre_topc(k10_relat_1(sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2)),sK0)
    | ~ spl5_22
    | ~ spl5_23
    | ~ spl5_27 ),
    inference(unit_resulting_resolution,[],[f191,f197,f238])).

fof(f238,plain,
    ( ! [X0] :
        ( v4_pre_topc(k10_relat_1(sK2,X0),sK0)
        | ~ v4_pre_topc(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f237])).

fof(f197,plain,
    ( m1_subset_1(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f195])).

fof(f191,plain,
    ( v4_pre_topc(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2),sK1)
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f189])).

fof(f265,plain,
    ( ~ spl5_12
    | ~ spl5_10
    | ~ spl5_8
    | ~ spl5_7
    | ~ spl5_30
    | spl5_1
    | ~ spl5_7
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f264,f104,f94,f64,f258,f94,f99,f109,f119])).

fof(f99,plain,
    ( spl5_8
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f64,plain,
    ( spl5_1
  <=> v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f264,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | spl5_1
    | ~ spl5_7
    | ~ spl5_9 ),
    inference(forward_demodulation,[],[f250,f159])).

fof(f250,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | spl5_1
    | ~ spl5_9 ),
    inference(resolution,[],[f66,f200])).

fof(f200,plain,
    ( ! [X0,X1] :
        ( v5_pre_topc(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,sK4(X0,X1,sK2)),X0)
        | ~ l1_pre_topc(X1)
        | ~ l1_pre_topc(X0) )
    | ~ spl5_9 ),
    inference(resolution,[],[f53,f106])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v5_pre_topc(X2,X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f66,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f64])).

fof(f255,plain,
    ( spl5_29
    | spl5_1
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f248,f119,f109,f104,f99,f94,f64,f252])).

fof(f248,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | spl5_1
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f121,f111,f106,f101,f96,f66,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f101,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f99])).

fof(f239,plain,
    ( ~ spl5_12
    | ~ spl5_10
    | ~ spl5_7
    | ~ spl5_1
    | spl5_27
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f235,f104,f99,f94,f237,f64,f94,f109,f119])).

fof(f235,plain,
    ( ! [X0] :
        ( v4_pre_topc(k10_relat_1(sK2,X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v4_pre_topc(X0,sK1)
        | ~ l1_pre_topc(sK1)
        | ~ l1_pre_topc(sK0) )
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(forward_demodulation,[],[f233,f159])).

fof(f233,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v4_pre_topc(X0,sK1)
        | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0)
        | ~ l1_pre_topc(sK1)
        | ~ l1_pre_topc(sK0) )
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(resolution,[],[f207,f101])).

fof(f206,plain,
    ( ~ spl5_24
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_14
    | ~ spl5_15
    | spl5_16
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f201,f163,f143,f137,f132,f109,f104,f203])).

fof(f201,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_14
    | ~ spl5_15
    | spl5_16
    | ~ spl5_19 ),
    inference(forward_demodulation,[],[f199,f160])).

fof(f199,plain,
    ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1),sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_14
    | ~ spl5_15
    | spl5_16
    | ~ spl5_19 ),
    inference(unit_resulting_resolution,[],[f106,f111,f165,f144,f139,f134,f53])).

fof(f144,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | spl5_16 ),
    inference(avatar_component_clause,[],[f143])).

fof(f198,plain,
    ( spl5_23
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_14
    | ~ spl5_15
    | spl5_16
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f193,f163,f143,f137,f132,f109,f104,f195])).

fof(f193,plain,
    ( m1_subset_1(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_14
    | ~ spl5_15
    | spl5_16
    | ~ spl5_19 ),
    inference(unit_resulting_resolution,[],[f106,f111,f165,f144,f139,f134,f51])).

fof(f192,plain,
    ( spl5_22
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_14
    | ~ spl5_15
    | spl5_16
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f181,f163,f143,f137,f132,f109,f104,f189])).

fof(f181,plain,
    ( v4_pre_topc(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2),sK1)
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_14
    | ~ spl5_15
    | spl5_16
    | ~ spl5_19 ),
    inference(unit_resulting_resolution,[],[f106,f111,f144,f139,f134,f165,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(sK4(X0,X1,X2),X1)
      | v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f179,plain,
    ( sK2 != sK3
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f178,plain,
    ( spl5_20
    | spl5_1
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f173,f119,f109,f104,f99,f94,f64,f175])).

fof(f173,plain,
    ( v4_pre_topc(sK4(sK0,sK1,sK2),sK1)
    | spl5_1
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f121,f111,f106,f66,f101,f96,f52])).

fof(f166,plain,
    ( spl5_19
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f161,f150,f163])).

fof(f150,plain,
    ( spl5_17
  <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f161,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_17 ),
    inference(unit_resulting_resolution,[],[f152,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f152,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f150])).

fof(f153,plain,
    ( spl5_17
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f148,f119,f150])).

fof(f148,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f121,f60])).

fof(f60,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f146,plain,
    ( spl5_16
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f141,f74,f68,f143])).

fof(f68,plain,
    ( spl5_2
  <=> v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f74,plain,
    ( spl5_3
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f141,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f69,f76])).

fof(f76,plain,
    ( sK2 = sK3
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f74])).

% (27899)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
fof(f69,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f140,plain,
    ( spl5_15
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f129,f84,f74,f137])).

fof(f84,plain,
    ( spl5_5
  <=> v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f129,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(backward_demodulation,[],[f86,f76])).

fof(f86,plain,
    ( v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f84])).

fof(f135,plain,
    ( spl5_14
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f128,f79,f74,f132])).

fof(f79,plain,
    ( spl5_4
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f128,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(backward_demodulation,[],[f81,f76])).

fof(f81,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f79])).

fof(f127,plain,(
    spl5_13 ),
    inference(avatar_split_clause,[],[f37,f124])).

fof(f37,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
      | ~ v5_pre_topc(sK2,sK0,sK1) )
    & ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
      | v5_pre_topc(sK2,sK0,sK1) )
    & sK2 = sK3
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f29,f28,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
                      | ~ v5_pre_topc(X2,X0,X1) )
                    & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
                      | v5_pre_topc(X2,X0,X1) )
                    & X2 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X1)
                    | ~ v5_pre_topc(X2,sK0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X1)
                    | v5_pre_topc(X2,sK0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X1)
                  | ~ v5_pre_topc(X2,sK0,X1) )
                & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X1)
                  | v5_pre_topc(X2,sK0,X1) )
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1))))
                & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1))
                & v1_funct_1(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
                | ~ v5_pre_topc(X2,sK0,sK1) )
              & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
                | v5_pre_topc(X2,sK0,sK1) )
              & X2 = X3
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
              & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
              & v1_funct_1(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
              | ~ v5_pre_topc(X2,sK0,sK1) )
            & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
              | v5_pre_topc(X2,sK0,sK1) )
            & X2 = X3
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
            & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
            | ~ v5_pre_topc(sK2,sK0,sK1) )
          & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
            | v5_pre_topc(sK2,sK0,sK1) )
          & sK2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
          & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X3] :
        ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
          | ~ v5_pre_topc(sK2,sK0,sK1) )
        & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
          | v5_pre_topc(sK2,sK0,sK1) )
        & sK2 = X3
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
        & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
        & v1_funct_1(X3) )
   => ( ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
        | ~ v5_pre_topc(sK2,sK0,sK1) )
      & ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
        | v5_pre_topc(sK2,sK0,sK1) )
      & sK2 = sK3
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
      & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                      & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                      & v1_funct_1(X3) )
                   => ( X2 = X3
                     => ( v5_pre_topc(X2,X0,X1)
                      <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_pre_topc)).

fof(f122,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f38,f119])).

fof(f38,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f112,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f40,f109])).

fof(f40,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f107,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f41,f104])).

fof(f41,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f102,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f42,f99])).

fof(f42,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f97,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f43,f94])).

fof(f43,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f30])).

fof(f87,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f45,f84])).

fof(f45,plain,(
    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f82,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f46,f79])).

fof(f46,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f30])).

fof(f77,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f47,f74])).

fof(f47,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f30])).

fof(f72,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f48,f68,f64])).

fof(f48,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f71,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f49,f68,f64])).

fof(f49,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:00:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (27895)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.52  % (27900)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.52  % (27901)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.53  % (27894)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.53  % (27891)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.53  % (27890)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.53  % (27912)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.53  % (27909)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.53  % (27895)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.54  % (27903)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.54  % (27904)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.54  % (27902)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.54  % (27889)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f421,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f71,f72,f77,f82,f87,f97,f102,f107,f112,f122,f127,f135,f140,f146,f153,f166,f178,f179,f192,f198,f206,f239,f255,f265,f301,f335,f355,f415])).
% 0.22/0.54  fof(f415,plain,(
% 0.22/0.54    ~spl5_33 | ~spl5_7 | ~spl5_9 | ~spl5_12 | ~spl5_13 | spl5_24),
% 0.22/0.54    inference(avatar_split_clause,[],[f412,f203,f124,f119,f104,f94,f295])).
% 0.22/0.54  fof(f295,plain,(
% 0.22/0.54    spl5_33 <=> v4_pre_topc(k10_relat_1(sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2)),sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 0.22/0.54  % (27905)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.22/0.54  fof(f94,plain,(
% 0.22/0.54    spl5_7 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.22/0.54  % (27912)Refutation not found, incomplete strategy% (27912)------------------------------
% 0.22/0.54  % (27912)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (27912)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (27912)Memory used [KB]: 10618
% 0.22/0.54  % (27912)Time elapsed: 0.071 s
% 0.22/0.54  % (27912)------------------------------
% 0.22/0.54  % (27912)------------------------------
% 0.22/0.54  fof(f104,plain,(
% 0.22/0.54    spl5_9 <=> v1_funct_1(sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.22/0.54  fof(f119,plain,(
% 0.22/0.54    spl5_12 <=> l1_pre_topc(sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.22/0.54  fof(f124,plain,(
% 0.22/0.54    spl5_13 <=> v2_pre_topc(sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.22/0.54  fof(f203,plain,(
% 0.22/0.54    spl5_24 <=> v4_pre_topc(k10_relat_1(sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.22/0.54  fof(f412,plain,(
% 0.22/0.54    ~v4_pre_topc(k10_relat_1(sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2)),sK0) | (~spl5_7 | ~spl5_9 | ~spl5_12 | ~spl5_13 | spl5_24)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f126,f121,f172,f205,f56])).
% 0.22/0.54  fof(f56,plain,(
% 0.22/0.54    ( ! [X0,X1] : (v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.54    inference(flattening,[],[f35])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.54    inference(nnf_transformation,[],[f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.54    inference(flattening,[],[f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_pre_topc)).
% 0.22/0.54  fof(f205,plain,(
% 0.22/0.54    ~v4_pre_topc(k10_relat_1(sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | spl5_24),
% 0.22/0.54    inference(avatar_component_clause,[],[f203])).
% 0.22/0.54  fof(f172,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(k10_relat_1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl5_7 | ~spl5_9)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f171,f62])).
% 0.22/0.54  fof(f62,plain,(
% 0.22/0.54    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,plain,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.22/0.54    inference(unused_predicate_definition_removal,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.54  fof(f171,plain,(
% 0.22/0.54    ( ! [X0] : (r1_tarski(k10_relat_1(sK2,X0),u1_struct_0(sK0))) ) | (~spl5_7 | ~spl5_9)),
% 0.22/0.54    inference(forward_demodulation,[],[f167,f159])).
% 0.22/0.54  fof(f159,plain,(
% 0.22/0.54    ( ! [X0] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k10_relat_1(sK2,X0)) ) | ~spl5_7),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f96,f54])).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f16])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(ennf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.22/0.54  fof(f96,plain,(
% 0.22/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl5_7),
% 0.22/0.54    inference(avatar_component_clause,[],[f94])).
% 0.22/0.54  fof(f167,plain,(
% 0.22/0.54    ( ! [X0] : (r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),u1_struct_0(sK0))) ) | (~spl5_7 | ~spl5_9)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f106,f96,f61])).
% 0.22/0.54  fof(f61,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r1_tarski(k8_relset_1(X0,X1,X3,X2),X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (r1_tarski(k8_relset_1(X0,X1,X3,X2),X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))),
% 0.22/0.54    inference(flattening,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (r1_tarski(k8_relset_1(X0,X1,X3,X2),X0) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)))),
% 0.22/0.54    inference(ennf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => r1_tarski(k8_relset_1(X0,X1,X3,X2),X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_funct_2)).
% 0.22/0.54  fof(f106,plain,(
% 0.22/0.54    v1_funct_1(sK2) | ~spl5_9),
% 0.22/0.54    inference(avatar_component_clause,[],[f104])).
% 0.22/0.54  fof(f121,plain,(
% 0.22/0.54    l1_pre_topc(sK0) | ~spl5_12),
% 0.22/0.54    inference(avatar_component_clause,[],[f119])).
% 0.22/0.54  fof(f126,plain,(
% 0.22/0.54    v2_pre_topc(sK0) | ~spl5_13),
% 0.22/0.54    inference(avatar_component_clause,[],[f124])).
% 0.22/0.54  fof(f355,plain,(
% 0.22/0.54    ~spl5_36 | ~spl5_9 | ~spl5_12 | ~spl5_13 | ~spl5_14 | spl5_30),
% 0.22/0.54    inference(avatar_split_clause,[],[f352,f258,f132,f124,f119,f104,f330])).
% 0.22/0.54  fof(f330,plain,(
% 0.22/0.54    spl5_36 <=> v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).
% 0.22/0.54  fof(f132,plain,(
% 0.22/0.54    spl5_14 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.22/0.54  fof(f258,plain,(
% 0.22/0.54    spl5_30 <=> v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 0.22/0.54  fof(f352,plain,(
% 0.22/0.54    ~v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl5_9 | ~spl5_12 | ~spl5_13 | ~spl5_14 | spl5_30)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f126,f121,f220,f260,f58])).
% 0.22/0.54  fof(f58,plain,(
% 0.22/0.54    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f36])).
% 0.22/0.54  fof(f260,plain,(
% 0.22/0.54    ~v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0) | spl5_30),
% 0.22/0.54    inference(avatar_component_clause,[],[f258])).
% 0.22/0.54  fof(f220,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(k10_relat_1(sK2,X0),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) ) | (~spl5_9 | ~spl5_14)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f170,f62])).
% 0.22/0.54  fof(f170,plain,(
% 0.22/0.54    ( ! [X0] : (r1_tarski(k10_relat_1(sK2,X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) ) | (~spl5_9 | ~spl5_14)),
% 0.22/0.54    inference(forward_demodulation,[],[f168,f160])).
% 0.22/0.54  fof(f160,plain,(
% 0.22/0.54    ( ! [X0] : (k10_relat_1(sK2,X0) = k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1),sK2,X0)) ) | ~spl5_14),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f134,f54])).
% 0.22/0.54  fof(f134,plain,(
% 0.22/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~spl5_14),
% 0.22/0.54    inference(avatar_component_clause,[],[f132])).
% 0.22/0.54  fof(f168,plain,(
% 0.22/0.54    ( ! [X0] : (r1_tarski(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1),sK2,X0),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) ) | (~spl5_9 | ~spl5_14)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f106,f134,f61])).
% 0.22/0.54  fof(f335,plain,(
% 0.22/0.54    spl5_36 | ~spl5_9 | ~spl5_10 | ~spl5_14 | ~spl5_15 | ~spl5_16 | ~spl5_19 | ~spl5_20 | ~spl5_29),
% 0.22/0.54    inference(avatar_split_clause,[],[f334,f252,f175,f163,f143,f137,f132,f109,f104,f330])).
% 0.22/0.54  fof(f109,plain,(
% 0.22/0.54    spl5_10 <=> l1_pre_topc(sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.22/0.54  fof(f137,plain,(
% 0.22/0.54    spl5_15 <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.22/0.54  fof(f143,plain,(
% 0.22/0.54    spl5_16 <=> v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.22/0.54  fof(f163,plain,(
% 0.22/0.54    spl5_19 <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.22/0.54  fof(f175,plain,(
% 0.22/0.54    spl5_20 <=> v4_pre_topc(sK4(sK0,sK1,sK2),sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.22/0.54  fof(f252,plain,(
% 0.22/0.54    spl5_29 <=> m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 0.22/0.54  fof(f334,plain,(
% 0.22/0.54    v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl5_9 | ~spl5_10 | ~spl5_14 | ~spl5_15 | ~spl5_16 | ~spl5_19 | ~spl5_20 | ~spl5_29)),
% 0.22/0.54    inference(forward_demodulation,[],[f314,f160])).
% 0.22/0.54  fof(f314,plain,(
% 0.22/0.54    v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl5_9 | ~spl5_10 | ~spl5_14 | ~spl5_15 | ~spl5_16 | ~spl5_19 | ~spl5_20 | ~spl5_29)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f111,f165,f177,f145,f139,f134,f254,f207])).
% 0.22/0.54  fof(f207,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v1_funct_2(sK2,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~v5_pre_topc(sK2,X2,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v4_pre_topc(X0,X1) | v4_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),sK2,X0),X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X2)) ) | ~spl5_9),
% 0.22/0.54    inference(resolution,[],[f50,f106])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X1] : (~v1_funct_1(X2) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X0) & v4_pre_topc(sK4(X0,X1,X2),X1) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ! [X2,X1,X0] : (? [X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v4_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X0) & v4_pre_topc(sK4(X0,X1,X2),X1) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v4_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(rectify,[],[f31])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v4_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(nnf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(flattening,[],[f14])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : ((v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (v4_pre_topc(X3,X1) => v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)))))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_pre_topc)).
% 0.22/0.54  fof(f254,plain,(
% 0.22/0.54    m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) | ~spl5_29),
% 0.22/0.54    inference(avatar_component_clause,[],[f252])).
% 0.22/0.54  fof(f139,plain,(
% 0.22/0.54    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~spl5_15),
% 0.22/0.54    inference(avatar_component_clause,[],[f137])).
% 0.22/0.54  fof(f145,plain,(
% 0.22/0.54    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~spl5_16),
% 0.22/0.54    inference(avatar_component_clause,[],[f143])).
% 0.22/0.54  fof(f177,plain,(
% 0.22/0.54    v4_pre_topc(sK4(sK0,sK1,sK2),sK1) | ~spl5_20),
% 0.22/0.54    inference(avatar_component_clause,[],[f175])).
% 0.22/0.54  fof(f165,plain,(
% 0.22/0.54    l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl5_19),
% 0.22/0.54    inference(avatar_component_clause,[],[f163])).
% 0.22/0.54  fof(f111,plain,(
% 0.22/0.54    l1_pre_topc(sK1) | ~spl5_10),
% 0.22/0.54    inference(avatar_component_clause,[],[f109])).
% 0.22/0.54  fof(f301,plain,(
% 0.22/0.54    spl5_33 | ~spl5_22 | ~spl5_23 | ~spl5_27),
% 0.22/0.54    inference(avatar_split_clause,[],[f278,f237,f195,f189,f295])).
% 0.22/0.54  fof(f189,plain,(
% 0.22/0.54    spl5_22 <=> v4_pre_topc(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2),sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.22/0.54  fof(f195,plain,(
% 0.22/0.54    spl5_23 <=> m1_subset_1(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.22/0.54  fof(f237,plain,(
% 0.22/0.54    spl5_27 <=> ! [X0] : (v4_pre_topc(k10_relat_1(sK2,X0),sK0) | ~v4_pre_topc(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 0.22/0.54  fof(f278,plain,(
% 0.22/0.54    v4_pre_topc(k10_relat_1(sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2)),sK0) | (~spl5_22 | ~spl5_23 | ~spl5_27)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f191,f197,f238])).
% 0.22/0.54  fof(f238,plain,(
% 0.22/0.54    ( ! [X0] : (v4_pre_topc(k10_relat_1(sK2,X0),sK0) | ~v4_pre_topc(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))) ) | ~spl5_27),
% 0.22/0.54    inference(avatar_component_clause,[],[f237])).
% 0.22/0.54  fof(f197,plain,(
% 0.22/0.54    m1_subset_1(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) | ~spl5_23),
% 0.22/0.54    inference(avatar_component_clause,[],[f195])).
% 0.22/0.54  fof(f191,plain,(
% 0.22/0.54    v4_pre_topc(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2),sK1) | ~spl5_22),
% 0.22/0.54    inference(avatar_component_clause,[],[f189])).
% 0.22/0.54  fof(f265,plain,(
% 0.22/0.54    ~spl5_12 | ~spl5_10 | ~spl5_8 | ~spl5_7 | ~spl5_30 | spl5_1 | ~spl5_7 | ~spl5_9),
% 0.22/0.54    inference(avatar_split_clause,[],[f264,f104,f94,f64,f258,f94,f99,f109,f119])).
% 0.22/0.54  fof(f99,plain,(
% 0.22/0.54    spl5_8 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.22/0.54  fof(f64,plain,(
% 0.22/0.54    spl5_1 <=> v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.54  fof(f264,plain,(
% 0.22/0.54    ~v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0) | (spl5_1 | ~spl5_7 | ~spl5_9)),
% 0.22/0.54    inference(forward_demodulation,[],[f250,f159])).
% 0.22/0.54  fof(f250,plain,(
% 0.22/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK0) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0) | (spl5_1 | ~spl5_9)),
% 0.22/0.54    inference(resolution,[],[f66,f200])).
% 0.22/0.54  fof(f200,plain,(
% 0.22/0.54    ( ! [X0,X1] : (v5_pre_topc(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) | ~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,sK4(X0,X1,sK2)),X0) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) ) | ~spl5_9),
% 0.22/0.54    inference(resolution,[],[f53,f106])).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | v5_pre_topc(X2,X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f34])).
% 0.22/0.54  fof(f66,plain,(
% 0.22/0.54    ~v5_pre_topc(sK2,sK0,sK1) | spl5_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f64])).
% 0.22/0.54  fof(f255,plain,(
% 0.22/0.54    spl5_29 | spl5_1 | ~spl5_7 | ~spl5_8 | ~spl5_9 | ~spl5_10 | ~spl5_12),
% 0.22/0.54    inference(avatar_split_clause,[],[f248,f119,f109,f104,f99,f94,f64,f252])).
% 0.22/0.54  fof(f248,plain,(
% 0.22/0.54    m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) | (spl5_1 | ~spl5_7 | ~spl5_8 | ~spl5_9 | ~spl5_10 | ~spl5_12)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f121,f111,f106,f101,f96,f66,f51])).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f34])).
% 0.22/0.54  fof(f101,plain,(
% 0.22/0.54    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl5_8),
% 0.22/0.54    inference(avatar_component_clause,[],[f99])).
% 0.22/0.54  fof(f239,plain,(
% 0.22/0.54    ~spl5_12 | ~spl5_10 | ~spl5_7 | ~spl5_1 | spl5_27 | ~spl5_7 | ~spl5_8 | ~spl5_9),
% 0.22/0.54    inference(avatar_split_clause,[],[f235,f104,f99,f94,f237,f64,f94,f109,f119])).
% 0.22/0.54  fof(f235,plain,(
% 0.22/0.54    ( ! [X0] : (v4_pre_topc(k10_relat_1(sK2,X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v4_pre_topc(X0,sK1) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)) ) | (~spl5_7 | ~spl5_8 | ~spl5_9)),
% 0.22/0.54    inference(forward_demodulation,[],[f233,f159])).
% 0.22/0.54  fof(f233,plain,(
% 0.22/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v4_pre_topc(X0,sK1) | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)) ) | (~spl5_8 | ~spl5_9)),
% 0.22/0.54    inference(resolution,[],[f207,f101])).
% 0.22/0.54  fof(f206,plain,(
% 0.22/0.54    ~spl5_24 | ~spl5_9 | ~spl5_10 | ~spl5_14 | ~spl5_15 | spl5_16 | ~spl5_19),
% 0.22/0.54    inference(avatar_split_clause,[],[f201,f163,f143,f137,f132,f109,f104,f203])).
% 0.22/0.54  fof(f201,plain,(
% 0.22/0.54    ~v4_pre_topc(k10_relat_1(sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl5_9 | ~spl5_10 | ~spl5_14 | ~spl5_15 | spl5_16 | ~spl5_19)),
% 0.22/0.54    inference(forward_demodulation,[],[f199,f160])).
% 0.22/0.54  fof(f199,plain,(
% 0.22/0.54    ~v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1),sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl5_9 | ~spl5_10 | ~spl5_14 | ~spl5_15 | spl5_16 | ~spl5_19)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f106,f111,f165,f144,f139,f134,f53])).
% 0.22/0.54  fof(f144,plain,(
% 0.22/0.54    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | spl5_16),
% 0.22/0.54    inference(avatar_component_clause,[],[f143])).
% 0.22/0.54  fof(f198,plain,(
% 0.22/0.54    spl5_23 | ~spl5_9 | ~spl5_10 | ~spl5_14 | ~spl5_15 | spl5_16 | ~spl5_19),
% 0.22/0.54    inference(avatar_split_clause,[],[f193,f163,f143,f137,f132,f109,f104,f195])).
% 0.22/0.55  fof(f193,plain,(
% 0.22/0.55    m1_subset_1(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) | (~spl5_9 | ~spl5_10 | ~spl5_14 | ~spl5_15 | spl5_16 | ~spl5_19)),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f106,f111,f165,f144,f139,f134,f51])).
% 0.22/0.55  fof(f192,plain,(
% 0.22/0.55    spl5_22 | ~spl5_9 | ~spl5_10 | ~spl5_14 | ~spl5_15 | spl5_16 | ~spl5_19),
% 0.22/0.55    inference(avatar_split_clause,[],[f181,f163,f143,f137,f132,f109,f104,f189])).
% 0.22/0.55  fof(f181,plain,(
% 0.22/0.55    v4_pre_topc(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2),sK1) | (~spl5_9 | ~spl5_10 | ~spl5_14 | ~spl5_15 | spl5_16 | ~spl5_19)),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f106,f111,f144,f139,f134,f165,f52])).
% 0.22/0.55  fof(f52,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (v4_pre_topc(sK4(X0,X1,X2),X1) | v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f34])).
% 0.22/0.55  fof(f179,plain,(
% 0.22/0.55    sK2 != sK3 | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),
% 0.22/0.55    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.55  fof(f178,plain,(
% 0.22/0.55    spl5_20 | spl5_1 | ~spl5_7 | ~spl5_8 | ~spl5_9 | ~spl5_10 | ~spl5_12),
% 0.22/0.55    inference(avatar_split_clause,[],[f173,f119,f109,f104,f99,f94,f64,f175])).
% 0.22/0.55  fof(f173,plain,(
% 0.22/0.55    v4_pre_topc(sK4(sK0,sK1,sK2),sK1) | (spl5_1 | ~spl5_7 | ~spl5_8 | ~spl5_9 | ~spl5_10 | ~spl5_12)),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f121,f111,f106,f66,f101,f96,f52])).
% 0.22/0.55  fof(f166,plain,(
% 0.22/0.55    spl5_19 | ~spl5_17),
% 0.22/0.55    inference(avatar_split_clause,[],[f161,f150,f163])).
% 0.22/0.55  fof(f150,plain,(
% 0.22/0.55    spl5_17 <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.22/0.55  fof(f161,plain,(
% 0.22/0.55    l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl5_17),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f152,f55])).
% 0.22/0.55  fof(f55,plain,(
% 0.22/0.55    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f17])).
% 0.22/0.55  fof(f17,plain,(
% 0.22/0.55    ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.55    inference(ennf_transformation,[],[f11])).
% 0.22/0.55  fof(f11,plain,(
% 0.22/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => l1_pre_topc(g1_pre_topc(X0,X1)))),
% 0.22/0.55    inference(pure_predicate_removal,[],[f5])).
% 0.22/0.55  fof(f5,axiom,(
% 0.22/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).
% 0.22/0.55  fof(f152,plain,(
% 0.22/0.55    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl5_17),
% 0.22/0.55    inference(avatar_component_clause,[],[f150])).
% 0.22/0.55  fof(f153,plain,(
% 0.22/0.55    spl5_17 | ~spl5_12),
% 0.22/0.55    inference(avatar_split_clause,[],[f148,f119,f150])).
% 0.22/0.55  fof(f148,plain,(
% 0.22/0.55    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl5_12),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f121,f60])).
% 0.22/0.55  fof(f60,plain,(
% 0.22/0.55    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f20])).
% 0.22/0.55  fof(f20,plain,(
% 0.22/0.55    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f6])).
% 0.22/0.55  fof(f6,axiom,(
% 0.22/0.55    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 0.22/0.55  fof(f146,plain,(
% 0.22/0.55    spl5_16 | ~spl5_2 | ~spl5_3),
% 0.22/0.55    inference(avatar_split_clause,[],[f141,f74,f68,f143])).
% 0.22/0.55  fof(f68,plain,(
% 0.22/0.55    spl5_2 <=> v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.55  fof(f74,plain,(
% 0.22/0.55    spl5_3 <=> sK2 = sK3),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.55  fof(f141,plain,(
% 0.22/0.55    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl5_2 | ~spl5_3)),
% 0.22/0.55    inference(forward_demodulation,[],[f69,f76])).
% 0.22/0.55  fof(f76,plain,(
% 0.22/0.55    sK2 = sK3 | ~spl5_3),
% 0.22/0.55    inference(avatar_component_clause,[],[f74])).
% 0.22/0.55  % (27899)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.55  fof(f69,plain,(
% 0.22/0.55    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~spl5_2),
% 0.22/0.55    inference(avatar_component_clause,[],[f68])).
% 0.22/0.55  fof(f140,plain,(
% 0.22/0.55    spl5_15 | ~spl5_3 | ~spl5_5),
% 0.22/0.55    inference(avatar_split_clause,[],[f129,f84,f74,f137])).
% 0.22/0.55  fof(f84,plain,(
% 0.22/0.55    spl5_5 <=> v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.55  fof(f129,plain,(
% 0.22/0.55    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl5_3 | ~spl5_5)),
% 0.22/0.55    inference(backward_demodulation,[],[f86,f76])).
% 0.22/0.55  fof(f86,plain,(
% 0.22/0.55    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~spl5_5),
% 0.22/0.55    inference(avatar_component_clause,[],[f84])).
% 0.22/0.55  fof(f135,plain,(
% 0.22/0.55    spl5_14 | ~spl5_3 | ~spl5_4),
% 0.22/0.55    inference(avatar_split_clause,[],[f128,f79,f74,f132])).
% 0.22/0.55  fof(f79,plain,(
% 0.22/0.55    spl5_4 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.55  fof(f128,plain,(
% 0.22/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | (~spl5_3 | ~spl5_4)),
% 0.22/0.55    inference(backward_demodulation,[],[f81,f76])).
% 0.22/0.55  fof(f81,plain,(
% 0.22/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~spl5_4),
% 0.22/0.55    inference(avatar_component_clause,[],[f79])).
% 0.22/0.55  fof(f127,plain,(
% 0.22/0.55    spl5_13),
% 0.22/0.55    inference(avatar_split_clause,[],[f37,f124])).
% 0.22/0.55  fof(f37,plain,(
% 0.22/0.55    v2_pre_topc(sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f30])).
% 0.22/0.55  fof(f30,plain,(
% 0.22/0.55    ((((~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f29,f28,f27,f26])).
% 0.22/0.55  fof(f26,plain,(
% 0.22/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X1) | ~v5_pre_topc(X2,sK0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X1) | v5_pre_topc(X2,sK0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f27,plain,(
% 0.22/0.55    ? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X1) | ~v5_pre_topc(X2,sK0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X1) | v5_pre_topc(X2,sK0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v5_pre_topc(X2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(X2,sK0,sK1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f28,plain,(
% 0.22/0.55    ? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v5_pre_topc(X2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(X2,sK0,sK1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f29,plain,(
% 0.22/0.55    ? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) & v1_funct_1(X3)) => ((~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) & v1_funct_1(sK3))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f25,plain,(
% 0.22/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.55    inference(flattening,[],[f24])).
% 0.22/0.55  fof(f24,plain,(
% 0.22/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X2,X0,X1))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.55    inference(nnf_transformation,[],[f13])).
% 0.22/0.55  fof(f13,plain,(
% 0.22/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.55    inference(flattening,[],[f12])).
% 0.22/0.55  fof(f12,plain,(
% 0.22/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f9])).
% 0.22/0.55  fof(f9,negated_conjecture,(
% 0.22/0.55    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 0.22/0.55    inference(negated_conjecture,[],[f8])).
% 0.22/0.55  fof(f8,conjecture,(
% 0.22/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_pre_topc)).
% 0.22/0.55  fof(f122,plain,(
% 0.22/0.55    spl5_12),
% 0.22/0.55    inference(avatar_split_clause,[],[f38,f119])).
% 0.22/0.55  fof(f38,plain,(
% 0.22/0.55    l1_pre_topc(sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f30])).
% 0.22/0.55  fof(f112,plain,(
% 0.22/0.55    spl5_10),
% 0.22/0.55    inference(avatar_split_clause,[],[f40,f109])).
% 0.22/0.55  fof(f40,plain,(
% 0.22/0.55    l1_pre_topc(sK1)),
% 0.22/0.55    inference(cnf_transformation,[],[f30])).
% 0.22/0.55  fof(f107,plain,(
% 0.22/0.55    spl5_9),
% 0.22/0.55    inference(avatar_split_clause,[],[f41,f104])).
% 0.22/0.55  fof(f41,plain,(
% 0.22/0.55    v1_funct_1(sK2)),
% 0.22/0.55    inference(cnf_transformation,[],[f30])).
% 0.22/0.55  fof(f102,plain,(
% 0.22/0.55    spl5_8),
% 0.22/0.55    inference(avatar_split_clause,[],[f42,f99])).
% 0.22/0.55  fof(f42,plain,(
% 0.22/0.55    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.55    inference(cnf_transformation,[],[f30])).
% 0.22/0.55  fof(f97,plain,(
% 0.22/0.55    spl5_7),
% 0.22/0.55    inference(avatar_split_clause,[],[f43,f94])).
% 0.22/0.55  fof(f43,plain,(
% 0.22/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.55    inference(cnf_transformation,[],[f30])).
% 0.22/0.55  fof(f87,plain,(
% 0.22/0.55    spl5_5),
% 0.22/0.55    inference(avatar_split_clause,[],[f45,f84])).
% 0.22/0.55  fof(f45,plain,(
% 0.22/0.55    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))),
% 0.22/0.55    inference(cnf_transformation,[],[f30])).
% 0.22/0.55  fof(f82,plain,(
% 0.22/0.55    spl5_4),
% 0.22/0.55    inference(avatar_split_clause,[],[f46,f79])).
% 0.22/0.55  fof(f46,plain,(
% 0.22/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))),
% 0.22/0.55    inference(cnf_transformation,[],[f30])).
% 0.22/0.55  fof(f77,plain,(
% 0.22/0.55    spl5_3),
% 0.22/0.55    inference(avatar_split_clause,[],[f47,f74])).
% 0.22/0.55  fof(f47,plain,(
% 0.22/0.55    sK2 = sK3),
% 0.22/0.55    inference(cnf_transformation,[],[f30])).
% 0.22/0.55  fof(f72,plain,(
% 0.22/0.55    spl5_1 | spl5_2),
% 0.22/0.55    inference(avatar_split_clause,[],[f48,f68,f64])).
% 0.22/0.55  fof(f48,plain,(
% 0.22/0.55    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.55    inference(cnf_transformation,[],[f30])).
% 0.22/0.55  fof(f71,plain,(
% 0.22/0.55    ~spl5_1 | ~spl5_2),
% 0.22/0.55    inference(avatar_split_clause,[],[f49,f68,f64])).
% 0.22/0.55  fof(f49,plain,(
% 0.22/0.55    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v5_pre_topc(sK2,sK0,sK1)),
% 0.22/0.55    inference(cnf_transformation,[],[f30])).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (27895)------------------------------
% 0.22/0.55  % (27895)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (27911)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.22/0.55  % (27895)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (27895)Memory used [KB]: 11001
% 0.22/0.55  % (27895)Time elapsed: 0.111 s
% 0.22/0.55  % (27895)------------------------------
% 0.22/0.55  % (27895)------------------------------
% 0.22/0.55  % (27896)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.55  % (27888)Success in time 0.182 s
%------------------------------------------------------------------------------
