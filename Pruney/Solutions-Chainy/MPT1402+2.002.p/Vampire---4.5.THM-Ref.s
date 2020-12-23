%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:23 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 269 expanded)
%              Number of leaves         :   15 ( 108 expanded)
%              Depth                    :   13
%              Number of atoms          :  494 (1129 expanded)
%              Number of equality atoms :   16 (  62 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f160,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f48,f52,f56,f72,f76,f95,f114,f130,f136,f154,f159])).

fof(f159,plain,
    ( spl6_8
    | ~ spl6_14 ),
    inference(avatar_contradiction_clause,[],[f158])).

fof(f158,plain,
    ( $false
    | spl6_8
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f156,f113])).

fof(f113,plain,
    ( ~ v4_pre_topc(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK0)
    | spl6_8 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl6_8
  <=> v4_pre_topc(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f156,plain,
    ( v4_pre_topc(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK0)
    | ~ spl6_14 ),
    inference(resolution,[],[f153,f25])).

fof(f25,plain,(
    ! [X4,X0,X1] :
      ( ~ sP5(X4,X1,X0)
      | v4_pre_topc(X4,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_connsp_2(X0,X1) = X2
              <=> ? [X3] :
                    ( k6_setfam_1(u1_struct_0(X0),X3) = X2
                    & ! [X4] :
                        ( ( r2_hidden(X4,X3)
                        <=> ( r2_hidden(X1,X4)
                            & v4_pre_topc(X4,X0)
                            & v3_pre_topc(X4,X0) ) )
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_connsp_2(X0,X1) = X2
              <=> ? [X3] :
                    ( k6_setfam_1(u1_struct_0(X0),X3) = X2
                    & ! [X4] :
                        ( ( r2_hidden(X4,X3)
                        <=> ( r2_hidden(X1,X4)
                            & v4_pre_topc(X4,X0)
                            & v3_pre_topc(X4,X0) ) )
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k1_connsp_2(X0,X1) = X2
              <=> ? [X3] :
                    ( k6_setfam_1(u1_struct_0(X0),X3) = X2
                    & ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                       => ( r2_hidden(X4,X3)
                        <=> ( r2_hidden(X1,X4)
                            & v4_pre_topc(X4,X0)
                            & v3_pre_topc(X4,X0) ) ) )
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_connsp_2)).

fof(f153,plain,
    ( sP5(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK1,sK0)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl6_14
  <=> sP5(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f154,plain,
    ( spl6_14
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_10
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f143,f134,f128,f74,f54,f50,f46,f42,f152])).

fof(f42,plain,
    ( spl6_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f46,plain,
    ( spl6_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f50,plain,
    ( spl6_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f54,plain,
    ( spl6_4
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f74,plain,
    ( spl6_6
  <=> m1_subset_1(k1_connsp_2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f128,plain,
    ( spl6_10
  <=> m1_subset_1(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f134,plain,
    ( spl6_11
  <=> r2_hidden(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK3(sK0,sK1,k1_connsp_2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f143,plain,
    ( sP5(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK1,sK0)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_10
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f142,f43])).

fof(f43,plain,
    ( ~ v2_struct_0(sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f142,plain,
    ( sP5(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_10
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f141,f129])).

fof(f129,plain,
    ( m1_subset_1(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f128])).

fof(f141,plain,
    ( ~ m1_subset_1(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | sP5(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f140,f75])).

fof(f75,plain,
    ( m1_subset_1(k1_connsp_2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f74])).

fof(f140,plain,
    ( ~ m1_subset_1(k1_connsp_2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | sP5(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f139,f55])).

fof(f55,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f54])).

fof(f139,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k1_connsp_2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | sP5(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f138,f51])).

fof(f51,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f138,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k1_connsp_2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | sP5(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f137,f47])).

fof(f47,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f137,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k1_connsp_2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | sP5(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl6_11 ),
    inference(resolution,[],[f135,f39])).

fof(f39,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,sK3(X0,X1,k1_connsp_2(X0,X1)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | sP5(X4,X1,X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X4,X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | sP5(X4,X1,X0)
      | ~ r2_hidden(X4,sK3(X0,X1,X2))
      | k1_connsp_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f135,plain,
    ( r2_hidden(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f134])).

fof(f136,plain,
    ( spl6_11
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f106,f93,f74,f70,f54,f50,f46,f42,f134])).

fof(f70,plain,
    ( spl6_5
  <=> v4_pre_topc(k1_connsp_2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f93,plain,
    ( spl6_7
  <=> m1_subset_1(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f106,plain,
    ( r2_hidden(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f105,f71])).

fof(f71,plain,
    ( ~ v4_pre_topc(k1_connsp_2(sK0,sK1),sK0)
    | spl6_5 ),
    inference(avatar_component_clause,[],[f70])).

fof(f105,plain,
    ( v4_pre_topc(k1_connsp_2(sK0,sK1),sK0)
    | r2_hidden(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f104,f91])).

fof(f91,plain,
    ( k1_connsp_2(sK0,sK1) = k6_setfam_1(u1_struct_0(sK0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f90,f43])).

fof(f90,plain,
    ( v2_struct_0(sK0)
    | k1_connsp_2(sK0,sK1) = k6_setfam_1(u1_struct_0(sK0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f89,f55])).

fof(f89,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | k1_connsp_2(sK0,sK1) = k6_setfam_1(u1_struct_0(sK0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f88,f51])).

fof(f88,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | k1_connsp_2(sK0,sK1) = k6_setfam_1(u1_struct_0(sK0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
    | ~ spl6_2
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f79,f47])).

fof(f79,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | k1_connsp_2(sK0,sK1) = k6_setfam_1(u1_struct_0(sK0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
    | ~ spl6_6 ),
    inference(resolution,[],[f75,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | k1_connsp_2(X0,X1) = k6_setfam_1(u1_struct_0(X0),sK3(X0,X1,k1_connsp_2(X0,X1))) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k6_setfam_1(u1_struct_0(X0),sK3(X0,X1,X2)) = X2
      | k1_connsp_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f104,plain,
    ( r2_hidden(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f103,f47])).

fof(f103,plain,
    ( ~ v2_pre_topc(sK0)
    | r2_hidden(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK0)
    | ~ spl6_3
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f97,f51])).

fof(f97,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | r2_hidden(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK0)
    | ~ spl6_7 ),
    inference(resolution,[],[f94,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | r2_hidden(sK2(X0,X1),X1)
      | v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
          | ? [X2] :
              ( ~ v4_pre_topc(X2,X0)
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
          | ? [X2] :
              ( ~ v4_pre_topc(X2,X0)
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v4_pre_topc(X2,X0) ) )
           => v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_pre_topc)).

fof(f94,plain,
    ( m1_subset_1(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f93])).

fof(f130,plain,
    ( spl6_10
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f102,f93,f74,f70,f54,f50,f46,f42,f128])).

fof(f102,plain,
    ( m1_subset_1(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f101,f71])).

fof(f101,plain,
    ( v4_pre_topc(k1_connsp_2(sK0,sK1),sK0)
    | m1_subset_1(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f100,f91])).

% (22388)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% (22383)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% (22384)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% (22390)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% (22382)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% (22376)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f100,plain,
    ( m1_subset_1(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f99,f47])).

fof(f99,plain,
    ( ~ v2_pre_topc(sK0)
    | m1_subset_1(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK0)
    | ~ spl6_3
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f96,f51])).

fof(f96,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | m1_subset_1(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK0)
    | ~ spl6_7 ),
    inference(resolution,[],[f94,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f114,plain,
    ( ~ spl6_8
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f110,f93,f74,f70,f54,f50,f46,f42,f112])).

fof(f110,plain,
    ( ~ v4_pre_topc(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK0)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f109,f71])).

fof(f109,plain,
    ( v4_pre_topc(k1_connsp_2(sK0,sK1),sK0)
    | ~ v4_pre_topc(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK0)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f108,f91])).

fof(f108,plain,
    ( ~ v4_pre_topc(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK0)
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f107,f47])).

fof(f107,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ v4_pre_topc(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK0)
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK0)
    | ~ spl6_3
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f98,f51])).

fof(f98,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v4_pre_topc(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK0)
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK0)
    | ~ spl6_7 ),
    inference(resolution,[],[f94,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ v4_pre_topc(sK2(X0,X1),X0)
      | v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f95,plain,
    ( spl6_7
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f87,f74,f54,f50,f46,f42,f93])).

fof(f87,plain,
    ( m1_subset_1(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f86,f43])).

fof(f86,plain,
    ( v2_struct_0(sK0)
    | m1_subset_1(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f85,f55])).

fof(f85,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | m1_subset_1(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f84,f51])).

fof(f84,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | m1_subset_1(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl6_2
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f78,f47])).

fof(f78,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | m1_subset_1(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl6_6 ),
    inference(resolution,[],[f75,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | m1_subset_1(sK3(X0,X1,k1_connsp_2(X0,X1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | k1_connsp_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f76,plain,
    ( spl6_6
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f68,f54,f50,f46,f42,f74])).

fof(f68,plain,
    ( m1_subset_1(k1_connsp_2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f67,f43])).

fof(f67,plain,
    ( v2_struct_0(sK0)
    | m1_subset_1(k1_connsp_2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f66,f51])).

fof(f66,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | m1_subset_1(k1_connsp_2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f59,f47])).

fof(f59,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | m1_subset_1(k1_connsp_2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_4 ),
    inference(resolution,[],[f55,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_connsp_2)).

fof(f72,plain,(
    ~ spl6_5 ),
    inference(avatar_split_clause,[],[f15,f70])).

fof(f15,plain,(
    ~ v4_pre_topc(k1_connsp_2(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v4_pre_topc(k1_connsp_2(X0,X1),X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v4_pre_topc(k1_connsp_2(X0,X1),X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => v4_pre_topc(k1_connsp_2(X0,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v4_pre_topc(k1_connsp_2(X0,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_connsp_2)).

fof(f56,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f14,f54])).

fof(f14,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f52,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f18,f50])).

fof(f18,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f48,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f17,f46])).

fof(f17,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f44,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f16,f42])).

fof(f16,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:17:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.48  % (22389)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.48  % (22375)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.49  % (22381)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.49  % (22375)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f160,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f44,f48,f52,f56,f72,f76,f95,f114,f130,f136,f154,f159])).
% 0.22/0.49  fof(f159,plain,(
% 0.22/0.49    spl6_8 | ~spl6_14),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f158])).
% 0.22/0.49  fof(f158,plain,(
% 0.22/0.49    $false | (spl6_8 | ~spl6_14)),
% 0.22/0.49    inference(subsumption_resolution,[],[f156,f113])).
% 0.22/0.49  fof(f113,plain,(
% 0.22/0.49    ~v4_pre_topc(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK0) | spl6_8),
% 0.22/0.49    inference(avatar_component_clause,[],[f112])).
% 0.22/0.49  fof(f112,plain,(
% 0.22/0.49    spl6_8 <=> v4_pre_topc(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.22/0.49  fof(f156,plain,(
% 0.22/0.49    v4_pre_topc(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK0) | ~spl6_14),
% 0.22/0.49    inference(resolution,[],[f153,f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ( ! [X4,X0,X1] : (~sP5(X4,X1,X0) | v4_pre_topc(X4,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : ((k1_connsp_2(X0,X1) = X2 <=> ? [X3] : (k6_setfam_1(u1_struct_0(X0),X3) = X2 & ! [X4] : ((r2_hidden(X4,X3) <=> (r2_hidden(X1,X4) & v4_pre_topc(X4,X0) & v3_pre_topc(X4,X0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : ((k1_connsp_2(X0,X1) = X2 <=> ? [X3] : (k6_setfam_1(u1_struct_0(X0),X3) = X2 & ! [X4] : ((r2_hidden(X4,X3) <=> (r2_hidden(X1,X4) & v4_pre_topc(X4,X0) & v3_pre_topc(X4,X0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (k1_connsp_2(X0,X1) = X2 <=> ? [X3] : (k6_setfam_1(u1_struct_0(X0),X3) = X2 & ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X4,X3) <=> (r2_hidden(X1,X4) & v4_pre_topc(X4,X0) & v3_pre_topc(X4,X0)))) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_connsp_2)).
% 0.22/0.49  fof(f153,plain,(
% 0.22/0.49    sP5(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK1,sK0) | ~spl6_14),
% 0.22/0.49    inference(avatar_component_clause,[],[f152])).
% 0.22/0.49  fof(f152,plain,(
% 0.22/0.49    spl6_14 <=> sP5(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK1,sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.22/0.49  fof(f154,plain,(
% 0.22/0.49    spl6_14 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_6 | ~spl6_10 | ~spl6_11),
% 0.22/0.49    inference(avatar_split_clause,[],[f143,f134,f128,f74,f54,f50,f46,f42,f152])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    spl6_1 <=> v2_struct_0(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    spl6_2 <=> v2_pre_topc(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    spl6_3 <=> l1_pre_topc(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    spl6_4 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.49  fof(f74,plain,(
% 0.22/0.49    spl6_6 <=> m1_subset_1(k1_connsp_2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.22/0.49  fof(f128,plain,(
% 0.22/0.49    spl6_10 <=> m1_subset_1(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.22/0.49  fof(f134,plain,(
% 0.22/0.49    spl6_11 <=> r2_hidden(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK3(sK0,sK1,k1_connsp_2(sK0,sK1)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.22/0.49  fof(f143,plain,(
% 0.22/0.49    sP5(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK1,sK0) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_6 | ~spl6_10 | ~spl6_11)),
% 0.22/0.49    inference(subsumption_resolution,[],[f142,f43])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    ~v2_struct_0(sK0) | spl6_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f42])).
% 0.22/0.49  fof(f142,plain,(
% 0.22/0.49    sP5(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK1,sK0) | v2_struct_0(sK0) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_6 | ~spl6_10 | ~spl6_11)),
% 0.22/0.49    inference(subsumption_resolution,[],[f141,f129])).
% 0.22/0.49  fof(f129,plain,(
% 0.22/0.49    m1_subset_1(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_10),
% 0.22/0.49    inference(avatar_component_clause,[],[f128])).
% 0.22/0.49  fof(f141,plain,(
% 0.22/0.49    ~m1_subset_1(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | sP5(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK1,sK0) | v2_struct_0(sK0) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_6 | ~spl6_11)),
% 0.22/0.49    inference(subsumption_resolution,[],[f140,f75])).
% 0.22/0.49  fof(f75,plain,(
% 0.22/0.49    m1_subset_1(k1_connsp_2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_6),
% 0.22/0.49    inference(avatar_component_clause,[],[f74])).
% 0.22/0.49  fof(f140,plain,(
% 0.22/0.49    ~m1_subset_1(k1_connsp_2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | sP5(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK1,sK0) | v2_struct_0(sK0) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_11)),
% 0.22/0.49    inference(subsumption_resolution,[],[f139,f55])).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl6_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f54])).
% 0.22/0.49  fof(f139,plain,(
% 0.22/0.49    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k1_connsp_2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | sP5(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK1,sK0) | v2_struct_0(sK0) | (~spl6_2 | ~spl6_3 | ~spl6_11)),
% 0.22/0.49    inference(subsumption_resolution,[],[f138,f51])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    l1_pre_topc(sK0) | ~spl6_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f50])).
% 0.22/0.49  fof(f138,plain,(
% 0.22/0.49    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k1_connsp_2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | sP5(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK1,sK0) | v2_struct_0(sK0) | (~spl6_2 | ~spl6_11)),
% 0.22/0.49    inference(subsumption_resolution,[],[f137,f47])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    v2_pre_topc(sK0) | ~spl6_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f46])).
% 0.22/0.49  fof(f137,plain,(
% 0.22/0.49    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k1_connsp_2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | sP5(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK1,sK0) | v2_struct_0(sK0) | ~spl6_11),
% 0.22/0.49    inference(resolution,[],[f135,f39])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ( ! [X4,X0,X1] : (~r2_hidden(X4,sK3(X0,X1,k1_connsp_2(X0,X1))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | sP5(X4,X1,X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(equality_resolution,[],[f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | sP5(X4,X1,X0) | ~r2_hidden(X4,sK3(X0,X1,X2)) | k1_connsp_2(X0,X1) != X2) )),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f135,plain,(
% 0.22/0.49    r2_hidden(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK3(sK0,sK1,k1_connsp_2(sK0,sK1))) | ~spl6_11),
% 0.22/0.49    inference(avatar_component_clause,[],[f134])).
% 0.22/0.49  fof(f136,plain,(
% 0.22/0.49    spl6_11 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | spl6_5 | ~spl6_6 | ~spl6_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f106,f93,f74,f70,f54,f50,f46,f42,f134])).
% 0.22/0.49  fof(f70,plain,(
% 0.22/0.49    spl6_5 <=> v4_pre_topc(k1_connsp_2(sK0,sK1),sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.22/0.49  fof(f93,plain,(
% 0.22/0.49    spl6_7 <=> m1_subset_1(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.22/0.49  fof(f106,plain,(
% 0.22/0.49    r2_hidden(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK3(sK0,sK1,k1_connsp_2(sK0,sK1))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | spl6_5 | ~spl6_6 | ~spl6_7)),
% 0.22/0.49    inference(subsumption_resolution,[],[f105,f71])).
% 0.22/0.49  fof(f71,plain,(
% 0.22/0.49    ~v4_pre_topc(k1_connsp_2(sK0,sK1),sK0) | spl6_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f70])).
% 0.22/0.49  fof(f105,plain,(
% 0.22/0.49    v4_pre_topc(k1_connsp_2(sK0,sK1),sK0) | r2_hidden(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK3(sK0,sK1,k1_connsp_2(sK0,sK1))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_6 | ~spl6_7)),
% 0.22/0.49    inference(forward_demodulation,[],[f104,f91])).
% 0.22/0.49  fof(f91,plain,(
% 0.22/0.49    k1_connsp_2(sK0,sK1) = k6_setfam_1(u1_struct_0(sK0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_6)),
% 0.22/0.49    inference(subsumption_resolution,[],[f90,f43])).
% 0.22/0.49  fof(f90,plain,(
% 0.22/0.49    v2_struct_0(sK0) | k1_connsp_2(sK0,sK1) = k6_setfam_1(u1_struct_0(sK0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1))) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_6)),
% 0.22/0.49    inference(subsumption_resolution,[],[f89,f55])).
% 0.22/0.49  fof(f89,plain,(
% 0.22/0.49    ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | k1_connsp_2(sK0,sK1) = k6_setfam_1(u1_struct_0(sK0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1))) | (~spl6_2 | ~spl6_3 | ~spl6_6)),
% 0.22/0.49    inference(subsumption_resolution,[],[f88,f51])).
% 0.22/0.49  fof(f88,plain,(
% 0.22/0.49    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | k1_connsp_2(sK0,sK1) = k6_setfam_1(u1_struct_0(sK0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1))) | (~spl6_2 | ~spl6_6)),
% 0.22/0.49    inference(subsumption_resolution,[],[f79,f47])).
% 0.22/0.49  fof(f79,plain,(
% 0.22/0.49    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | k1_connsp_2(sK0,sK1) = k6_setfam_1(u1_struct_0(sK0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1))) | ~spl6_6),
% 0.22/0.49    inference(resolution,[],[f75,f34])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | k1_connsp_2(X0,X1) = k6_setfam_1(u1_struct_0(X0),sK3(X0,X1,k1_connsp_2(X0,X1)))) )),
% 0.22/0.49    inference(equality_resolution,[],[f33])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k6_setfam_1(u1_struct_0(X0),sK3(X0,X1,X2)) = X2 | k1_connsp_2(X0,X1) != X2) )),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f104,plain,(
% 0.22/0.49    r2_hidden(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK3(sK0,sK1,k1_connsp_2(sK0,sK1))) | v4_pre_topc(k6_setfam_1(u1_struct_0(sK0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK0) | (~spl6_2 | ~spl6_3 | ~spl6_7)),
% 0.22/0.49    inference(subsumption_resolution,[],[f103,f47])).
% 0.22/0.49  fof(f103,plain,(
% 0.22/0.49    ~v2_pre_topc(sK0) | r2_hidden(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK3(sK0,sK1,k1_connsp_2(sK0,sK1))) | v4_pre_topc(k6_setfam_1(u1_struct_0(sK0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK0) | (~spl6_3 | ~spl6_7)),
% 0.22/0.49    inference(subsumption_resolution,[],[f97,f51])).
% 0.22/0.49  fof(f97,plain,(
% 0.22/0.49    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | r2_hidden(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK3(sK0,sK1,k1_connsp_2(sK0,sK1))) | v4_pre_topc(k6_setfam_1(u1_struct_0(sK0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK0) | ~spl6_7),
% 0.22/0.49    inference(resolution,[],[f94,f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | r2_hidden(sK2(X0,X1),X1) | v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) | ? [X2] : (~v4_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.49    inference(flattening,[],[f8])).
% 0.22/0.49  fof(f8,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) | ? [X2] : ((~v4_pre_topc(X2,X0) & r2_hidden(X2,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,X1) => v4_pre_topc(X2,X0))) => v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_pre_topc)).
% 0.22/0.49  fof(f94,plain,(
% 0.22/0.49    m1_subset_1(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl6_7),
% 0.22/0.49    inference(avatar_component_clause,[],[f93])).
% 0.22/0.49  fof(f130,plain,(
% 0.22/0.49    spl6_10 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | spl6_5 | ~spl6_6 | ~spl6_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f102,f93,f74,f70,f54,f50,f46,f42,f128])).
% 0.22/0.49  fof(f102,plain,(
% 0.22/0.49    m1_subset_1(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | spl6_5 | ~spl6_6 | ~spl6_7)),
% 0.22/0.49    inference(subsumption_resolution,[],[f101,f71])).
% 0.22/0.49  fof(f101,plain,(
% 0.22/0.49    v4_pre_topc(k1_connsp_2(sK0,sK1),sK0) | m1_subset_1(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_6 | ~spl6_7)),
% 0.22/0.49    inference(forward_demodulation,[],[f100,f91])).
% 0.22/0.50  % (22388)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.50  % (22383)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.50  % (22384)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.50  % (22390)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.50  % (22382)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.50  % (22376)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  fof(f100,plain,(
% 0.22/0.50    m1_subset_1(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(k6_setfam_1(u1_struct_0(sK0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK0) | (~spl6_2 | ~spl6_3 | ~spl6_7)),
% 0.22/0.50    inference(subsumption_resolution,[],[f99,f47])).
% 0.22/0.50  fof(f99,plain,(
% 0.22/0.50    ~v2_pre_topc(sK0) | m1_subset_1(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(k6_setfam_1(u1_struct_0(sK0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK0) | (~spl6_3 | ~spl6_7)),
% 0.22/0.50    inference(subsumption_resolution,[],[f96,f51])).
% 0.22/0.50  fof(f96,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | m1_subset_1(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(k6_setfam_1(u1_struct_0(sK0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK0) | ~spl6_7),
% 0.22/0.50    inference(resolution,[],[f94,f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f9])).
% 0.22/0.50  fof(f114,plain,(
% 0.22/0.50    ~spl6_8 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | spl6_5 | ~spl6_6 | ~spl6_7),
% 0.22/0.50    inference(avatar_split_clause,[],[f110,f93,f74,f70,f54,f50,f46,f42,f112])).
% 0.22/0.50  fof(f110,plain,(
% 0.22/0.50    ~v4_pre_topc(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK0) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | spl6_5 | ~spl6_6 | ~spl6_7)),
% 0.22/0.50    inference(subsumption_resolution,[],[f109,f71])).
% 0.22/0.50  fof(f109,plain,(
% 0.22/0.50    v4_pre_topc(k1_connsp_2(sK0,sK1),sK0) | ~v4_pre_topc(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK0) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_6 | ~spl6_7)),
% 0.22/0.50    inference(forward_demodulation,[],[f108,f91])).
% 0.22/0.50  fof(f108,plain,(
% 0.22/0.50    ~v4_pre_topc(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK0) | v4_pre_topc(k6_setfam_1(u1_struct_0(sK0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK0) | (~spl6_2 | ~spl6_3 | ~spl6_7)),
% 0.22/0.50    inference(subsumption_resolution,[],[f107,f47])).
% 0.22/0.50  fof(f107,plain,(
% 0.22/0.50    ~v2_pre_topc(sK0) | ~v4_pre_topc(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK0) | v4_pre_topc(k6_setfam_1(u1_struct_0(sK0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK0) | (~spl6_3 | ~spl6_7)),
% 0.22/0.50    inference(subsumption_resolution,[],[f98,f51])).
% 0.22/0.50  fof(f98,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~v4_pre_topc(sK2(sK0,sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK0) | v4_pre_topc(k6_setfam_1(u1_struct_0(sK0),sK3(sK0,sK1,k1_connsp_2(sK0,sK1))),sK0) | ~spl6_7),
% 0.22/0.50    inference(resolution,[],[f94,f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~v4_pre_topc(sK2(X0,X1),X0) | v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f9])).
% 0.22/0.50  fof(f95,plain,(
% 0.22/0.50    spl6_7 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f87,f74,f54,f50,f46,f42,f93])).
% 0.22/0.50  fof(f87,plain,(
% 0.22/0.50    m1_subset_1(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_6)),
% 0.22/0.50    inference(subsumption_resolution,[],[f86,f43])).
% 0.22/0.50  fof(f86,plain,(
% 0.22/0.50    v2_struct_0(sK0) | m1_subset_1(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_6)),
% 0.22/0.50    inference(subsumption_resolution,[],[f85,f55])).
% 0.22/0.50  fof(f85,plain,(
% 0.22/0.50    ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | m1_subset_1(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (~spl6_2 | ~spl6_3 | ~spl6_6)),
% 0.22/0.50    inference(subsumption_resolution,[],[f84,f51])).
% 0.22/0.50  fof(f84,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | m1_subset_1(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (~spl6_2 | ~spl6_6)),
% 0.22/0.50    inference(subsumption_resolution,[],[f78,f47])).
% 0.22/0.50  fof(f78,plain,(
% 0.22/0.50    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | m1_subset_1(sK3(sK0,sK1,k1_connsp_2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl6_6),
% 0.22/0.50    inference(resolution,[],[f75,f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | m1_subset_1(sK3(X0,X1,k1_connsp_2(X0,X1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) )),
% 0.22/0.50    inference(equality_resolution,[],[f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | k1_connsp_2(X0,X1) != X2) )),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f76,plain,(
% 0.22/0.50    spl6_6 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f68,f54,f50,f46,f42,f74])).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    m1_subset_1(k1_connsp_2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4)),
% 0.22/0.50    inference(subsumption_resolution,[],[f67,f43])).
% 0.22/0.50  fof(f67,plain,(
% 0.22/0.50    v2_struct_0(sK0) | m1_subset_1(k1_connsp_2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl6_2 | ~spl6_3 | ~spl6_4)),
% 0.22/0.50    inference(subsumption_resolution,[],[f66,f51])).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | m1_subset_1(k1_connsp_2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl6_2 | ~spl6_4)),
% 0.22/0.50    inference(subsumption_resolution,[],[f59,f47])).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | m1_subset_1(k1_connsp_2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_4),
% 0.22/0.50    inference(resolution,[],[f55,f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,plain,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f10])).
% 0.22/0.50  fof(f10,plain,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_connsp_2)).
% 0.22/0.50  fof(f72,plain,(
% 0.22/0.50    ~spl6_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f15,f70])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ~v4_pre_topc(k1_connsp_2(sK0,sK1),sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (~v4_pre_topc(k1_connsp_2(X0,X1),X0) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f6])).
% 0.22/0.50  fof(f6,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (~v4_pre_topc(k1_connsp_2(X0,X1),X0) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,negated_conjecture,(
% 0.22/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v4_pre_topc(k1_connsp_2(X0,X1),X0)))),
% 0.22/0.50    inference(negated_conjecture,[],[f4])).
% 0.22/0.50  fof(f4,conjecture,(
% 0.22/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v4_pre_topc(k1_connsp_2(X0,X1),X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_connsp_2)).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    spl6_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f14,f54])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.51    inference(cnf_transformation,[],[f7])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    spl6_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f18,f50])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    l1_pre_topc(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f7])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    spl6_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f17,f46])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    v2_pre_topc(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f7])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    ~spl6_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f16,f42])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ~v2_struct_0(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f7])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (22375)------------------------------
% 0.22/0.51  % (22375)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (22375)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (22375)Memory used [KB]: 6268
% 0.22/0.51  % (22375)Time elapsed: 0.063 s
% 0.22/0.51  % (22375)------------------------------
% 0.22/0.51  % (22375)------------------------------
% 0.22/0.51  % (22376)Refutation not found, incomplete strategy% (22376)------------------------------
% 0.22/0.51  % (22376)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (22376)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (22376)Memory used [KB]: 10618
% 0.22/0.51  % (22376)Time elapsed: 0.055 s
% 0.22/0.51  % (22376)------------------------------
% 0.22/0.51  % (22376)------------------------------
% 0.22/0.51  % (22374)Success in time 0.139 s
%------------------------------------------------------------------------------
