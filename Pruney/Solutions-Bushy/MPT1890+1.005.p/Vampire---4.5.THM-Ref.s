%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1890+1.005 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:53 EST 2020

% Result     : Theorem 0.14s
% Output     : Refutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 207 expanded)
%              Number of leaves         :   24 ( 100 expanded)
%              Depth                    :    8
%              Number of atoms          :  367 (1037 expanded)
%              Number of equality atoms :   21 (  89 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f207,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f54,f59,f64,f69,f74,f105,f115,f130,f135,f144,f169,f180,f202,f206])).

fof(f206,plain,
    ( ~ spl3_5
    | ~ spl3_3
    | ~ spl3_21
    | spl3_23 ),
    inference(avatar_split_clause,[],[f204,f177,f166,f56,f66])).

fof(f66,plain,
    ( spl3_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f56,plain,
    ( spl3_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f166,plain,
    ( spl3_21
  <=> m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f177,plain,
    ( spl3_23
  <=> v4_pre_topc(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f204,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl3_23 ),
    inference(resolution,[],[f179,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

fof(f179,plain,
    ( ~ v4_pre_topc(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1))),sK0)
    | spl3_23 ),
    inference(avatar_component_clause,[],[f177])).

fof(f202,plain,
    ( ~ spl3_3
    | ~ spl3_21
    | spl3_22 ),
    inference(avatar_split_clause,[],[f200,f173,f166,f56])).

fof(f173,plain,
    ( spl3_22
  <=> m1_subset_1(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f200,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_22 ),
    inference(resolution,[],[f175,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f175,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_22 ),
    inference(avatar_component_clause,[],[f173])).

fof(f180,plain,
    ( spl3_6
    | ~ spl3_5
    | ~ spl3_4
    | ~ spl3_3
    | ~ spl3_2
    | ~ spl3_22
    | ~ spl3_23
    | spl3_1
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f171,f132,f46,f177,f173,f51,f56,f61,f66,f71])).

fof(f71,plain,
    ( spl3_6
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f61,plain,
    ( spl3_4
  <=> v3_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f51,plain,
    ( spl3_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f46,plain,
    ( spl3_1
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f132,plain,
    ( spl3_16
  <=> k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f171,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ v4_pre_topc(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1))),sK0)
    | ~ m1_subset_1(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v3_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_16 ),
    inference(trivial_inequality_removal,[],[f170])).

fof(f170,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) != k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1))
    | v2_tex_2(sK1,sK0)
    | ~ v4_pre_topc(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1))),sK0)
    | ~ m1_subset_1(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v3_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_16 ),
    inference(superposition,[],[f38,f134])).

fof(f134,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1))))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f132])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),sK2(X0,X1))
      | v2_tex_2(X1,X0)
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),sK2(X0,X1))
                | ~ v4_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & r2_hidden(sK2(X0,X1),X1)
            & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2)
              | ~ v4_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),sK2(X0,X1))
            | ~ v4_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r2_hidden(sK2(X0,X1),X1)
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ? [X2] :
              ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2)
                  | ~ v4_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ? [X2] :
              ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2)
                  | ~ v4_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = k6_domain_1(u1_struct_0(X0),X2)
                            & v4_pre_topc(X3,X0) ) )
                    & r2_hidden(X2,X1) ) )
           => v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_tex_2)).

fof(f169,plain,
    ( spl3_21
    | ~ spl3_13
    | spl3_17 ),
    inference(avatar_split_clause,[],[f164,f141,f112,f166])).

fof(f112,plain,
    ( spl3_13
  <=> m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f141,plain,
    ( spl3_17
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f164,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_13
    | spl3_17 ),
    inference(unit_resulting_resolution,[],[f114,f143,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f143,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl3_17 ),
    inference(avatar_component_clause,[],[f141])).

fof(f114,plain,
    ( m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f112])).

fof(f144,plain,
    ( ~ spl3_17
    | ~ spl3_2
    | spl3_15 ),
    inference(avatar_split_clause,[],[f139,f127,f51,f141])).

fof(f127,plain,
    ( spl3_15
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f139,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl3_2
    | spl3_15 ),
    inference(unit_resulting_resolution,[],[f53,f129,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f129,plain,
    ( ~ v1_xboole_0(sK1)
    | spl3_15 ),
    inference(avatar_component_clause,[],[f127])).

fof(f53,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f135,plain,
    ( ~ spl3_13
    | spl3_16
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f124,f102,f132,f112])).

fof(f102,plain,
    ( spl3_11
  <=> r2_hidden(sK2(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f124,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1))))
    | ~ m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0))
    | ~ spl3_11 ),
    inference(resolution,[],[f104,f34])).

fof(f34,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK1)
      | k6_domain_1(u1_struct_0(sK0),X2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ v2_tex_2(sK1,sK0)
    & ! [X2] :
        ( k6_domain_1(u1_struct_0(sK0),X2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
        | ~ r2_hidden(X2,sK1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v3_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f25,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_tex_2(X1,X0)
            & ! [X2] :
                ( k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ v2_tex_2(X1,sK0)
          & ! [X2] :
              ( k6_domain_1(u1_struct_0(sK0),X2) = k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v3_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( ~ v2_tex_2(X1,sK0)
        & ! [X2] :
            ( k6_domain_1(u1_struct_0(sK0),X2) = k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
            | ~ r2_hidden(X2,X1)
            | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ v2_tex_2(sK1,sK0)
      & ! [X2] :
          ( k6_domain_1(u1_struct_0(sK0),X2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
          | ~ r2_hidden(X2,sK1)
          | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & ! [X2] :
              ( k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & ! [X2] :
              ( k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ( r2_hidden(X2,X1)
                   => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) )
             => v2_tex_2(X1,X0) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,X1)
                 => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) )
           => v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_tex_2)).

fof(f104,plain,
    ( r2_hidden(sK2(sK0,sK1),sK1)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f102])).

fof(f130,plain,
    ( ~ spl3_15
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f123,f102,f127])).

fof(f123,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl3_11 ),
    inference(unit_resulting_resolution,[],[f104,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f115,plain,
    ( spl3_13
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | spl3_6 ),
    inference(avatar_split_clause,[],[f110,f71,f66,f61,f56,f51,f46,f112])).

fof(f110,plain,
    ( m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | spl3_6 ),
    inference(unit_resulting_resolution,[],[f73,f68,f63,f58,f48,f53,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f48,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f58,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f63,plain,
    ( v3_tdlat_3(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f61])).

fof(f68,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f66])).

fof(f73,plain,
    ( ~ v2_struct_0(sK0)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f71])).

fof(f105,plain,
    ( spl3_11
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | spl3_6 ),
    inference(avatar_split_clause,[],[f99,f71,f66,f61,f56,f51,f46,f102])).

fof(f99,plain,
    ( r2_hidden(sK2(sK0,sK1),sK1)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | spl3_6 ),
    inference(unit_resulting_resolution,[],[f73,f68,f63,f58,f48,f53,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v3_tdlat_3(X0)
      | r2_hidden(sK2(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_tex_2(X1,X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f74,plain,(
    ~ spl3_6 ),
    inference(avatar_split_clause,[],[f29,f71])).

fof(f29,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f69,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f30,f66])).

fof(f30,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f64,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f31,f61])).

fof(f31,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f59,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f32,f56])).

fof(f32,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f54,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f33,f51])).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f49,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f35,f46])).

fof(f35,plain,(
    ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

%------------------------------------------------------------------------------
