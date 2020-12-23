%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:17 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 578 expanded)
%              Number of leaves         :   18 ( 121 expanded)
%              Depth                    :   24
%              Number of atoms          :  502 (3623 expanded)
%              Number of equality atoms :   60 ( 336 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f252,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f98,f101,f155,f199,f204,f251])).

fof(f251,plain,
    ( ~ spl4_3
    | ~ spl4_7
    | spl4_8
    | ~ spl4_11 ),
    inference(avatar_contradiction_clause,[],[f250])).

fof(f250,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_7
    | spl4_8
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f249,f208])).

fof(f208,plain,
    ( r1_funct_2(k1_relat_1(sK3),u1_struct_0(sK0),k1_relat_1(sK3),u1_struct_0(sK0),sK3,sK3)
    | ~ spl4_7
    | spl4_8
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f207,f158])).

fof(f158,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK0))
    | ~ spl4_7 ),
    inference(backward_demodulation,[],[f37,f157])).

fof(f157,plain,
    ( u1_struct_0(sK1) = k1_relat_1(sK3)
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f156,f69])).

fof(f69,plain,(
    v4_relat_1(sK3,u1_struct_0(sK1)) ),
    inference(resolution,[],[f60,f38])).

fof(f38,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2))
                  & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2))
                  & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
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
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                      & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                      & v1_funct_1(X3) )
                   => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                     => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
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
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                    & v1_funct_1(X3) )
                 => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                   => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_tmap_1)).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f156,plain,
    ( u1_struct_0(sK1) = k1_relat_1(sK3)
    | ~ v4_relat_1(sK3,u1_struct_0(sK1))
    | ~ spl4_7 ),
    inference(resolution,[],[f150,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v1_partfun1(sK3,X0)
      | k1_relat_1(sK3) = X0
      | ~ v4_relat_1(sK3,X0) ) ),
    inference(resolution,[],[f58,f67])).

fof(f67,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f59,f38])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f150,plain,
    ( v1_partfun1(sK3,u1_struct_0(sK1))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl4_7
  <=> v1_partfun1(sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f37,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f207,plain,
    ( r1_funct_2(k1_relat_1(sK3),u1_struct_0(sK0),k1_relat_1(sK3),u1_struct_0(sK0),sK3,sK3)
    | ~ v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK0))
    | ~ spl4_7
    | spl4_8
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f206,f153])).

fof(f153,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl4_8 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl4_8
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f206,plain,
    ( r1_funct_2(k1_relat_1(sK3),u1_struct_0(sK0),k1_relat_1(sK3),u1_struct_0(sK0),sK3,sK3)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK0))
    | ~ spl4_7
    | ~ spl4_11 ),
    inference(resolution,[],[f198,f159])).

fof(f159,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0))))
    | ~ spl4_7 ),
    inference(backward_demodulation,[],[f38,f157])).

fof(f198,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | r1_funct_2(X1,X0,k1_relat_1(sK3),u1_struct_0(sK0),sK3,sK3)
        | v1_xboole_0(X0)
        | ~ v1_funct_2(sK3,X1,X0) )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f197])).

fof(f197,plain,
    ( spl4_11
  <=> ! [X1,X0] :
        ( v1_xboole_0(X0)
        | r1_funct_2(X1,X0,k1_relat_1(sK3),u1_struct_0(sK0),sK3,sK3)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(sK3,X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f249,plain,
    ( ~ r1_funct_2(k1_relat_1(sK3),u1_struct_0(sK0),k1_relat_1(sK3),u1_struct_0(sK0),sK3,sK3)
    | ~ spl4_3
    | ~ spl4_7 ),
    inference(backward_demodulation,[],[f163,f248])).

fof(f248,plain,
    ( sK3 = k2_tmap_1(sK1,sK0,sK3,sK2)
    | ~ spl4_3
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f247,f68])).

fof(f68,plain,(
    sK3 = k7_relat_1(sK3,k1_relat_1(sK3)) ),
    inference(resolution,[],[f67,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

fof(f247,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,k1_relat_1(sK3))
    | ~ spl4_3
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f246,f192])).

fof(f192,plain,
    ( ! [X0] : k7_relat_1(sK3,X0) = k2_partfun1(k1_relat_1(sK3),u1_struct_0(sK0),sK3,X0)
    | ~ spl4_7 ),
    inference(resolution,[],[f191,f159])).

fof(f191,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ) ),
    inference(resolution,[],[f61,f36])).

fof(f36,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f246,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) = k2_partfun1(k1_relat_1(sK3),u1_struct_0(sK0),sK3,k1_relat_1(sK3))
    | ~ spl4_3
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f245,f36])).

fof(f245,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) = k2_partfun1(k1_relat_1(sK3),u1_struct_0(sK0),sK3,k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ spl4_3
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f244,f159])).

fof(f244,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0))))
    | k2_tmap_1(sK1,sK0,sK3,sK2) = k2_partfun1(k1_relat_1(sK3),u1_struct_0(sK0),sK3,k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ spl4_3
    | ~ spl4_7 ),
    inference(resolution,[],[f243,f158])).

fof(f243,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,k1_relat_1(sK3),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0))))
        | k2_tmap_1(sK1,sK0,X0,sK2) = k2_partfun1(k1_relat_1(sK3),u1_struct_0(sK0),X0,k1_relat_1(sK3))
        | ~ v1_funct_1(X0) )
    | ~ spl4_3
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f242,f161])).

fof(f161,plain,
    ( u1_struct_0(sK2) = k1_relat_1(sK3)
    | ~ spl4_3
    | ~ spl4_7 ),
    inference(backward_demodulation,[],[f93,f157])).

fof(f93,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl4_3
  <=> u1_struct_0(sK1) = u1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f242,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,k1_relat_1(sK3),u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | k2_tmap_1(sK1,sK0,X0,sK2) = k2_partfun1(k1_relat_1(sK3),u1_struct_0(sK0),X0,u1_struct_0(sK2)) )
    | ~ spl4_7 ),
    inference(resolution,[],[f239,f42])).

fof(f42,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f239,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X1,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,k1_relat_1(sK3),u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | k2_tmap_1(sK1,sK0,X0,X1) = k2_partfun1(k1_relat_1(sK3),u1_struct_0(sK0),X0,u1_struct_0(X1)) )
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f238,f157])).

fof(f238,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,k1_relat_1(sK3),u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | ~ m1_pre_topc(X1,sK1)
        | k2_tmap_1(sK1,sK0,X0,X1) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X0,u1_struct_0(X1)) )
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f237,f157])).

fof(f237,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X0,k1_relat_1(sK3),u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ m1_pre_topc(X1,sK1)
        | k2_tmap_1(sK1,sK0,X0,X1) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X0,u1_struct_0(X1)) )
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f236,f157])).

fof(f236,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X1,sK1)
      | k2_tmap_1(sK1,sK0,X0,X1) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X0,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f235,f43])).

fof(f43,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f235,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK1)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X1,sK1)
      | k2_tmap_1(sK1,sK0,X0,X1) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X0,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f233,f45])).

fof(f45,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f233,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X1,sK1)
      | k2_tmap_1(sK1,sK0,X0,X1) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X0,u1_struct_0(X1)) ) ),
    inference(resolution,[],[f221,f44])).

fof(f44,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f221,plain,(
    ! [X4,X5,X3] :
      ( ~ v2_pre_topc(X3)
      | ~ l1_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X5,X3)
      | k2_tmap_1(X3,sK0,X4,X5) = k2_partfun1(u1_struct_0(X3),u1_struct_0(sK0),X4,u1_struct_0(X5)) ) ),
    inference(subsumption_resolution,[],[f220,f48])).

fof(f48,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f220,plain,(
    ! [X4,X5,X3] :
      ( ~ v2_pre_topc(X3)
      | ~ l1_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(sK0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X5,X3)
      | k2_tmap_1(X3,sK0,X4,X5) = k2_partfun1(u1_struct_0(X3),u1_struct_0(sK0),X4,u1_struct_0(X5)) ) ),
    inference(subsumption_resolution,[],[f214,f46])).

fof(f46,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f214,plain,(
    ! [X4,X5,X3] :
      ( ~ v2_pre_topc(X3)
      | ~ l1_pre_topc(X3)
      | v2_struct_0(sK0)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(sK0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
      | ~ m1_pre_topc(X5,X3)
      | k2_tmap_1(X3,sK0,X4,X5) = k2_partfun1(u1_struct_0(X3),u1_struct_0(sK0),X4,u1_struct_0(X5)) ) ),
    inference(resolution,[],[f53,f47])).

fof(f47,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X0)
      | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f163,plain,
    ( ~ r1_funct_2(k1_relat_1(sK3),u1_struct_0(sK0),k1_relat_1(sK3),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2))
    | ~ spl4_3
    | ~ spl4_7 ),
    inference(backward_demodulation,[],[f105,f157])).

fof(f105,plain,
    ( ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2))
    | ~ spl4_3 ),
    inference(backward_demodulation,[],[f40,f93])).

fof(f40,plain,(
    ~ r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f204,plain,(
    ~ spl4_8 ),
    inference(avatar_contradiction_clause,[],[f203])).

fof(f203,plain,
    ( $false
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f202,f48])).

fof(f202,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl4_8 ),
    inference(resolution,[],[f201,f50])).

fof(f50,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f201,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f200,f46])).

fof(f200,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_8 ),
    inference(resolution,[],[f154,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

% (23983)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f154,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f152])).

fof(f199,plain,
    ( spl4_8
    | spl4_11
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f195,f148,f197,f152])).

fof(f195,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(X0)
        | ~ v1_funct_2(sK3,X1,X0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | v1_xboole_0(u1_struct_0(sK0))
        | r1_funct_2(X1,X0,k1_relat_1(sK3),u1_struct_0(sK0),sK3,sK3) )
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f194,f158])).

fof(f194,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(X0)
        | ~ v1_funct_2(sK3,X1,X0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK0))
        | v1_xboole_0(u1_struct_0(sK0))
        | r1_funct_2(X1,X0,k1_relat_1(sK3),u1_struct_0(sK0),sK3,sK3) )
    | ~ spl4_7 ),
    inference(resolution,[],[f193,f159])).

fof(f193,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
      | v1_xboole_0(X1)
      | ~ v1_funct_2(sK3,X2,X1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(sK3,X3,X0)
      | v1_xboole_0(X0)
      | r1_funct_2(X2,X1,X3,X0,sK3,sK3) ) ),
    inference(resolution,[],[f66,f36])).

fof(f66,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X5)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1)
      | ~ v1_funct_2(X5,X0,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | r1_funct_2(X0,X1,X2,X3,X5,X5) ) ),
    inference(duplicate_literal_removal,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( v1_xboole_0(X1)
      | v1_xboole_0(X3)
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X0,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | r1_funct_2(X0,X1,X2,X3,X5,X5) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(X1)
      | v1_xboole_0(X3)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X0,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | X4 != X5
      | r1_funct_2(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_2(X5,X2,X3)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4)
        & ~ v1_xboole_0(X3)
        & ~ v1_xboole_0(X1) )
     => ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

fof(f155,plain,
    ( spl4_7
    | spl4_8 ),
    inference(avatar_split_clause,[],[f146,f152,f148])).

fof(f146,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | v1_partfun1(sK3,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f145,f37])).

fof(f145,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | v1_partfun1(sK3,u1_struct_0(sK1)) ),
    inference(resolution,[],[f144,f38])).

fof(f144,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | ~ v1_funct_2(sK3,X0,X1)
      | v1_partfun1(sK3,X0) ) ),
    inference(resolution,[],[f54,f36])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f101,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f100])).

fof(f100,plain,
    ( $false
    | spl4_4 ),
    inference(subsumption_resolution,[],[f99,f45])).

fof(f99,plain,
    ( ~ l1_pre_topc(sK1)
    | spl4_4 ),
    inference(resolution,[],[f97,f51])).

fof(f51,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f97,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl4_4
  <=> m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f98,plain,
    ( spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f89,f95,f91])).

fof(f89,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | u1_struct_0(sK1) = u1_struct_0(sK2) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | u1_struct_0(sK2) = X0 ) ),
    inference(superposition,[],[f55,f39])).

fof(f39,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:07:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (24002)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.52  % (23986)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.52  % (23986)Refutation not found, incomplete strategy% (23986)------------------------------
% 0.22/0.52  % (23986)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (23986)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (23986)Memory used [KB]: 10746
% 0.22/0.52  % (23986)Time elapsed: 0.088 s
% 0.22/0.52  % (23986)------------------------------
% 0.22/0.52  % (23986)------------------------------
% 0.22/0.53  % (23982)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.53  % (24002)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f252,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f98,f101,f155,f199,f204,f251])).
% 0.22/0.53  fof(f251,plain,(
% 0.22/0.53    ~spl4_3 | ~spl4_7 | spl4_8 | ~spl4_11),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f250])).
% 0.22/0.53  fof(f250,plain,(
% 0.22/0.53    $false | (~spl4_3 | ~spl4_7 | spl4_8 | ~spl4_11)),
% 0.22/0.53    inference(subsumption_resolution,[],[f249,f208])).
% 0.22/0.53  fof(f208,plain,(
% 0.22/0.53    r1_funct_2(k1_relat_1(sK3),u1_struct_0(sK0),k1_relat_1(sK3),u1_struct_0(sK0),sK3,sK3) | (~spl4_7 | spl4_8 | ~spl4_11)),
% 0.22/0.53    inference(subsumption_resolution,[],[f207,f158])).
% 0.22/0.53  fof(f158,plain,(
% 0.22/0.53    v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK0)) | ~spl4_7),
% 0.22/0.53    inference(backward_demodulation,[],[f37,f157])).
% 0.22/0.53  fof(f157,plain,(
% 0.22/0.53    u1_struct_0(sK1) = k1_relat_1(sK3) | ~spl4_7),
% 0.22/0.53    inference(subsumption_resolution,[],[f156,f69])).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    v4_relat_1(sK3,u1_struct_0(sK1))),
% 0.22/0.53    inference(resolution,[],[f60,f38])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,negated_conjecture,(
% 0.22/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)))))))),
% 0.22/0.53    inference(negated_conjecture,[],[f13])).
% 0.22/0.53  fof(f13,conjecture,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X3)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) => r1_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X2),u1_struct_0(X0),X3,k2_tmap_1(X1,X0,X3,X2)))))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_tmap_1)).
% 0.22/0.53  fof(f60,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.22/0.53    inference(pure_predicate_removal,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.53  fof(f156,plain,(
% 0.22/0.53    u1_struct_0(sK1) = k1_relat_1(sK3) | ~v4_relat_1(sK3,u1_struct_0(sK1)) | ~spl4_7),
% 0.22/0.53    inference(resolution,[],[f150,f70])).
% 0.22/0.53  fof(f70,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_partfun1(sK3,X0) | k1_relat_1(sK3) = X0 | ~v4_relat_1(sK3,X0)) )),
% 0.22/0.53    inference(resolution,[],[f58,f67])).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    v1_relat_1(sK3)),
% 0.22/0.53    inference(resolution,[],[f59,f38])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(flattening,[],[f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 0.22/0.53  fof(f150,plain,(
% 0.22/0.53    v1_partfun1(sK3,u1_struct_0(sK1)) | ~spl4_7),
% 0.22/0.53    inference(avatar_component_clause,[],[f148])).
% 0.22/0.53  fof(f148,plain,(
% 0.22/0.53    spl4_7 <=> v1_partfun1(sK3,u1_struct_0(sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f207,plain,(
% 0.22/0.53    r1_funct_2(k1_relat_1(sK3),u1_struct_0(sK0),k1_relat_1(sK3),u1_struct_0(sK0),sK3,sK3) | ~v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK0)) | (~spl4_7 | spl4_8 | ~spl4_11)),
% 0.22/0.53    inference(subsumption_resolution,[],[f206,f153])).
% 0.22/0.53  fof(f153,plain,(
% 0.22/0.53    ~v1_xboole_0(u1_struct_0(sK0)) | spl4_8),
% 0.22/0.53    inference(avatar_component_clause,[],[f152])).
% 0.22/0.53  fof(f152,plain,(
% 0.22/0.53    spl4_8 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.53  fof(f206,plain,(
% 0.22/0.53    r1_funct_2(k1_relat_1(sK3),u1_struct_0(sK0),k1_relat_1(sK3),u1_struct_0(sK0),sK3,sK3) | v1_xboole_0(u1_struct_0(sK0)) | ~v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK0)) | (~spl4_7 | ~spl4_11)),
% 0.22/0.53    inference(resolution,[],[f198,f159])).
% 0.22/0.53  fof(f159,plain,(
% 0.22/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) | ~spl4_7),
% 0.22/0.53    inference(backward_demodulation,[],[f38,f157])).
% 0.22/0.53  fof(f198,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | r1_funct_2(X1,X0,k1_relat_1(sK3),u1_struct_0(sK0),sK3,sK3) | v1_xboole_0(X0) | ~v1_funct_2(sK3,X1,X0)) ) | ~spl4_11),
% 0.22/0.53    inference(avatar_component_clause,[],[f197])).
% 0.22/0.53  fof(f197,plain,(
% 0.22/0.53    spl4_11 <=> ! [X1,X0] : (v1_xboole_0(X0) | r1_funct_2(X1,X0,k1_relat_1(sK3),u1_struct_0(sK0),sK3,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(sK3,X1,X0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.22/0.53  fof(f249,plain,(
% 0.22/0.53    ~r1_funct_2(k1_relat_1(sK3),u1_struct_0(sK0),k1_relat_1(sK3),u1_struct_0(sK0),sK3,sK3) | (~spl4_3 | ~spl4_7)),
% 0.22/0.53    inference(backward_demodulation,[],[f163,f248])).
% 0.22/0.53  fof(f248,plain,(
% 0.22/0.53    sK3 = k2_tmap_1(sK1,sK0,sK3,sK2) | (~spl4_3 | ~spl4_7)),
% 0.22/0.53    inference(forward_demodulation,[],[f247,f68])).
% 0.22/0.53  fof(f68,plain,(
% 0.22/0.53    sK3 = k7_relat_1(sK3,k1_relat_1(sK3))),
% 0.22/0.53    inference(resolution,[],[f67,f49])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).
% 0.22/0.53  fof(f247,plain,(
% 0.22/0.53    k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,k1_relat_1(sK3)) | (~spl4_3 | ~spl4_7)),
% 0.22/0.53    inference(forward_demodulation,[],[f246,f192])).
% 0.22/0.53  fof(f192,plain,(
% 0.22/0.53    ( ! [X0] : (k7_relat_1(sK3,X0) = k2_partfun1(k1_relat_1(sK3),u1_struct_0(sK0),sK3,X0)) ) | ~spl4_7),
% 0.22/0.53    inference(resolution,[],[f191,f159])).
% 0.22/0.53  fof(f191,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2)) )),
% 0.22/0.53    inference(resolution,[],[f61,f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    v1_funct_1(sK3)),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.22/0.53    inference(flattening,[],[f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.22/0.53  fof(f246,plain,(
% 0.22/0.53    k2_tmap_1(sK1,sK0,sK3,sK2) = k2_partfun1(k1_relat_1(sK3),u1_struct_0(sK0),sK3,k1_relat_1(sK3)) | (~spl4_3 | ~spl4_7)),
% 0.22/0.53    inference(subsumption_resolution,[],[f245,f36])).
% 0.22/0.53  fof(f245,plain,(
% 0.22/0.53    k2_tmap_1(sK1,sK0,sK3,sK2) = k2_partfun1(k1_relat_1(sK3),u1_struct_0(sK0),sK3,k1_relat_1(sK3)) | ~v1_funct_1(sK3) | (~spl4_3 | ~spl4_7)),
% 0.22/0.53    inference(subsumption_resolution,[],[f244,f159])).
% 0.22/0.53  fof(f244,plain,(
% 0.22/0.53    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) | k2_tmap_1(sK1,sK0,sK3,sK2) = k2_partfun1(k1_relat_1(sK3),u1_struct_0(sK0),sK3,k1_relat_1(sK3)) | ~v1_funct_1(sK3) | (~spl4_3 | ~spl4_7)),
% 0.22/0.53    inference(resolution,[],[f243,f158])).
% 0.22/0.53  fof(f243,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_funct_2(X0,k1_relat_1(sK3),u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) | k2_tmap_1(sK1,sK0,X0,sK2) = k2_partfun1(k1_relat_1(sK3),u1_struct_0(sK0),X0,k1_relat_1(sK3)) | ~v1_funct_1(X0)) ) | (~spl4_3 | ~spl4_7)),
% 0.22/0.53    inference(forward_demodulation,[],[f242,f161])).
% 0.22/0.53  fof(f161,plain,(
% 0.22/0.53    u1_struct_0(sK2) = k1_relat_1(sK3) | (~spl4_3 | ~spl4_7)),
% 0.22/0.53    inference(backward_demodulation,[],[f93,f157])).
% 0.22/0.53  fof(f93,plain,(
% 0.22/0.53    u1_struct_0(sK1) = u1_struct_0(sK2) | ~spl4_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f91])).
% 0.22/0.53  fof(f91,plain,(
% 0.22/0.53    spl4_3 <=> u1_struct_0(sK1) = u1_struct_0(sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.53  fof(f242,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) | ~v1_funct_2(X0,k1_relat_1(sK3),u1_struct_0(sK0)) | ~v1_funct_1(X0) | k2_tmap_1(sK1,sK0,X0,sK2) = k2_partfun1(k1_relat_1(sK3),u1_struct_0(sK0),X0,u1_struct_0(sK2))) ) | ~spl4_7),
% 0.22/0.53    inference(resolution,[],[f239,f42])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    m1_pre_topc(sK2,sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f239,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_pre_topc(X1,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) | ~v1_funct_2(X0,k1_relat_1(sK3),u1_struct_0(sK0)) | ~v1_funct_1(X0) | k2_tmap_1(sK1,sK0,X0,X1) = k2_partfun1(k1_relat_1(sK3),u1_struct_0(sK0),X0,u1_struct_0(X1))) ) | ~spl4_7),
% 0.22/0.53    inference(forward_demodulation,[],[f238,f157])).
% 0.22/0.53  fof(f238,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),u1_struct_0(sK0)))) | ~v1_funct_2(X0,k1_relat_1(sK3),u1_struct_0(sK0)) | ~v1_funct_1(X0) | ~m1_pre_topc(X1,sK1) | k2_tmap_1(sK1,sK0,X0,X1) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X0,u1_struct_0(X1))) ) | ~spl4_7),
% 0.22/0.53    inference(forward_demodulation,[],[f237,f157])).
% 0.22/0.53  fof(f237,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_funct_2(X0,k1_relat_1(sK3),u1_struct_0(sK0)) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X1,sK1) | k2_tmap_1(sK1,sK0,X0,X1) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X0,u1_struct_0(X1))) ) | ~spl4_7),
% 0.22/0.53    inference(forward_demodulation,[],[f236,f157])).
% 0.22/0.53  fof(f236,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X1,sK1) | k2_tmap_1(sK1,sK0,X0,X1) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X0,u1_struct_0(X1))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f235,f43])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ~v2_struct_0(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f235,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v2_struct_0(sK1) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X1,sK1) | k2_tmap_1(sK1,sK0,X0,X1) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X0,u1_struct_0(X1))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f233,f45])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    l1_pre_topc(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f233,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_pre_topc(X1,sK1) | k2_tmap_1(sK1,sK0,X0,X1) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),X0,u1_struct_0(X1))) )),
% 0.22/0.53    inference(resolution,[],[f221,f44])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    v2_pre_topc(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f221,plain,(
% 0.22/0.53    ( ! [X4,X5,X3] : (~v2_pre_topc(X3) | ~l1_pre_topc(X3) | v2_struct_0(X3) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) | ~m1_pre_topc(X5,X3) | k2_tmap_1(X3,sK0,X4,X5) = k2_partfun1(u1_struct_0(X3),u1_struct_0(sK0),X4,u1_struct_0(X5))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f220,f48])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    l1_pre_topc(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f220,plain,(
% 0.22/0.53    ( ! [X4,X5,X3] : (~v2_pre_topc(X3) | ~l1_pre_topc(X3) | v2_struct_0(X3) | ~l1_pre_topc(sK0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) | ~m1_pre_topc(X5,X3) | k2_tmap_1(X3,sK0,X4,X5) = k2_partfun1(u1_struct_0(X3),u1_struct_0(sK0),X4,u1_struct_0(X5))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f214,f46])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ~v2_struct_0(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f214,plain,(
% 0.22/0.53    ( ! [X4,X5,X3] : (~v2_pre_topc(X3) | ~l1_pre_topc(X3) | v2_struct_0(sK0) | v2_struct_0(X3) | ~l1_pre_topc(sK0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) | ~m1_pre_topc(X5,X3) | k2_tmap_1(X3,sK0,X4,X5) = k2_partfun1(u1_struct_0(X3),u1_struct_0(sK0),X4,u1_struct_0(X5))) )),
% 0.22/0.53    inference(resolution,[],[f53,f47])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    v2_pre_topc(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,axiom,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).
% 0.22/0.53  fof(f163,plain,(
% 0.22/0.53    ~r1_funct_2(k1_relat_1(sK3),u1_struct_0(sK0),k1_relat_1(sK3),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) | (~spl4_3 | ~spl4_7)),
% 0.22/0.53    inference(backward_demodulation,[],[f105,f157])).
% 0.22/0.53  fof(f105,plain,(
% 0.22/0.53    ~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2)) | ~spl4_3),
% 0.22/0.53    inference(backward_demodulation,[],[f40,f93])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ~r1_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK2),u1_struct_0(sK0),sK3,k2_tmap_1(sK1,sK0,sK3,sK2))),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f204,plain,(
% 0.22/0.53    ~spl4_8),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f203])).
% 0.22/0.53  fof(f203,plain,(
% 0.22/0.53    $false | ~spl4_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f202,f48])).
% 0.22/0.53  fof(f202,plain,(
% 0.22/0.53    ~l1_pre_topc(sK0) | ~spl4_8),
% 0.22/0.53    inference(resolution,[],[f201,f50])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.53  fof(f201,plain,(
% 0.22/0.53    ~l1_struct_0(sK0) | ~spl4_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f200,f46])).
% 0.22/0.53  fof(f200,plain,(
% 0.22/0.53    ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl4_8),
% 0.22/0.53    inference(resolution,[],[f154,f52])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  % (23983)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.53  fof(f9,axiom,(
% 0.22/0.53    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.22/0.53  fof(f154,plain,(
% 0.22/0.53    v1_xboole_0(u1_struct_0(sK0)) | ~spl4_8),
% 0.22/0.53    inference(avatar_component_clause,[],[f152])).
% 0.22/0.53  fof(f199,plain,(
% 0.22/0.53    spl4_8 | spl4_11 | ~spl4_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f195,f148,f197,f152])).
% 0.22/0.54  fof(f195,plain,(
% 0.22/0.54    ( ! [X0,X1] : (v1_xboole_0(X0) | ~v1_funct_2(sK3,X1,X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(u1_struct_0(sK0)) | r1_funct_2(X1,X0,k1_relat_1(sK3),u1_struct_0(sK0),sK3,sK3)) ) | ~spl4_7),
% 0.22/0.54    inference(subsumption_resolution,[],[f194,f158])).
% 0.22/0.54  fof(f194,plain,(
% 0.22/0.54    ( ! [X0,X1] : (v1_xboole_0(X0) | ~v1_funct_2(sK3,X1,X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(sK3,k1_relat_1(sK3),u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | r1_funct_2(X1,X0,k1_relat_1(sK3),u1_struct_0(sK0),sK3,sK3)) ) | ~spl4_7),
% 0.22/0.54    inference(resolution,[],[f193,f159])).
% 0.22/0.54  fof(f193,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | v1_xboole_0(X1) | ~v1_funct_2(sK3,X2,X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(sK3,X3,X0) | v1_xboole_0(X0) | r1_funct_2(X2,X1,X3,X0,sK3,sK3)) )),
% 0.22/0.54    inference(resolution,[],[f66,f36])).
% 0.22/0.54  fof(f66,plain,(
% 0.22/0.54    ( ! [X2,X0,X5,X3,X1] : (~v1_funct_1(X5) | v1_xboole_0(X3) | v1_xboole_0(X1) | ~v1_funct_2(X5,X0,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X5,X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | r1_funct_2(X0,X1,X2,X3,X5,X5)) )),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f65])).
% 0.22/0.54  fof(f65,plain,(
% 0.22/0.54    ( ! [X2,X0,X5,X3,X1] : (v1_xboole_0(X1) | v1_xboole_0(X3) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X0,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | r1_funct_2(X0,X1,X2,X3,X5,X5)) )),
% 0.22/0.54    inference(equality_resolution,[],[f62])).
% 0.22/0.54  fof(f62,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X1) | v1_xboole_0(X3) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X0,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | X4 != X5 | r1_funct_2(X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f35])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 0.22/0.54    inference(flattening,[],[f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 0.22/0.54    inference(ennf_transformation,[],[f11])).
% 0.22/0.54  fof(f11,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_funct_2)).
% 0.22/0.54  fof(f155,plain,(
% 0.22/0.54    spl4_7 | spl4_8),
% 0.22/0.54    inference(avatar_split_clause,[],[f146,f152,f148])).
% 0.22/0.54  fof(f146,plain,(
% 0.22/0.54    v1_xboole_0(u1_struct_0(sK0)) | v1_partfun1(sK3,u1_struct_0(sK1))),
% 0.22/0.54    inference(subsumption_resolution,[],[f145,f37])).
% 0.22/0.54  fof(f145,plain,(
% 0.22/0.54    v1_xboole_0(u1_struct_0(sK0)) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) | v1_partfun1(sK3,u1_struct_0(sK1))),
% 0.22/0.54    inference(resolution,[],[f144,f38])).
% 0.22/0.54  fof(f144,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_2(sK3,X0,X1) | v1_partfun1(sK3,X0)) )),
% 0.22/0.54    inference(resolution,[],[f54,f36])).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.54    inference(flattening,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.22/0.54  fof(f101,plain,(
% 0.22/0.54    spl4_4),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f100])).
% 0.22/0.54  fof(f100,plain,(
% 0.22/0.54    $false | spl4_4),
% 0.22/0.54    inference(subsumption_resolution,[],[f99,f45])).
% 0.22/0.54  fof(f99,plain,(
% 0.22/0.54    ~l1_pre_topc(sK1) | spl4_4),
% 0.22/0.54    inference(resolution,[],[f97,f51])).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 0.22/0.54  fof(f97,plain,(
% 0.22/0.54    ~m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | spl4_4),
% 0.22/0.54    inference(avatar_component_clause,[],[f95])).
% 0.22/0.54  fof(f95,plain,(
% 0.22/0.54    spl4_4 <=> m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.54  fof(f98,plain,(
% 0.22/0.54    spl4_3 | ~spl4_4),
% 0.22/0.54    inference(avatar_split_clause,[],[f89,f95,f91])).
% 0.22/0.54  fof(f89,plain,(
% 0.22/0.54    ~m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | u1_struct_0(sK1) = u1_struct_0(sK2)),
% 0.22/0.54    inference(equality_resolution,[],[f74])).
% 0.22/0.54  fof(f74,plain,(
% 0.22/0.54    ( ! [X0,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | u1_struct_0(sK2) = X0) )),
% 0.22/0.54    inference(superposition,[],[f55,f39])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f55,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | X0 = X2) )),
% 0.22/0.54    inference(cnf_transformation,[],[f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.54    inference(ennf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,axiom,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (24002)------------------------------
% 0.22/0.54  % (24002)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (24002)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (24002)Memory used [KB]: 10874
% 0.22/0.54  % (24002)Time elapsed: 0.096 s
% 0.22/0.54  % (24002)------------------------------
% 0.22/0.54  % (24002)------------------------------
% 0.22/0.54  % (23979)Success in time 0.173 s
%------------------------------------------------------------------------------
