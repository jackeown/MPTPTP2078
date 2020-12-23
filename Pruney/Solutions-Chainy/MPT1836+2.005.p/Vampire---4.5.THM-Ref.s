%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:52 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  178 ( 522 expanded)
%              Number of leaves         :   35 ( 174 expanded)
%              Depth                    :   10
%              Number of atoms          : 1134 (7539 expanded)
%              Number of equality atoms :    5 ( 234 expanded)
%              Maximal formula depth    :   47 (   7 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f254,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f71,f127,f131,f133,f145,f147,f149,f151,f153,f162,f176,f178,f180,f184,f186,f188,f190,f192,f194,f196,f198,f206,f220,f222,f229,f231,f233,f235,f246,f253])).

fof(f253,plain,(
    spl6_31 ),
    inference(avatar_contradiction_clause,[],[f251])).

fof(f251,plain,
    ( $false
    | spl6_31 ),
    inference(resolution,[],[f245,f72])).

fof(f72,plain,(
    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4) ),
    inference(forward_demodulation,[],[f26,f25])).

fof(f25,plain,(
    sK0 = k1_tsep_1(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)
                            | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                            | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                          & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                          & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
                          & k1_tsep_1(X0,X2,X3) = X0
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_borsuk_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & v1_borsuk_1(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)
                            | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                            | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                          & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                          & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
                          & k1_tsep_1(X0,X2,X3) = X0
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_borsuk_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & v1_borsuk_1(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & v1_borsuk_1(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & v1_borsuk_1(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(X4,X2,X1)
                          & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v5_pre_topc(X5,X3,X1)
                              & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                                & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
                                & k1_tsep_1(X0,X2,X3) = X0 )
                             => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                                & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)
                                & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                                & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_borsuk_1(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & v1_borsuk_1(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v5_pre_topc(X4,X2,X1)
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(X5,X3,X1)
                            & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                         => ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                              & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
                              & k1_tsep_1(X0,X2,X3) = X0 )
                           => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                              & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1)
                              & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1))
                              & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_tmap_1)).

fof(f26,plain,(
    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4) ),
    inference(cnf_transformation,[],[f9])).

fof(f245,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4)
    | spl6_31 ),
    inference(avatar_component_clause,[],[f244])).

fof(f244,plain,
    ( spl6_31
  <=> r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f246,plain,
    ( spl6_2
    | spl6_18
    | ~ spl6_17
    | ~ spl6_16
    | ~ spl6_11
    | ~ spl6_10
    | ~ spl6_9
    | ~ spl6_8
    | ~ spl6_7
    | ~ spl6_6
    | ~ spl6_28
    | ~ spl6_29
    | ~ spl6_31
    | ~ spl6_30 ),
    inference(avatar_split_clause,[],[f236,f225,f244,f204,f201,f79,f82,f85,f88,f91,f94,f109,f112,f115,f63])).

fof(f63,plain,
    ( spl6_2
  <=> v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f115,plain,
    ( spl6_18
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f112,plain,
    ( spl6_17
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f109,plain,
    ( spl6_16
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f94,plain,
    ( spl6_11
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f91,plain,
    ( spl6_10
  <=> v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f88,plain,
    ( spl6_9
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f85,plain,
    ( spl6_8
  <=> v1_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f82,plain,
    ( spl6_7
  <=> v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f79,plain,
    ( spl6_6
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f201,plain,
    ( spl6_28
  <=> v5_pre_topc(sK4,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f204,plain,
    ( spl6_29
  <=> v5_pre_topc(sK5,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f225,plain,
    ( spl6_30
  <=> ! [X1,X0,X2] :
        ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),k3_tmap_1(sK0,X0,sK0,sK2,k10_tmap_1(sK0,X0,sK2,sK3,X1,X2)),X1)
        | v5_pre_topc(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),sK0,X0)
        | ~ v5_pre_topc(X2,sK3,X0)
        | ~ v5_pre_topc(X1,sK2,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),k3_tmap_1(sK0,X0,sK0,sK3,k10_tmap_1(sK0,X0,sK2,sK3,X1,X2)),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f236,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4)
    | ~ v5_pre_topc(sK5,sK3,sK1)
    | ~ v5_pre_topc(sK4,sK2,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1)
    | ~ spl6_30 ),
    inference(resolution,[],[f226,f73])).

fof(f73,plain,(
    r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) ),
    inference(forward_demodulation,[],[f27,f25])).

fof(f27,plain,(
    r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5) ),
    inference(cnf_transformation,[],[f9])).

fof(f226,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),k3_tmap_1(sK0,X0,sK0,sK3,k10_tmap_1(sK0,X0,sK2,sK3,X1,X2)),X2)
        | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),k3_tmap_1(sK0,X0,sK0,sK2,k10_tmap_1(sK0,X0,sK2,sK3,X1,X2)),X1)
        | ~ v5_pre_topc(X2,sK3,X0)
        | ~ v5_pre_topc(X1,sK2,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | v5_pre_topc(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),sK0,X0) )
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f225])).

fof(f235,plain,(
    ~ spl6_15 ),
    inference(avatar_contradiction_clause,[],[f234])).

fof(f234,plain,
    ( $false
    | ~ spl6_15 ),
    inference(resolution,[],[f107,f35])).

fof(f35,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f107,plain,
    ( v2_struct_0(sK2)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl6_15
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f233,plain,
    ( spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12
    | spl6_13
    | ~ spl6_14
    | spl6_15
    | ~ spl6_16
    | ~ spl6_17
    | spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | spl6_4 ),
    inference(avatar_split_clause,[],[f232,f69,f121,f118,f115,f112,f109,f106,f103,f100,f97,f94,f91,f88,f85,f82,f79,f76])).

fof(f76,plain,
    ( spl6_5
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f97,plain,
    ( spl6_12
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f100,plain,
    ( spl6_13
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f103,plain,
    ( spl6_14
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f118,plain,
    ( spl6_19
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f121,plain,
    ( spl6_20
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f69,plain,
    ( spl6_4
  <=> v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f232,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v2_struct_0(sK0)
    | spl6_4 ),
    inference(resolution,[],[f70,f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(X4)
        & m1_pre_topc(X3,X0)
        & ~ v2_struct_0(X3)
        & m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_tmap_1)).

fof(f70,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | spl6_4 ),
    inference(avatar_component_clause,[],[f69])).

fof(f231,plain,(
    ~ spl6_13 ),
    inference(avatar_contradiction_clause,[],[f230])).

fof(f230,plain,
    ( $false
    | ~ spl6_13 ),
    inference(resolution,[],[f101,f32])).

fof(f32,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f9])).

fof(f101,plain,
    ( v2_struct_0(sK3)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f100])).

fof(f229,plain,
    ( ~ spl6_21
    | spl6_22
    | spl6_30 ),
    inference(avatar_split_clause,[],[f228,f225,f140,f137])).

fof(f137,plain,
    ( spl6_21
  <=> r4_tsep_1(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f140,plain,
    ( spl6_22
  <=> r1_tsep_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f228,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),k3_tmap_1(sK0,X0,sK0,sK3,k10_tmap_1(sK0,X0,sK2,sK3,X1,X2)),X2)
      | ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),k3_tmap_1(sK0,X0,sK0,sK2,k10_tmap_1(sK0,X0,sK2,sK3,X1,X2)),X1)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | r1_tsep_1(sK2,sK3)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
      | ~ v5_pre_topc(X1,sK2,X0)
      | ~ v5_pre_topc(X2,sK3,X0)
      | ~ r4_tsep_1(sK0,sK2,sK3)
      | v5_pre_topc(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),sK0,X0) ) ),
    inference(global_subsumption,[],[f223])).

fof(f223,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),k3_tmap_1(sK0,X0,sK0,sK2,k10_tmap_1(sK0,X0,sK2,sK3,X1,X2)),X1)
      | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),k3_tmap_1(sK0,X0,sK0,sK3,k10_tmap_1(sK0,X0,sK2,sK3,X1,X2)),X2)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | r1_tsep_1(sK2,sK3)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
      | ~ v5_pre_topc(X1,sK2,X0)
      | ~ v5_pre_topc(X2,sK3,X0)
      | ~ r4_tsep_1(sK0,sK2,sK3)
      | v5_pre_topc(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),sK0,X0) ) ),
    inference(global_subsumption,[],[f32,f35,f41,f42,f43,f34,f37,f213])).

fof(f213,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),k3_tmap_1(sK0,X0,sK0,sK2,k10_tmap_1(sK0,X0,sK2,sK3,X1,X2)),X1)
      | ~ r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),k3_tmap_1(sK0,X0,sK0,sK3,k10_tmap_1(sK0,X0,sK2,sK3,X1,X2)),X2)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,sK0)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | r1_tsep_1(sK2,sK3)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ v5_pre_topc(X1,sK2,X0)
      | ~ v5_pre_topc(X2,sK3,X0)
      | ~ r4_tsep_1(sK0,sK2,sK3)
      | v5_pre_topc(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),sK0,X0) ) ),
    inference(superposition,[],[f182,f25])).

fof(f182,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
      | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | r1_tsep_1(X2,X3)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ v5_pre_topc(X4,X2,X1)
      | ~ v5_pre_topc(X5,X3,X1)
      | ~ r4_tsep_1(X0,X2,X3)
      | v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) ) ),
    inference(duplicate_literal_removal,[],[f181])).

fof(f181,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | r1_tsep_1(X2,X3)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | v2_struct_0(X0)
      | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
      | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | r1_tsep_1(X2,X3)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v5_pre_topc(X4,X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v5_pre_topc(X5,X3,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | v2_struct_0(X0)
      | ~ r4_tsep_1(X0,X2,X3)
      | v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) ) ),
    inference(resolution,[],[f48,f46])).

fof(f46,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | r1_tsep_1(X2,X3)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v5_pre_topc(X4,X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v5_pre_topc(X5,X3,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | v2_struct_0(X0)
      | ~ r4_tsep_1(X0,X2,X3)
      | v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                            & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                          | ~ r4_tsep_1(X0,X2,X3)
                          | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v5_pre_topc(X5,X3,X1)
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v5_pre_topc(X4,X2,X1)
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | r1_tsep_1(X2,X3)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                            & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                          | ~ r4_tsep_1(X0,X2,X3)
                          | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v5_pre_topc(X5,X3,X1)
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v5_pre_topc(X4,X2,X1)
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | r1_tsep_1(X2,X3)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( ~ r1_tsep_1(X2,X3)
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(X4,X2,X1)
                          & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v5_pre_topc(X5,X3,X1)
                              & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => ( ( r4_tsep_1(X0,X2,X3)
                                & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) )
                             => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                                & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                                & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                                & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_tmap_1)).

fof(f48,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | r1_tsep_1(X2,X3)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | v2_struct_0(X0)
      | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
      | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                              & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) )
                          <=> r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | r1_tsep_1(X2,X3)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                              & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) )
                          <=> r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | r1_tsep_1(X2,X3)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
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
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( ~ r1_tsep_1(X2,X3)
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                                & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) )
                            <=> r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_tmap_1)).

fof(f37,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f34,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f43,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f42,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f41,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f222,plain,(
    spl6_29 ),
    inference(avatar_contradiction_clause,[],[f221])).

fof(f221,plain,
    ( $false
    | spl6_29 ),
    inference(resolution,[],[f205,f23])).

fof(f23,plain,(
    v5_pre_topc(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f205,plain,
    ( ~ v5_pre_topc(sK5,sK3,sK1)
    | spl6_29 ),
    inference(avatar_component_clause,[],[f204])).

fof(f220,plain,(
    spl6_28 ),
    inference(avatar_contradiction_clause,[],[f219])).

fof(f219,plain,
    ( $false
    | spl6_28 ),
    inference(resolution,[],[f202,f30])).

fof(f30,plain,(
    v5_pre_topc(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f202,plain,
    ( ~ v5_pre_topc(sK4,sK2,sK1)
    | spl6_28 ),
    inference(avatar_component_clause,[],[f201])).

fof(f206,plain,
    ( spl6_18
    | ~ spl6_17
    | ~ spl6_16
    | ~ spl6_11
    | ~ spl6_10
    | ~ spl6_28
    | ~ spl6_9
    | ~ spl6_8
    | ~ spl6_7
    | ~ spl6_29
    | ~ spl6_6
    | spl6_2
    | ~ spl6_23 ),
    inference(avatar_split_clause,[],[f199,f143,f63,f79,f204,f82,f85,f88,f201,f91,f94,f109,f112,f115])).

fof(f143,plain,
    ( spl6_23
  <=> ! [X1,X0,X2] :
        ( v5_pre_topc(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),sK0,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v5_pre_topc(X2,sK3,X0)
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v5_pre_topc(X1,sK2,X0)
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f199,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(sK5,sK3,sK1)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v5_pre_topc(sK4,sK2,sK1)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl6_2
    | ~ spl6_23 ),
    inference(resolution,[],[f144,f64])).

fof(f64,plain,
    ( ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f144,plain,
    ( ! [X2,X0,X1] :
        ( v5_pre_topc(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),sK0,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
        | ~ v5_pre_topc(X2,sK3,X0)
        | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
        | ~ v5_pre_topc(X1,sK2,X0)
        | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f143])).

fof(f198,plain,(
    ~ spl6_18 ),
    inference(avatar_contradiction_clause,[],[f197])).

fof(f197,plain,
    ( $false
    | ~ spl6_18 ),
    inference(resolution,[],[f116,f38])).

fof(f38,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f116,plain,
    ( v2_struct_0(sK1)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f115])).

fof(f196,plain,
    ( ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_16
    | ~ spl6_17
    | spl6_18
    | spl6_1 ),
    inference(avatar_split_clause,[],[f195,f60,f115,f112,f109,f94,f91,f88,f85,f82,f79])).

fof(f60,plain,
    ( spl6_1
  <=> m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f195,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | spl6_1 ),
    inference(resolution,[],[f129,f61])).

fof(f61,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f60])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) ) ),
    inference(global_subsumption,[],[f32,f35,f41,f42,f43,f34,f37,f128])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,sK0)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f58,f25])).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f194,plain,
    ( ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_16
    | ~ spl6_17
    | spl6_18
    | spl6_3 ),
    inference(avatar_split_clause,[],[f193,f66,f115,f112,f109,f94,f91,f88,f85,f82,f79])).

fof(f66,plain,
    ( spl6_3
  <=> v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f193,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | spl6_3 ),
    inference(resolution,[],[f125,f67])).

fof(f67,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | spl6_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),u1_struct_0(sK0),u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) ) ),
    inference(global_subsumption,[],[f32,f35,f41,f42,f43,f34,f37,f124])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,sK0)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f57,f25])).

fof(f57,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f192,plain,(
    spl6_9 ),
    inference(avatar_contradiction_clause,[],[f191])).

fof(f191,plain,
    ( $false
    | spl6_9 ),
    inference(resolution,[],[f89,f31])).

fof(f31,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f9])).

fof(f89,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | spl6_9 ),
    inference(avatar_component_clause,[],[f88])).

fof(f190,plain,(
    spl6_6 ),
    inference(avatar_contradiction_clause,[],[f189])).

fof(f189,plain,
    ( $false
    | spl6_6 ),
    inference(resolution,[],[f80,f24])).

fof(f24,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f9])).

fof(f80,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | spl6_6 ),
    inference(avatar_component_clause,[],[f79])).

fof(f188,plain,(
    spl6_10 ),
    inference(avatar_contradiction_clause,[],[f187])).

fof(f187,plain,
    ( $false
    | spl6_10 ),
    inference(resolution,[],[f92,f29])).

fof(f29,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f92,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))
    | spl6_10 ),
    inference(avatar_component_clause,[],[f91])).

fof(f186,plain,(
    spl6_7 ),
    inference(avatar_contradiction_clause,[],[f185])).

fof(f185,plain,
    ( $false
    | spl6_7 ),
    inference(resolution,[],[f83,f22])).

fof(f22,plain,(
    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f83,plain,
    ( ~ v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))
    | spl6_7 ),
    inference(avatar_component_clause,[],[f82])).

fof(f184,plain,(
    ~ spl6_5 ),
    inference(avatar_contradiction_clause,[],[f183])).

fof(f183,plain,
    ( $false
    | ~ spl6_5 ),
    inference(resolution,[],[f77,f41])).

fof(f77,plain,
    ( v2_struct_0(sK0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f76])).

fof(f180,plain,(
    spl6_27 ),
    inference(avatar_contradiction_clause,[],[f179])).

fof(f179,plain,
    ( $false
    | spl6_27 ),
    inference(resolution,[],[f175,f36])).

fof(f36,plain,(
    v1_borsuk_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f175,plain,
    ( ~ v1_borsuk_1(sK2,sK0)
    | spl6_27 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl6_27
  <=> v1_borsuk_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f178,plain,(
    spl6_26 ),
    inference(avatar_contradiction_clause,[],[f177])).

fof(f177,plain,
    ( $false
    | spl6_26 ),
    inference(resolution,[],[f172,f33])).

fof(f33,plain,(
    v1_borsuk_1(sK3,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f172,plain,
    ( ~ v1_borsuk_1(sK3,sK0)
    | spl6_26 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl6_26
  <=> v1_borsuk_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f176,plain,
    ( spl6_5
    | ~ spl6_12
    | ~ spl6_26
    | ~ spl6_14
    | ~ spl6_27
    | ~ spl6_19
    | ~ spl6_20
    | spl6_21 ),
    inference(avatar_split_clause,[],[f169,f137,f121,f118,f174,f103,f171,f97,f76])).

fof(f169,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_borsuk_1(sK2,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v1_borsuk_1(sK3,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | spl6_21 ),
    inference(resolution,[],[f138,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r4_tsep_1(X0,X1,X2)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_borsuk_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_borsuk_1(X2,X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_tsep_1(X0,X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_borsuk_1(X2,X0) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_borsuk_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_tsep_1(X0,X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_borsuk_1(X2,X0) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_borsuk_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v1_borsuk_1(X1,X0) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_borsuk_1(X2,X0) )
             => r4_tsep_1(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_tsep_1)).

fof(f138,plain,
    ( ~ r4_tsep_1(sK0,sK2,sK3)
    | spl6_21 ),
    inference(avatar_component_clause,[],[f137])).

fof(f162,plain,(
    spl6_14 ),
    inference(avatar_contradiction_clause,[],[f161])).

fof(f161,plain,
    ( $false
    | spl6_14 ),
    inference(resolution,[],[f104,f37])).

fof(f104,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | spl6_14 ),
    inference(avatar_component_clause,[],[f103])).

fof(f153,plain,(
    spl6_12 ),
    inference(avatar_contradiction_clause,[],[f152])).

fof(f152,plain,
    ( $false
    | spl6_12 ),
    inference(resolution,[],[f98,f34])).

fof(f98,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | spl6_12 ),
    inference(avatar_component_clause,[],[f97])).

fof(f151,plain,(
    spl6_20 ),
    inference(avatar_contradiction_clause,[],[f150])).

fof(f150,plain,
    ( $false
    | spl6_20 ),
    inference(resolution,[],[f122,f42])).

fof(f122,plain,
    ( ~ v2_pre_topc(sK0)
    | spl6_20 ),
    inference(avatar_component_clause,[],[f121])).

fof(f149,plain,(
    spl6_19 ),
    inference(avatar_contradiction_clause,[],[f148])).

fof(f148,plain,
    ( $false
    | spl6_19 ),
    inference(resolution,[],[f119,f43])).

fof(f119,plain,
    ( ~ l1_pre_topc(sK0)
    | spl6_19 ),
    inference(avatar_component_clause,[],[f118])).

fof(f147,plain,(
    spl6_17 ),
    inference(avatar_contradiction_clause,[],[f146])).

fof(f146,plain,
    ( $false
    | spl6_17 ),
    inference(resolution,[],[f113,f39])).

fof(f39,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f113,plain,
    ( ~ v2_pre_topc(sK1)
    | spl6_17 ),
    inference(avatar_component_clause,[],[f112])).

fof(f145,plain,
    ( ~ spl6_21
    | ~ spl6_22
    | spl6_23 ),
    inference(avatar_split_clause,[],[f135,f143,f140,f137])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),sK0,X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ r1_tsep_1(sK2,sK3)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
      | ~ v5_pre_topc(X1,sK2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
      | ~ v5_pre_topc(X2,sK3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
      | ~ r4_tsep_1(sK0,sK2,sK3) ) ),
    inference(global_subsumption,[],[f32,f35,f41,f42,f43,f34,f37,f134])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),sK0,X0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,sK0)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ r1_tsep_1(sK2,sK3)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
      | ~ v5_pre_topc(X1,sK2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0))
      | ~ v5_pre_topc(X2,sK3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))
      | ~ r4_tsep_1(sK0,sK2,sK3)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f53,f25])).

fof(f53,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ r1_tsep_1(X2,X3)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v5_pre_topc(X4,X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v5_pre_topc(X5,X3,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ r4_tsep_1(X0,X2,X3)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                            & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                          | ~ r4_tsep_1(X0,X2,X3)
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v5_pre_topc(X5,X3,X1)
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v5_pre_topc(X4,X2,X1)
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ r1_tsep_1(X2,X3)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                            & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                          | ~ r4_tsep_1(X0,X2,X3)
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v5_pre_topc(X5,X3,X1)
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v5_pre_topc(X4,X2,X1)
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ r1_tsep_1(X2,X3)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( r1_tsep_1(X2,X3)
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(X4,X2,X1)
                          & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v5_pre_topc(X5,X3,X1)
                              & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => ( r4_tsep_1(X0,X2,X3)
                             => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                                & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                                & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                                & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_tmap_1)).

fof(f133,plain,(
    spl6_16 ),
    inference(avatar_contradiction_clause,[],[f132])).

fof(f132,plain,
    ( $false
    | spl6_16 ),
    inference(resolution,[],[f110,f40])).

fof(f40,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f110,plain,
    ( ~ l1_pre_topc(sK1)
    | spl6_16 ),
    inference(avatar_component_clause,[],[f109])).

fof(f131,plain,(
    spl6_11 ),
    inference(avatar_contradiction_clause,[],[f130])).

fof(f130,plain,
    ( $false
    | spl6_11 ),
    inference(resolution,[],[f95,f28])).

fof(f28,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f9])).

fof(f95,plain,
    ( ~ v1_funct_1(sK4)
    | spl6_11 ),
    inference(avatar_component_clause,[],[f94])).

fof(f127,plain,(
    spl6_8 ),
    inference(avatar_contradiction_clause,[],[f126])).

fof(f126,plain,
    ( $false
    | spl6_8 ),
    inference(resolution,[],[f86,f21])).

fof(f21,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f9])).

fof(f86,plain,
    ( ~ v1_funct_1(sK5)
    | spl6_8 ),
    inference(avatar_component_clause,[],[f85])).

fof(f71,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f20,f69,f66,f63,f60])).

fof(f20,plain,
    ( ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1)
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:22:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.45  % (12370)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.20/0.45  % (12362)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.20/0.46  % (12359)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.46  % (12351)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.46  % (12370)Refutation not found, incomplete strategy% (12370)------------------------------
% 0.20/0.46  % (12370)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (12370)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.46  
% 0.20/0.46  % (12370)Memory used [KB]: 10746
% 0.20/0.46  % (12370)Time elapsed: 0.039 s
% 0.20/0.46  % (12370)------------------------------
% 0.20/0.46  % (12370)------------------------------
% 0.20/0.47  % (12359)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % (12354)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f254,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f71,f127,f131,f133,f145,f147,f149,f151,f153,f162,f176,f178,f180,f184,f186,f188,f190,f192,f194,f196,f198,f206,f220,f222,f229,f231,f233,f235,f246,f253])).
% 0.20/0.48  fof(f253,plain,(
% 0.20/0.48    spl6_31),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f251])).
% 0.20/0.48  fof(f251,plain,(
% 0.20/0.48    $false | spl6_31),
% 0.20/0.48    inference(resolution,[],[f245,f72])).
% 0.20/0.48  fof(f72,plain,(
% 0.20/0.48    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4)),
% 0.20/0.48    inference(forward_demodulation,[],[f26,f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    sK0 = k1_tsep_1(sK0,sK2,sK3)),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f8])).
% 0.20/0.48  fof(f8,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0)) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,negated_conjecture,(
% 0.20/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))))))))),
% 0.20/0.48    inference(negated_conjecture,[],[f6])).
% 0.20/0.48  fof(f6,conjecture,(
% 0.20/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) & k1_tsep_1(X0,X2,X3) = X0) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),X0,X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))))))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_tmap_1)).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4)),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f245,plain,(
% 0.20/0.48    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4) | spl6_31),
% 0.20/0.48    inference(avatar_component_clause,[],[f244])).
% 0.20/0.48  fof(f244,plain,(
% 0.20/0.48    spl6_31 <=> r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 0.20/0.48  fof(f246,plain,(
% 0.20/0.48    spl6_2 | spl6_18 | ~spl6_17 | ~spl6_16 | ~spl6_11 | ~spl6_10 | ~spl6_9 | ~spl6_8 | ~spl6_7 | ~spl6_6 | ~spl6_28 | ~spl6_29 | ~spl6_31 | ~spl6_30),
% 0.20/0.48    inference(avatar_split_clause,[],[f236,f225,f244,f204,f201,f79,f82,f85,f88,f91,f94,f109,f112,f115,f63])).
% 0.20/0.48  fof(f63,plain,(
% 0.20/0.48    spl6_2 <=> v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.48  fof(f115,plain,(
% 0.20/0.48    spl6_18 <=> v2_struct_0(sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.20/0.48  fof(f112,plain,(
% 0.20/0.48    spl6_17 <=> v2_pre_topc(sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.20/0.48  fof(f109,plain,(
% 0.20/0.48    spl6_16 <=> l1_pre_topc(sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.20/0.48  fof(f94,plain,(
% 0.20/0.48    spl6_11 <=> v1_funct_1(sK4)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.20/0.48  fof(f91,plain,(
% 0.20/0.48    spl6_10 <=> v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.20/0.48  fof(f88,plain,(
% 0.20/0.48    spl6_9 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.20/0.48  fof(f85,plain,(
% 0.20/0.48    spl6_8 <=> v1_funct_1(sK5)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.20/0.48  fof(f82,plain,(
% 0.20/0.48    spl6_7 <=> v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.20/0.48  fof(f79,plain,(
% 0.20/0.48    spl6_6 <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.20/0.48  fof(f201,plain,(
% 0.20/0.48    spl6_28 <=> v5_pre_topc(sK4,sK2,sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 0.20/0.48  fof(f204,plain,(
% 0.20/0.48    spl6_29 <=> v5_pre_topc(sK5,sK3,sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 0.20/0.48  fof(f225,plain,(
% 0.20/0.48    spl6_30 <=> ! [X1,X0,X2] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),k3_tmap_1(sK0,X0,sK0,sK2,k10_tmap_1(sK0,X0,sK2,sK3,X1,X2)),X1) | v5_pre_topc(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),sK0,X0) | ~v5_pre_topc(X2,sK3,X0) | ~v5_pre_topc(X1,sK2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),k3_tmap_1(sK0,X0,sK0,sK3,k10_tmap_1(sK0,X0,sK2,sK3,X1,X2)),X2))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 0.20/0.48  fof(f236,plain,(
% 0.20/0.48    ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK2,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK4) | ~v5_pre_topc(sK5,sK3,sK1) | ~v5_pre_topc(sK4,sK2,sK1) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1) | ~spl6_30),
% 0.20/0.48    inference(resolution,[],[f226,f73])).
% 0.20/0.48  fof(f73,plain,(
% 0.20/0.48    r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,sK0,sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)),
% 0.20/0.48    inference(forward_demodulation,[],[f27,f25])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    r2_funct_2(u1_struct_0(sK3),u1_struct_0(sK1),k3_tmap_1(sK0,sK1,k1_tsep_1(sK0,sK2,sK3),sK3,k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)),sK5)),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f226,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),k3_tmap_1(sK0,X0,sK0,sK3,k10_tmap_1(sK0,X0,sK2,sK3,X1,X2)),X2) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),k3_tmap_1(sK0,X0,sK0,sK2,k10_tmap_1(sK0,X0,sK2,sK3,X1,X2)),X1) | ~v5_pre_topc(X2,sK3,X0) | ~v5_pre_topc(X1,sK2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v5_pre_topc(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),sK0,X0)) ) | ~spl6_30),
% 0.20/0.48    inference(avatar_component_clause,[],[f225])).
% 0.20/0.48  fof(f235,plain,(
% 0.20/0.48    ~spl6_15),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f234])).
% 0.20/0.48  fof(f234,plain,(
% 0.20/0.48    $false | ~spl6_15),
% 0.20/0.48    inference(resolution,[],[f107,f35])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ~v2_struct_0(sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f107,plain,(
% 0.20/0.48    v2_struct_0(sK2) | ~spl6_15),
% 0.20/0.48    inference(avatar_component_clause,[],[f106])).
% 0.20/0.48  fof(f106,plain,(
% 0.20/0.48    spl6_15 <=> v2_struct_0(sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.20/0.48  fof(f233,plain,(
% 0.20/0.48    spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_12 | spl6_13 | ~spl6_14 | spl6_15 | ~spl6_16 | ~spl6_17 | spl6_18 | ~spl6_19 | ~spl6_20 | spl6_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f232,f69,f121,f118,f115,f112,f109,f106,f103,f100,f97,f94,f91,f88,f85,f82,f79,f76])).
% 0.20/0.48  fof(f76,plain,(
% 0.20/0.48    spl6_5 <=> v2_struct_0(sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.20/0.48  fof(f97,plain,(
% 0.20/0.48    spl6_12 <=> m1_pre_topc(sK3,sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.20/0.48  fof(f100,plain,(
% 0.20/0.48    spl6_13 <=> v2_struct_0(sK3)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.20/0.48  fof(f103,plain,(
% 0.20/0.48    spl6_14 <=> m1_pre_topc(sK2,sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.20/0.48  fof(f118,plain,(
% 0.20/0.48    spl6_19 <=> l1_pre_topc(sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.20/0.48  fof(f121,plain,(
% 0.20/0.48    spl6_20 <=> v2_pre_topc(sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.20/0.48  fof(f69,plain,(
% 0.20/0.48    spl6_4 <=> v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.20/0.48  fof(f232,plain,(
% 0.20/0.48    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | v2_struct_0(sK0) | spl6_4),
% 0.20/0.48    inference(resolution,[],[f70,f56])).
% 0.20/0.48  fof(f56,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | v2_struct_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_tmap_1)).
% 0.20/0.48  fof(f70,plain,(
% 0.20/0.48    ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | spl6_4),
% 0.20/0.48    inference(avatar_component_clause,[],[f69])).
% 0.20/0.48  fof(f231,plain,(
% 0.20/0.48    ~spl6_13),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f230])).
% 0.20/0.48  fof(f230,plain,(
% 0.20/0.48    $false | ~spl6_13),
% 0.20/0.48    inference(resolution,[],[f101,f32])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ~v2_struct_0(sK3)),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f101,plain,(
% 0.20/0.48    v2_struct_0(sK3) | ~spl6_13),
% 0.20/0.48    inference(avatar_component_clause,[],[f100])).
% 0.20/0.48  fof(f229,plain,(
% 0.20/0.48    ~spl6_21 | spl6_22 | spl6_30),
% 0.20/0.48    inference(avatar_split_clause,[],[f228,f225,f140,f137])).
% 0.20/0.48  fof(f137,plain,(
% 0.20/0.48    spl6_21 <=> r4_tsep_1(sK0,sK2,sK3)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.20/0.48  fof(f140,plain,(
% 0.20/0.48    spl6_22 <=> r1_tsep_1(sK2,sK3)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 0.20/0.48  fof(f228,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),k3_tmap_1(sK0,X0,sK0,sK3,k10_tmap_1(sK0,X0,sK2,sK3,X1,X2)),X2) | ~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),k3_tmap_1(sK0,X0,sK0,sK2,k10_tmap_1(sK0,X0,sK2,sK3,X1,X2)),X1) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | r1_tsep_1(sK2,sK3) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v5_pre_topc(X1,sK2,X0) | ~v5_pre_topc(X2,sK3,X0) | ~r4_tsep_1(sK0,sK2,sK3) | v5_pre_topc(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),sK0,X0)) )),
% 0.20/0.48    inference(global_subsumption,[],[f223])).
% 0.20/0.48  fof(f223,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),k3_tmap_1(sK0,X0,sK0,sK2,k10_tmap_1(sK0,X0,sK2,sK3,X1,X2)),X1) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),k3_tmap_1(sK0,X0,sK0,sK3,k10_tmap_1(sK0,X0,sK2,sK3,X1,X2)),X2) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | r1_tsep_1(sK2,sK3) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v5_pre_topc(X1,sK2,X0) | ~v5_pre_topc(X2,sK3,X0) | ~r4_tsep_1(sK0,sK2,sK3) | v5_pre_topc(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),sK0,X0)) )),
% 0.20/0.48    inference(global_subsumption,[],[f32,f35,f41,f42,f43,f34,f37,f213])).
% 0.20/0.48  fof(f213,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),k3_tmap_1(sK0,X0,sK0,sK2,k10_tmap_1(sK0,X0,sK2,sK3,X1,X2)),X1) | ~r2_funct_2(u1_struct_0(sK3),u1_struct_0(X0),k3_tmap_1(sK0,X0,sK0,sK3,k10_tmap_1(sK0,X0,sK2,sK3,X1,X2)),X2) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | r1_tsep_1(sK2,sK3) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~v5_pre_topc(X1,sK2,X0) | ~v5_pre_topc(X2,sK3,X0) | ~r4_tsep_1(sK0,sK2,sK3) | v5_pre_topc(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),sK0,X0)) )),
% 0.20/0.48    inference(superposition,[],[f182,f25])).
% 0.20/0.48  fof(f182,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | r1_tsep_1(X2,X3) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~v5_pre_topc(X4,X2,X1) | ~v5_pre_topc(X5,X3,X1) | ~r4_tsep_1(X0,X2,X3) | v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)) )),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f181])).
% 0.20/0.48  fof(f181,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | r1_tsep_1(X2,X3) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | v2_struct_0(X0) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) | ~r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | r1_tsep_1(X2,X3) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v5_pre_topc(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v5_pre_topc(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | v2_struct_0(X0) | ~r4_tsep_1(X0,X2,X3) | v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)) )),
% 0.20/0.48    inference(resolution,[],[f48,f46])).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | r1_tsep_1(X2,X3) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v5_pre_topc(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v5_pre_topc(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | v2_struct_0(X0) | ~r4_tsep_1(X0,X2,X3) | v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~r4_tsep_1(X0,X2,X3) | ~r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(X5,X3,X1) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(X4,X2,X1) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | r1_tsep_1(X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f10])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X4] : (! [X5] : (((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | (~r4_tsep_1(X0,X2,X3) | ~r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(X5,X3,X1) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(X4,X2,X1) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | r1_tsep_1(X2,X3)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~r1_tsep_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)))))))))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_tmap_1)).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | r1_tsep_1(X2,X3) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | v2_struct_0(X0) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) | ~r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)) <=> r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | r1_tsep_1(X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X4] : (! [X5] : (((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)) <=> r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | r1_tsep_1(X2,X3)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~r1_tsep_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)) <=> r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))))))))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_tmap_1)).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    m1_pre_topc(sK2,sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    m1_pre_topc(sK3,sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    l1_pre_topc(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    v2_pre_topc(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    ~v2_struct_0(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f222,plain,(
% 0.20/0.48    spl6_29),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f221])).
% 0.20/0.48  fof(f221,plain,(
% 0.20/0.48    $false | spl6_29),
% 0.20/0.48    inference(resolution,[],[f205,f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    v5_pre_topc(sK5,sK3,sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f205,plain,(
% 0.20/0.48    ~v5_pre_topc(sK5,sK3,sK1) | spl6_29),
% 0.20/0.48    inference(avatar_component_clause,[],[f204])).
% 0.20/0.48  fof(f220,plain,(
% 0.20/0.48    spl6_28),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f219])).
% 0.20/0.48  fof(f219,plain,(
% 0.20/0.48    $false | spl6_28),
% 0.20/0.48    inference(resolution,[],[f202,f30])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    v5_pre_topc(sK4,sK2,sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f202,plain,(
% 0.20/0.48    ~v5_pre_topc(sK4,sK2,sK1) | spl6_28),
% 0.20/0.48    inference(avatar_component_clause,[],[f201])).
% 0.20/0.48  fof(f206,plain,(
% 0.20/0.48    spl6_18 | ~spl6_17 | ~spl6_16 | ~spl6_11 | ~spl6_10 | ~spl6_28 | ~spl6_9 | ~spl6_8 | ~spl6_7 | ~spl6_29 | ~spl6_6 | spl6_2 | ~spl6_23),
% 0.20/0.48    inference(avatar_split_clause,[],[f199,f143,f63,f79,f204,f82,f85,f88,f201,f91,f94,f109,f112,f115])).
% 0.20/0.48  fof(f143,plain,(
% 0.20/0.48    spl6_23 <=> ! [X1,X0,X2] : (v5_pre_topc(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),sK0,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v5_pre_topc(X2,sK3,X0) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v5_pre_topc(X1,sK2,X0) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.20/0.48  fof(f199,plain,(
% 0.20/0.48    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(sK5,sK3,sK1) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v5_pre_topc(sK4,sK2,sK1) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (spl6_2 | ~spl6_23)),
% 0.20/0.48    inference(resolution,[],[f144,f64])).
% 0.20/0.48  fof(f64,plain,(
% 0.20/0.48    ~v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1) | spl6_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f63])).
% 0.20/0.48  fof(f144,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (v5_pre_topc(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),sK0,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~v5_pre_topc(X2,sK3,X0) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v5_pre_topc(X1,sK2,X0) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl6_23),
% 0.20/0.48    inference(avatar_component_clause,[],[f143])).
% 0.20/0.48  fof(f198,plain,(
% 0.20/0.48    ~spl6_18),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f197])).
% 0.20/0.48  fof(f197,plain,(
% 0.20/0.48    $false | ~spl6_18),
% 0.20/0.48    inference(resolution,[],[f116,f38])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ~v2_struct_0(sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f116,plain,(
% 0.20/0.48    v2_struct_0(sK1) | ~spl6_18),
% 0.20/0.48    inference(avatar_component_clause,[],[f115])).
% 0.20/0.48  fof(f196,plain,(
% 0.20/0.48    ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_16 | ~spl6_17 | spl6_18 | spl6_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f195,f60,f115,f112,f109,f94,f91,f88,f85,f82,f79])).
% 0.20/0.48  fof(f60,plain,(
% 0.20/0.48    spl6_1 <=> m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.48  fof(f195,plain,(
% 0.20/0.48    v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | spl6_1),
% 0.20/0.48    inference(resolution,[],[f129,f61])).
% 0.20/0.48  fof(f61,plain,(
% 0.20/0.48    ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | spl6_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f60])).
% 0.20/0.48  fof(f129,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))) )),
% 0.20/0.48    inference(global_subsumption,[],[f32,f35,f41,f42,f43,f34,f37,f128])).
% 0.20/0.48  fof(f128,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (m1_subset_1(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | v2_struct_0(sK0)) )),
% 0.20/0.48    inference(superposition,[],[f58,f25])).
% 0.20/0.48  fof(f58,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | v2_struct_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f19])).
% 0.20/0.48  fof(f194,plain,(
% 0.20/0.48    ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_16 | ~spl6_17 | spl6_18 | spl6_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f193,f66,f115,f112,f109,f94,f91,f88,f85,f82,f79])).
% 0.20/0.48  fof(f66,plain,(
% 0.20/0.48    spl6_3 <=> v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.48  fof(f193,plain,(
% 0.20/0.48    v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK4) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_1(sK5) | ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | spl6_3),
% 0.20/0.48    inference(resolution,[],[f125,f67])).
% 0.20/0.48  fof(f67,plain,(
% 0.20/0.48    ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) | spl6_3),
% 0.20/0.48    inference(avatar_component_clause,[],[f66])).
% 0.20/0.48  fof(f125,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),u1_struct_0(sK0),u1_struct_0(X0)) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0))))) )),
% 0.20/0.48    inference(global_subsumption,[],[f32,f35,f41,f42,f43,f34,f37,f124])).
% 0.20/0.48  fof(f124,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (v1_funct_2(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),u1_struct_0(sK0),u1_struct_0(X0)) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | v2_struct_0(sK0)) )),
% 0.20/0.48    inference(superposition,[],[f57,f25])).
% 0.20/0.48  fof(f57,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | v2_struct_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f19])).
% 0.20/0.48  fof(f192,plain,(
% 0.20/0.48    spl6_9),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f191])).
% 0.20/0.48  fof(f191,plain,(
% 0.20/0.48    $false | spl6_9),
% 0.20/0.48    inference(resolution,[],[f89,f31])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f89,plain,(
% 0.20/0.48    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | spl6_9),
% 0.20/0.48    inference(avatar_component_clause,[],[f88])).
% 0.20/0.48  fof(f190,plain,(
% 0.20/0.48    spl6_6),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f189])).
% 0.20/0.48  fof(f189,plain,(
% 0.20/0.48    $false | spl6_6),
% 0.20/0.48    inference(resolution,[],[f80,f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f80,plain,(
% 0.20/0.48    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | spl6_6),
% 0.20/0.48    inference(avatar_component_clause,[],[f79])).
% 0.20/0.48  fof(f188,plain,(
% 0.20/0.48    spl6_10),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f187])).
% 0.20/0.48  fof(f187,plain,(
% 0.20/0.48    $false | spl6_10),
% 0.20/0.48    inference(resolution,[],[f92,f29])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1))),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f92,plain,(
% 0.20/0.48    ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK1)) | spl6_10),
% 0.20/0.48    inference(avatar_component_clause,[],[f91])).
% 0.20/0.48  fof(f186,plain,(
% 0.20/0.48    spl6_7),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f185])).
% 0.20/0.48  fof(f185,plain,(
% 0.20/0.48    $false | spl6_7),
% 0.20/0.48    inference(resolution,[],[f83,f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1))),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f83,plain,(
% 0.20/0.48    ~v1_funct_2(sK5,u1_struct_0(sK3),u1_struct_0(sK1)) | spl6_7),
% 0.20/0.48    inference(avatar_component_clause,[],[f82])).
% 0.20/0.48  fof(f184,plain,(
% 0.20/0.48    ~spl6_5),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f183])).
% 0.20/0.48  fof(f183,plain,(
% 0.20/0.48    $false | ~spl6_5),
% 0.20/0.48    inference(resolution,[],[f77,f41])).
% 0.20/0.48  fof(f77,plain,(
% 0.20/0.48    v2_struct_0(sK0) | ~spl6_5),
% 0.20/0.48    inference(avatar_component_clause,[],[f76])).
% 0.20/0.48  fof(f180,plain,(
% 0.20/0.48    spl6_27),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f179])).
% 0.20/0.48  fof(f179,plain,(
% 0.20/0.48    $false | spl6_27),
% 0.20/0.48    inference(resolution,[],[f175,f36])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    v1_borsuk_1(sK2,sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f175,plain,(
% 0.20/0.48    ~v1_borsuk_1(sK2,sK0) | spl6_27),
% 0.20/0.48    inference(avatar_component_clause,[],[f174])).
% 0.20/0.48  fof(f174,plain,(
% 0.20/0.48    spl6_27 <=> v1_borsuk_1(sK2,sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 0.20/0.48  fof(f178,plain,(
% 0.20/0.48    spl6_26),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f177])).
% 0.20/0.48  fof(f177,plain,(
% 0.20/0.48    $false | spl6_26),
% 0.20/0.48    inference(resolution,[],[f172,f33])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    v1_borsuk_1(sK3,sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f172,plain,(
% 0.20/0.48    ~v1_borsuk_1(sK3,sK0) | spl6_26),
% 0.20/0.48    inference(avatar_component_clause,[],[f171])).
% 0.20/0.48  fof(f171,plain,(
% 0.20/0.48    spl6_26 <=> v1_borsuk_1(sK3,sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 0.20/0.48  fof(f176,plain,(
% 0.20/0.48    spl6_5 | ~spl6_12 | ~spl6_26 | ~spl6_14 | ~spl6_27 | ~spl6_19 | ~spl6_20 | spl6_21),
% 0.20/0.48    inference(avatar_split_clause,[],[f169,f137,f121,f118,f174,f103,f171,f97,f76])).
% 0.20/0.48  fof(f169,plain,(
% 0.20/0.48    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_borsuk_1(sK2,sK0) | ~m1_pre_topc(sK2,sK0) | ~v1_borsuk_1(sK3,sK0) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK0) | spl6_21),
% 0.20/0.48    inference(resolution,[],[f138,f55])).
% 0.20/0.48  fof(f55,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (r4_tsep_1(X0,X1,X2) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_borsuk_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X2,X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (r4_tsep_1(X0,X1,X2) | ~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0)) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (r4_tsep_1(X0,X1,X2) | (~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0))) | (~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)) => r4_tsep_1(X0,X1,X2))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_tsep_1)).
% 0.20/0.48  fof(f138,plain,(
% 0.20/0.48    ~r4_tsep_1(sK0,sK2,sK3) | spl6_21),
% 0.20/0.48    inference(avatar_component_clause,[],[f137])).
% 0.20/0.48  fof(f162,plain,(
% 0.20/0.48    spl6_14),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f161])).
% 0.20/0.48  fof(f161,plain,(
% 0.20/0.48    $false | spl6_14),
% 0.20/0.48    inference(resolution,[],[f104,f37])).
% 0.20/0.48  fof(f104,plain,(
% 0.20/0.48    ~m1_pre_topc(sK2,sK0) | spl6_14),
% 0.20/0.48    inference(avatar_component_clause,[],[f103])).
% 0.20/0.48  fof(f153,plain,(
% 0.20/0.48    spl6_12),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f152])).
% 0.20/0.48  fof(f152,plain,(
% 0.20/0.48    $false | spl6_12),
% 0.20/0.48    inference(resolution,[],[f98,f34])).
% 0.20/0.48  fof(f98,plain,(
% 0.20/0.48    ~m1_pre_topc(sK3,sK0) | spl6_12),
% 0.20/0.48    inference(avatar_component_clause,[],[f97])).
% 0.20/0.48  fof(f151,plain,(
% 0.20/0.48    spl6_20),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f150])).
% 0.20/0.48  fof(f150,plain,(
% 0.20/0.48    $false | spl6_20),
% 0.20/0.48    inference(resolution,[],[f122,f42])).
% 0.20/0.48  fof(f122,plain,(
% 0.20/0.48    ~v2_pre_topc(sK0) | spl6_20),
% 0.20/0.48    inference(avatar_component_clause,[],[f121])).
% 0.20/0.48  fof(f149,plain,(
% 0.20/0.48    spl6_19),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f148])).
% 0.20/0.48  fof(f148,plain,(
% 0.20/0.48    $false | spl6_19),
% 0.20/0.48    inference(resolution,[],[f119,f43])).
% 0.20/0.48  fof(f119,plain,(
% 0.20/0.48    ~l1_pre_topc(sK0) | spl6_19),
% 0.20/0.48    inference(avatar_component_clause,[],[f118])).
% 0.20/0.48  fof(f147,plain,(
% 0.20/0.48    spl6_17),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f146])).
% 0.20/0.48  fof(f146,plain,(
% 0.20/0.48    $false | spl6_17),
% 0.20/0.48    inference(resolution,[],[f113,f39])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    v2_pre_topc(sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f113,plain,(
% 0.20/0.48    ~v2_pre_topc(sK1) | spl6_17),
% 0.20/0.48    inference(avatar_component_clause,[],[f112])).
% 0.20/0.48  fof(f145,plain,(
% 0.20/0.48    ~spl6_21 | ~spl6_22 | spl6_23),
% 0.20/0.48    inference(avatar_split_clause,[],[f135,f143,f140,f137])).
% 0.20/0.48  fof(f135,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (v5_pre_topc(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),sK0,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~r1_tsep_1(sK2,sK3) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v5_pre_topc(X1,sK2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~v5_pre_topc(X2,sK3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~r4_tsep_1(sK0,sK2,sK3)) )),
% 0.20/0.48    inference(global_subsumption,[],[f32,f35,f41,f42,f43,f34,f37,f134])).
% 0.20/0.48  fof(f134,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (v5_pre_topc(k10_tmap_1(sK0,X0,sK2,sK3,X1,X2),sK0,X0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~r1_tsep_1(sK2,sK3) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v5_pre_topc(X1,sK2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK3),u1_struct_0(X0)) | ~v5_pre_topc(X2,sK3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0)))) | ~r4_tsep_1(sK0,sK2,sK3) | v2_struct_0(sK0)) )),
% 0.20/0.48    inference(superposition,[],[f53,f25])).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~r1_tsep_1(X2,X3) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v5_pre_topc(X4,X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v5_pre_topc(X5,X3,X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~r4_tsep_1(X0,X2,X3) | v2_struct_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~r4_tsep_1(X0,X2,X3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(X5,X3,X1) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(X4,X2,X1) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r1_tsep_1(X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X4] : (! [X5] : (((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~r4_tsep_1(X0,X2,X3)) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(X5,X3,X1) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(X4,X2,X1) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~r1_tsep_1(X2,X3)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (r1_tsep_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => (r4_tsep_1(X0,X2,X3) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)))))))))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_tmap_1)).
% 0.20/0.48  fof(f133,plain,(
% 0.20/0.48    spl6_16),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f132])).
% 0.20/0.48  fof(f132,plain,(
% 0.20/0.48    $false | spl6_16),
% 0.20/0.48    inference(resolution,[],[f110,f40])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    l1_pre_topc(sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f110,plain,(
% 0.20/0.48    ~l1_pre_topc(sK1) | spl6_16),
% 0.20/0.48    inference(avatar_component_clause,[],[f109])).
% 0.20/0.48  fof(f131,plain,(
% 0.20/0.48    spl6_11),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f130])).
% 0.20/0.48  fof(f130,plain,(
% 0.20/0.48    $false | spl6_11),
% 0.20/0.48    inference(resolution,[],[f95,f28])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    v1_funct_1(sK4)),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f95,plain,(
% 0.20/0.48    ~v1_funct_1(sK4) | spl6_11),
% 0.20/0.48    inference(avatar_component_clause,[],[f94])).
% 0.20/0.48  fof(f127,plain,(
% 0.20/0.48    spl6_8),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f126])).
% 0.20/0.48  fof(f126,plain,(
% 0.20/0.48    $false | spl6_8),
% 0.20/0.48    inference(resolution,[],[f86,f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    v1_funct_1(sK5)),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f86,plain,(
% 0.20/0.48    ~v1_funct_1(sK5) | spl6_8),
% 0.20/0.48    inference(avatar_component_clause,[],[f85])).
% 0.20/0.48  fof(f71,plain,(
% 0.20/0.48    ~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f20,f69,f66,f63,f60])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ~v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK0,sK1) | ~m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (12359)------------------------------
% 0.20/0.48  % (12359)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (12359)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (12359)Memory used [KB]: 11001
% 0.20/0.48  % (12359)Time elapsed: 0.054 s
% 0.20/0.48  % (12359)------------------------------
% 0.20/0.48  % (12359)------------------------------
% 0.20/0.49  % (12346)Success in time 0.128 s
%------------------------------------------------------------------------------
