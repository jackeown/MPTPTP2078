%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1775+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:32 EST 2020

% Result     : Theorem 17.98s
% Output     : Refutation 17.98s
% Verified   : 
% Statistics : Number of formulae       :  175 ( 916 expanded)
%              Number of leaves         :   41 ( 452 expanded)
%              Depth                    :   10
%              Number of atoms          : 1247 (9766 expanded)
%              Number of equality atoms :   53 ( 562 expanded)
%              Maximal formula depth    :   27 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13776,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f8498,f8503,f8508,f8513,f8518,f8523,f8528,f8533,f8538,f8543,f8548,f8553,f8558,f8568,f8573,f8578,f8588,f8597,f8603,f8705,f8830,f8872,f8961,f10561,f11216,f11226,f11233,f13774])).

fof(f13774,plain,
    ( spl495_4
    | ~ spl495_5
    | ~ spl495_6
    | spl495_7
    | spl495_8
    | ~ spl495_9
    | ~ spl495_12
    | ~ spl495_13
    | ~ spl495_15
    | ~ spl495_16
    | ~ spl495_17
    | ~ spl495_19
    | spl495_20
    | ~ spl495_30
    | ~ spl495_52
    | ~ spl495_133 ),
    inference(avatar_contradiction_clause,[],[f13773])).

fof(f13773,plain,
    ( $false
    | spl495_4
    | ~ spl495_5
    | ~ spl495_6
    | spl495_7
    | spl495_8
    | ~ spl495_9
    | ~ spl495_12
    | ~ spl495_13
    | ~ spl495_15
    | ~ spl495_16
    | ~ spl495_17
    | ~ spl495_19
    | spl495_20
    | ~ spl495_30
    | ~ spl495_52
    | ~ spl495_133 ),
    inference(subsumption_resolution,[],[f13771,f11215])).

fof(f11215,plain,
    ( r1_tmap_1(sK6,sK5,k7_relat_1(sK8,u1_struct_0(sK6)),sK9)
    | ~ spl495_133 ),
    inference(avatar_component_clause,[],[f11213])).

fof(f11213,plain,
    ( spl495_133
  <=> r1_tmap_1(sK6,sK5,k7_relat_1(sK8,u1_struct_0(sK6)),sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl495_133])])).

fof(f13771,plain,
    ( ~ r1_tmap_1(sK6,sK5,k7_relat_1(sK8,u1_struct_0(sK6)),sK9)
    | spl495_4
    | ~ spl495_5
    | ~ spl495_6
    | spl495_7
    | spl495_8
    | ~ spl495_9
    | ~ spl495_12
    | ~ spl495_13
    | ~ spl495_15
    | ~ spl495_16
    | ~ spl495_17
    | ~ spl495_19
    | spl495_20
    | ~ spl495_30
    | ~ spl495_52 ),
    inference(backward_demodulation,[],[f11250,f13769])).

fof(f13769,plain,
    ( k2_tmap_1(sK7,sK5,sK8,sK6) = k7_relat_1(sK8,u1_struct_0(sK6))
    | spl495_4
    | ~ spl495_5
    | ~ spl495_6
    | spl495_8
    | ~ spl495_9
    | ~ spl495_13
    | ~ spl495_17
    | ~ spl495_19
    | ~ spl495_30
    | ~ spl495_52 ),
    inference(forward_demodulation,[],[f13758,f11033])).

fof(f11033,plain,
    ( ! [X0] : k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,X0) = k7_relat_1(sK8,X0)
    | ~ spl495_9
    | ~ spl495_19 ),
    inference(unit_resulting_resolution,[],[f8537,f8587,f5930])).

fof(f5930,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f3748])).

fof(f3748,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f3747])).

fof(f3747,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1554])).

fof(f1554,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f8587,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5))))
    | ~ spl495_19 ),
    inference(avatar_component_clause,[],[f8585])).

fof(f8585,plain,
    ( spl495_19
  <=> m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl495_19])])).

fof(f8537,plain,
    ( v1_funct_1(sK8)
    | ~ spl495_9 ),
    inference(avatar_component_clause,[],[f8535])).

fof(f8535,plain,
    ( spl495_9
  <=> v1_funct_1(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl495_9])])).

fof(f13758,plain,
    ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(sK6)) = k2_tmap_1(sK7,sK5,sK8,sK6)
    | spl495_4
    | ~ spl495_5
    | ~ spl495_6
    | spl495_8
    | ~ spl495_9
    | ~ spl495_13
    | ~ spl495_17
    | ~ spl495_19
    | ~ spl495_30
    | ~ spl495_52 ),
    inference(unit_resulting_resolution,[],[f8532,f8871,f8704,f8512,f8517,f8522,f8537,f8557,f8577,f8587,f5941])).

fof(f5941,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3756])).

fof(f3756,plain,(
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
    inference(flattening,[],[f3755])).

fof(f3755,plain,(
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
    inference(ennf_transformation,[],[f3330])).

fof(f3330,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f8577,plain,
    ( v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5))
    | ~ spl495_17 ),
    inference(avatar_component_clause,[],[f8575])).

fof(f8575,plain,
    ( spl495_17
  <=> v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl495_17])])).

fof(f8557,plain,
    ( m1_pre_topc(sK6,sK7)
    | ~ spl495_13 ),
    inference(avatar_component_clause,[],[f8555])).

fof(f8555,plain,
    ( spl495_13
  <=> m1_pre_topc(sK6,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl495_13])])).

fof(f8522,plain,
    ( l1_pre_topc(sK5)
    | ~ spl495_6 ),
    inference(avatar_component_clause,[],[f8520])).

fof(f8520,plain,
    ( spl495_6
  <=> l1_pre_topc(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl495_6])])).

fof(f8517,plain,
    ( v2_pre_topc(sK5)
    | ~ spl495_5 ),
    inference(avatar_component_clause,[],[f8515])).

fof(f8515,plain,
    ( spl495_5
  <=> v2_pre_topc(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl495_5])])).

fof(f8512,plain,
    ( ~ v2_struct_0(sK5)
    | spl495_4 ),
    inference(avatar_component_clause,[],[f8510])).

fof(f8510,plain,
    ( spl495_4
  <=> v2_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl495_4])])).

fof(f8704,plain,
    ( l1_pre_topc(sK7)
    | ~ spl495_30 ),
    inference(avatar_component_clause,[],[f8702])).

fof(f8702,plain,
    ( spl495_30
  <=> l1_pre_topc(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl495_30])])).

fof(f8871,plain,
    ( v2_pre_topc(sK7)
    | ~ spl495_52 ),
    inference(avatar_component_clause,[],[f8869])).

fof(f8869,plain,
    ( spl495_52
  <=> v2_pre_topc(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl495_52])])).

fof(f8532,plain,
    ( ~ v2_struct_0(sK7)
    | spl495_8 ),
    inference(avatar_component_clause,[],[f8530])).

fof(f8530,plain,
    ( spl495_8
  <=> v2_struct_0(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl495_8])])).

fof(f11250,plain,
    ( ~ r1_tmap_1(sK6,sK5,k2_tmap_1(sK7,sK5,sK8,sK6),sK9)
    | spl495_4
    | ~ spl495_5
    | ~ spl495_6
    | spl495_7
    | spl495_8
    | ~ spl495_9
    | ~ spl495_12
    | ~ spl495_13
    | ~ spl495_15
    | ~ spl495_16
    | ~ spl495_17
    | ~ spl495_19
    | spl495_20
    | ~ spl495_30
    | ~ spl495_52 ),
    inference(unit_resulting_resolution,[],[f8512,f8517,f8522,f8532,f8871,f8704,f8537,f8527,f8557,f8552,f8572,f8567,f8577,f8587,f8591,f7699])).

fof(f7699,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | r1_tmap_1(X1,X0,X2,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X1)
      | ~ v1_tsep_1(X3,X1)
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
    inference(equality_resolution,[],[f5637])).

fof(f5637,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X1,X0,X2,X4)
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | X4 != X5
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X1)
      | ~ v1_tsep_1(X3,X1)
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
    inference(cnf_transformation,[],[f4788])).

fof(f4788,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r1_tmap_1(X1,X0,X2,X4)
                              | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                            & ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                              | ~ r1_tmap_1(X1,X0,X2,X4) ) )
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | ~ v1_tsep_1(X3,X1)
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
    inference(nnf_transformation,[],[f3526])).

fof(f3526,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( r1_tmap_1(X1,X0,X2,X4)
                          <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | ~ v1_tsep_1(X3,X1)
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
    inference(flattening,[],[f3525])).

fof(f3525,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( r1_tmap_1(X1,X0,X2,X4)
                          <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | ~ v1_tsep_1(X3,X1)
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
    inference(ennf_transformation,[],[f3418])).

fof(f3418,axiom,(
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
                    & v1_tsep_1(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                         => ( X4 = X5
                           => ( r1_tmap_1(X1,X0,X2,X4)
                            <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_tmap_1)).

fof(f8591,plain,
    ( ~ r1_tmap_1(sK7,sK5,sK8,sK9)
    | spl495_20 ),
    inference(avatar_component_clause,[],[f8590])).

fof(f8590,plain,
    ( spl495_20
  <=> r1_tmap_1(sK7,sK5,sK8,sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl495_20])])).

fof(f8567,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK7))
    | ~ spl495_15 ),
    inference(avatar_component_clause,[],[f8565])).

fof(f8565,plain,
    ( spl495_15
  <=> m1_subset_1(sK9,u1_struct_0(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl495_15])])).

fof(f8572,plain,
    ( m1_subset_1(sK9,u1_struct_0(sK6))
    | ~ spl495_16 ),
    inference(avatar_component_clause,[],[f8570])).

fof(f8570,plain,
    ( spl495_16
  <=> m1_subset_1(sK9,u1_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl495_16])])).

fof(f8552,plain,
    ( v1_tsep_1(sK6,sK7)
    | ~ spl495_12 ),
    inference(avatar_component_clause,[],[f8550])).

fof(f8550,plain,
    ( spl495_12
  <=> v1_tsep_1(sK6,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl495_12])])).

fof(f8527,plain,
    ( ~ v2_struct_0(sK6)
    | spl495_7 ),
    inference(avatar_component_clause,[],[f8525])).

fof(f8525,plain,
    ( spl495_7
  <=> v2_struct_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl495_7])])).

fof(f11233,plain,
    ( spl495_1
    | ~ spl495_2
    | ~ spl495_3
    | spl495_4
    | ~ spl495_5
    | ~ spl495_6
    | spl495_7
    | spl495_8
    | ~ spl495_9
    | ~ spl495_10
    | ~ spl495_11
    | ~ spl495_13
    | ~ spl495_15
    | ~ spl495_16
    | ~ spl495_17
    | ~ spl495_19
    | ~ spl495_20
    | spl495_21
    | ~ spl495_30
    | ~ spl495_48
    | ~ spl495_52
    | ~ spl495_127 ),
    inference(avatar_contradiction_clause,[],[f11232])).

fof(f11232,plain,
    ( $false
    | spl495_1
    | ~ spl495_2
    | ~ spl495_3
    | spl495_4
    | ~ spl495_5
    | ~ spl495_6
    | spl495_7
    | spl495_8
    | ~ spl495_9
    | ~ spl495_10
    | ~ spl495_11
    | ~ spl495_13
    | ~ spl495_15
    | ~ spl495_16
    | ~ spl495_17
    | ~ spl495_19
    | ~ spl495_20
    | spl495_21
    | ~ spl495_30
    | ~ spl495_48
    | ~ spl495_52
    | ~ spl495_127 ),
    inference(subsumption_resolution,[],[f11218,f11227])).

fof(f11227,plain,
    ( r1_tmap_1(sK6,sK5,k7_relat_1(sK8,u1_struct_0(sK6)),sK9)
    | spl495_1
    | ~ spl495_2
    | ~ spl495_3
    | spl495_4
    | ~ spl495_5
    | ~ spl495_6
    | spl495_7
    | spl495_8
    | ~ spl495_9
    | ~ spl495_10
    | ~ spl495_11
    | ~ spl495_13
    | ~ spl495_15
    | ~ spl495_16
    | ~ spl495_17
    | ~ spl495_19
    | ~ spl495_20
    | ~ spl495_30
    | ~ spl495_48
    | ~ spl495_52
    | ~ spl495_127 ),
    inference(forward_demodulation,[],[f11221,f11102])).

fof(f11102,plain,
    ( k3_tmap_1(sK4,sK5,sK7,sK6,sK8) = k7_relat_1(sK8,u1_struct_0(sK6))
    | spl495_4
    | ~ spl495_5
    | ~ spl495_6
    | spl495_8
    | ~ spl495_9
    | ~ spl495_13
    | ~ spl495_17
    | ~ spl495_19
    | ~ spl495_30
    | ~ spl495_48
    | ~ spl495_52
    | ~ spl495_127 ),
    inference(backward_demodulation,[],[f10560,f11035])).

fof(f11035,plain,
    ( k3_tmap_1(sK7,sK5,sK7,sK6,sK8) = k7_relat_1(sK8,u1_struct_0(sK6))
    | spl495_4
    | ~ spl495_5
    | ~ spl495_6
    | spl495_8
    | ~ spl495_9
    | ~ spl495_13
    | ~ spl495_17
    | ~ spl495_19
    | ~ spl495_30
    | ~ spl495_48
    | ~ spl495_52 ),
    inference(backward_demodulation,[],[f8920,f11033])).

fof(f8920,plain,
    ( k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(sK6)) = k3_tmap_1(sK7,sK5,sK7,sK6,sK8)
    | spl495_4
    | ~ spl495_5
    | ~ spl495_6
    | spl495_8
    | ~ spl495_9
    | ~ spl495_13
    | ~ spl495_17
    | ~ spl495_19
    | ~ spl495_30
    | ~ spl495_48
    | ~ spl495_52 ),
    inference(unit_resulting_resolution,[],[f8532,f8871,f8704,f8512,f8517,f8522,f8557,f8557,f8537,f8577,f8587,f8829,f5583])).

fof(f5583,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3496])).

fof(f3496,plain,(
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
    inference(flattening,[],[f3495])).

fof(f3495,plain,(
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
    inference(ennf_transformation,[],[f3331])).

fof(f3331,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).

fof(f8829,plain,
    ( m1_pre_topc(sK7,sK7)
    | ~ spl495_48 ),
    inference(avatar_component_clause,[],[f8827])).

fof(f8827,plain,
    ( spl495_48
  <=> m1_pre_topc(sK7,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl495_48])])).

fof(f10560,plain,
    ( k3_tmap_1(sK4,sK5,sK7,sK6,sK8) = k3_tmap_1(sK7,sK5,sK7,sK6,sK8)
    | ~ spl495_127 ),
    inference(avatar_component_clause,[],[f10558])).

fof(f10558,plain,
    ( spl495_127
  <=> k3_tmap_1(sK4,sK5,sK7,sK6,sK8) = k3_tmap_1(sK7,sK5,sK7,sK6,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl495_127])])).

fof(f11221,plain,
    ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK9)
    | spl495_1
    | ~ spl495_2
    | ~ spl495_3
    | spl495_4
    | ~ spl495_5
    | ~ spl495_6
    | spl495_7
    | spl495_8
    | ~ spl495_9
    | ~ spl495_10
    | ~ spl495_11
    | ~ spl495_13
    | ~ spl495_15
    | ~ spl495_16
    | ~ spl495_17
    | ~ spl495_19
    | ~ spl495_20 ),
    inference(unit_resulting_resolution,[],[f8497,f8502,f8507,f8512,f8517,f8522,f8532,f8527,f8547,f8542,f8537,f8557,f8572,f8567,f8577,f8587,f8592,f7684])).

fof(f7684,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ r1_tmap_1(X2,X1,X4,X6)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
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
    inference(equality_resolution,[],[f5568])).

fof(f5568,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
      | ~ r1_tmap_1(X2,X1,X4,X5)
      | ~ m1_pre_topc(X3,X2)
      | X5 != X6
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X2))
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
    inference(cnf_transformation,[],[f3476])).

fof(f3476,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
                              | ~ r1_tmap_1(X2,X1,X4,X5)
                              | ~ m1_pre_topc(X3,X2)
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
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
    inference(flattening,[],[f3475])).

fof(f3475,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
                              | ~ r1_tmap_1(X2,X1,X4,X5)
                              | ~ m1_pre_topc(X3,X2)
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
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
    inference(ennf_transformation,[],[f3434])).

fof(f3434,axiom,(
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
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X2))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X3))
                             => ( ( r1_tmap_1(X2,X1,X4,X5)
                                  & m1_pre_topc(X3,X2)
                                  & X5 = X6 )
                               => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tmap_1)).

fof(f8592,plain,
    ( r1_tmap_1(sK7,sK5,sK8,sK9)
    | ~ spl495_20 ),
    inference(avatar_component_clause,[],[f8590])).

fof(f8542,plain,
    ( m1_pre_topc(sK6,sK4)
    | ~ spl495_10 ),
    inference(avatar_component_clause,[],[f8540])).

fof(f8540,plain,
    ( spl495_10
  <=> m1_pre_topc(sK6,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl495_10])])).

fof(f8547,plain,
    ( m1_pre_topc(sK7,sK4)
    | ~ spl495_11 ),
    inference(avatar_component_clause,[],[f8545])).

fof(f8545,plain,
    ( spl495_11
  <=> m1_pre_topc(sK7,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl495_11])])).

fof(f8507,plain,
    ( l1_pre_topc(sK4)
    | ~ spl495_3 ),
    inference(avatar_component_clause,[],[f8505])).

fof(f8505,plain,
    ( spl495_3
  <=> l1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl495_3])])).

fof(f8502,plain,
    ( v2_pre_topc(sK4)
    | ~ spl495_2 ),
    inference(avatar_component_clause,[],[f8500])).

fof(f8500,plain,
    ( spl495_2
  <=> v2_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl495_2])])).

fof(f8497,plain,
    ( ~ v2_struct_0(sK4)
    | spl495_1 ),
    inference(avatar_component_clause,[],[f8495])).

fof(f8495,plain,
    ( spl495_1
  <=> v2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl495_1])])).

fof(f11218,plain,
    ( ~ r1_tmap_1(sK6,sK5,k7_relat_1(sK8,u1_struct_0(sK6)),sK9)
    | spl495_4
    | ~ spl495_5
    | ~ spl495_6
    | spl495_8
    | ~ spl495_9
    | ~ spl495_13
    | ~ spl495_17
    | ~ spl495_19
    | spl495_21
    | ~ spl495_30
    | ~ spl495_48
    | ~ spl495_52
    | ~ spl495_127 ),
    inference(forward_demodulation,[],[f8595,f11102])).

fof(f8595,plain,
    ( ~ r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK9)
    | spl495_21 ),
    inference(avatar_component_clause,[],[f8594])).

fof(f8594,plain,
    ( spl495_21
  <=> r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl495_21])])).

fof(f11226,plain,
    ( spl495_4
    | ~ spl495_5
    | ~ spl495_6
    | spl495_7
    | spl495_8
    | ~ spl495_9
    | ~ spl495_13
    | ~ spl495_15
    | ~ spl495_16
    | ~ spl495_17
    | ~ spl495_19
    | ~ spl495_20
    | ~ spl495_30
    | ~ spl495_48
    | ~ spl495_52
    | spl495_133 ),
    inference(avatar_contradiction_clause,[],[f11225])).

fof(f11225,plain,
    ( $false
    | spl495_4
    | ~ spl495_5
    | ~ spl495_6
    | spl495_7
    | spl495_8
    | ~ spl495_9
    | ~ spl495_13
    | ~ spl495_15
    | ~ spl495_16
    | ~ spl495_17
    | ~ spl495_19
    | ~ spl495_20
    | ~ spl495_30
    | ~ spl495_48
    | ~ spl495_52
    | spl495_133 ),
    inference(subsumption_resolution,[],[f11224,f11214])).

fof(f11214,plain,
    ( ~ r1_tmap_1(sK6,sK5,k7_relat_1(sK8,u1_struct_0(sK6)),sK9)
    | spl495_133 ),
    inference(avatar_component_clause,[],[f11213])).

fof(f11224,plain,
    ( r1_tmap_1(sK6,sK5,k7_relat_1(sK8,u1_struct_0(sK6)),sK9)
    | spl495_4
    | ~ spl495_5
    | ~ spl495_6
    | spl495_7
    | spl495_8
    | ~ spl495_9
    | ~ spl495_13
    | ~ spl495_15
    | ~ spl495_16
    | ~ spl495_17
    | ~ spl495_19
    | ~ spl495_20
    | ~ spl495_30
    | ~ spl495_48
    | ~ spl495_52 ),
    inference(forward_demodulation,[],[f11222,f11035])).

fof(f11222,plain,
    ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK7,sK5,sK7,sK6,sK8),sK9)
    | spl495_4
    | ~ spl495_5
    | ~ spl495_6
    | spl495_7
    | spl495_8
    | ~ spl495_9
    | ~ spl495_13
    | ~ spl495_15
    | ~ spl495_16
    | ~ spl495_17
    | ~ spl495_19
    | ~ spl495_20
    | ~ spl495_30
    | ~ spl495_48
    | ~ spl495_52 ),
    inference(unit_resulting_resolution,[],[f8532,f8871,f8704,f8512,f8517,f8522,f8532,f8527,f8829,f8557,f8537,f8557,f8572,f8567,f8577,f8587,f8592,f7684])).

fof(f11216,plain,
    ( spl495_133
    | spl495_4
    | ~ spl495_5
    | ~ spl495_6
    | spl495_8
    | ~ spl495_9
    | ~ spl495_13
    | ~ spl495_17
    | ~ spl495_19
    | ~ spl495_30
    | ~ spl495_48
    | ~ spl495_52
    | ~ spl495_53 ),
    inference(avatar_split_clause,[],[f11099,f8958,f8869,f8827,f8702,f8585,f8575,f8555,f8535,f8530,f8520,f8515,f8510,f11213])).

fof(f8958,plain,
    ( spl495_53
  <=> r1_tmap_1(sK6,sK5,k3_tmap_1(sK7,sK5,sK7,sK6,sK8),sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl495_53])])).

fof(f11099,plain,
    ( r1_tmap_1(sK6,sK5,k7_relat_1(sK8,u1_struct_0(sK6)),sK9)
    | spl495_4
    | ~ spl495_5
    | ~ spl495_6
    | spl495_8
    | ~ spl495_9
    | ~ spl495_13
    | ~ spl495_17
    | ~ spl495_19
    | ~ spl495_30
    | ~ spl495_48
    | ~ spl495_52
    | ~ spl495_53 ),
    inference(backward_demodulation,[],[f8960,f11035])).

fof(f8960,plain,
    ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK7,sK5,sK7,sK6,sK8),sK9)
    | ~ spl495_53 ),
    inference(avatar_component_clause,[],[f8958])).

fof(f10561,plain,
    ( spl495_127
    | spl495_1
    | ~ spl495_2
    | ~ spl495_3
    | spl495_4
    | ~ spl495_5
    | ~ spl495_6
    | spl495_8
    | ~ spl495_9
    | ~ spl495_10
    | ~ spl495_11
    | ~ spl495_13
    | ~ spl495_17
    | ~ spl495_19
    | ~ spl495_30
    | ~ spl495_48
    | ~ spl495_52 ),
    inference(avatar_split_clause,[],[f8947,f8869,f8827,f8702,f8585,f8575,f8555,f8545,f8540,f8535,f8530,f8520,f8515,f8510,f8505,f8500,f8495,f10558])).

fof(f8947,plain,
    ( k3_tmap_1(sK4,sK5,sK7,sK6,sK8) = k3_tmap_1(sK7,sK5,sK7,sK6,sK8)
    | spl495_1
    | ~ spl495_2
    | ~ spl495_3
    | spl495_4
    | ~ spl495_5
    | ~ spl495_6
    | spl495_8
    | ~ spl495_9
    | ~ spl495_10
    | ~ spl495_11
    | ~ spl495_13
    | ~ spl495_17
    | ~ spl495_19
    | ~ spl495_30
    | ~ spl495_48
    | ~ spl495_52 ),
    inference(backward_demodulation,[],[f8757,f8920])).

fof(f8757,plain,
    ( k3_tmap_1(sK4,sK5,sK7,sK6,sK8) = k2_partfun1(u1_struct_0(sK7),u1_struct_0(sK5),sK8,u1_struct_0(sK6))
    | spl495_1
    | ~ spl495_2
    | ~ spl495_3
    | spl495_4
    | ~ spl495_5
    | ~ spl495_6
    | ~ spl495_9
    | ~ spl495_10
    | ~ spl495_11
    | ~ spl495_13
    | ~ spl495_17
    | ~ spl495_19 ),
    inference(unit_resulting_resolution,[],[f8497,f8502,f8507,f8512,f8517,f8522,f8547,f8542,f8537,f8557,f8577,f8587,f5583])).

fof(f8961,plain,
    ( spl495_53
    | spl495_1
    | ~ spl495_2
    | ~ spl495_3
    | spl495_4
    | ~ spl495_5
    | ~ spl495_6
    | spl495_8
    | ~ spl495_9
    | ~ spl495_10
    | ~ spl495_11
    | ~ spl495_13
    | ~ spl495_17
    | ~ spl495_19
    | ~ spl495_21
    | ~ spl495_30
    | ~ spl495_48
    | ~ spl495_52 ),
    inference(avatar_split_clause,[],[f8952,f8869,f8827,f8702,f8594,f8585,f8575,f8555,f8545,f8540,f8535,f8530,f8520,f8515,f8510,f8505,f8500,f8495,f8958])).

fof(f8952,plain,
    ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK7,sK5,sK7,sK6,sK8),sK9)
    | spl495_1
    | ~ spl495_2
    | ~ spl495_3
    | spl495_4
    | ~ spl495_5
    | ~ spl495_6
    | spl495_8
    | ~ spl495_9
    | ~ spl495_10
    | ~ spl495_11
    | ~ spl495_13
    | ~ spl495_17
    | ~ spl495_19
    | ~ spl495_21
    | ~ spl495_30
    | ~ spl495_48
    | ~ spl495_52 ),
    inference(backward_demodulation,[],[f8596,f8947])).

fof(f8596,plain,
    ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK9)
    | ~ spl495_21 ),
    inference(avatar_component_clause,[],[f8594])).

fof(f8872,plain,
    ( spl495_52
    | ~ spl495_2
    | ~ spl495_3
    | ~ spl495_11 ),
    inference(avatar_split_clause,[],[f8659,f8545,f8505,f8500,f8869])).

fof(f8659,plain,
    ( v2_pre_topc(sK7)
    | ~ spl495_2
    | ~ spl495_3
    | ~ spl495_11 ),
    inference(unit_resulting_resolution,[],[f8502,f8547,f8507,f5658])).

fof(f5658,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3540])).

fof(f3540,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f3539])).

fof(f3539,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1760])).

fof(f1760,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f8830,plain,
    ( spl495_48
    | ~ spl495_30 ),
    inference(avatar_split_clause,[],[f8714,f8702,f8827])).

fof(f8714,plain,
    ( m1_pre_topc(sK7,sK7)
    | ~ spl495_30 ),
    inference(unit_resulting_resolution,[],[f8704,f5668])).

fof(f5668,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3551])).

fof(f3551,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3376])).

fof(f3376,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f8705,plain,
    ( spl495_30
    | ~ spl495_3
    | ~ spl495_11 ),
    inference(avatar_split_clause,[],[f8635,f8545,f8505,f8702])).

fof(f8635,plain,
    ( l1_pre_topc(sK7)
    | ~ spl495_3
    | ~ spl495_11 ),
    inference(unit_resulting_resolution,[],[f8547,f8507,f5667])).

fof(f5667,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f3550])).

fof(f3550,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1784])).

fof(f1784,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f8603,plain,
    ( ~ spl495_20
    | ~ spl495_21 ),
    inference(avatar_split_clause,[],[f8291,f8594,f8590])).

fof(f8291,plain,
    ( ~ r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK9)
    | ~ r1_tmap_1(sK7,sK5,sK8,sK9) ),
    inference(backward_demodulation,[],[f5562,f5560])).

fof(f5560,plain,(
    sK9 = sK10 ),
    inference(cnf_transformation,[],[f4751])).

fof(f4751,plain,
    ( ( ~ r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10)
      | ~ r1_tmap_1(sK7,sK5,sK8,sK9) )
    & ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10)
      | r1_tmap_1(sK7,sK5,sK8,sK9) )
    & sK9 = sK10
    & m1_subset_1(sK10,u1_struct_0(sK6))
    & m1_subset_1(sK9,u1_struct_0(sK7))
    & m1_pre_topc(sK6,sK7)
    & v1_tsep_1(sK6,sK7)
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5))))
    & v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5))
    & v1_funct_1(sK8)
    & m1_pre_topc(sK7,sK4)
    & ~ v2_struct_0(sK7)
    & m1_pre_topc(sK6,sK4)
    & ~ v2_struct_0(sK6)
    & l1_pre_topc(sK5)
    & v2_pre_topc(sK5)
    & ~ v2_struct_0(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9,sK10])],[f4743,f4750,f4749,f4748,f4747,f4746,f4745,f4744])).

fof(f4744,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                  | ~ r1_tmap_1(X3,X1,X4,X5) )
                                & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                  | r1_tmap_1(X3,X1,X4,X5) )
                                & X5 = X6
                                & m1_subset_1(X6,u1_struct_0(X2)) )
                            & m1_subset_1(X5,u1_struct_0(X3)) )
                        & m1_pre_topc(X2,X3)
                        & v1_tsep_1(X2,X3)
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
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
                              ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(sK4,X1,X3,X2,X4),X6)
                                | ~ r1_tmap_1(X3,X1,X4,X5) )
                              & ( r1_tmap_1(X2,X1,k3_tmap_1(sK4,X1,X3,X2,X4),X6)
                                | r1_tmap_1(X3,X1,X4,X5) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & v1_tsep_1(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK4)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK4)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f4745,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(sK4,X1,X3,X2,X4),X6)
                              | ~ r1_tmap_1(X3,X1,X4,X5) )
                            & ( r1_tmap_1(X2,X1,k3_tmap_1(sK4,X1,X3,X2,X4),X6)
                              | r1_tmap_1(X3,X1,X4,X5) )
                            & X5 = X6
                            & m1_subset_1(X6,u1_struct_0(X2)) )
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & m1_pre_topc(X2,X3)
                    & v1_tsep_1(X2,X3)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,sK4)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK4)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ( ~ r1_tmap_1(X2,sK5,k3_tmap_1(sK4,sK5,X3,X2,X4),X6)
                            | ~ r1_tmap_1(X3,sK5,X4,X5) )
                          & ( r1_tmap_1(X2,sK5,k3_tmap_1(sK4,sK5,X3,X2,X4),X6)
                            | r1_tmap_1(X3,sK5,X4,X5) )
                          & X5 = X6
                          & m1_subset_1(X6,u1_struct_0(X2)) )
                      & m1_subset_1(X5,u1_struct_0(X3)) )
                  & m1_pre_topc(X2,X3)
                  & v1_tsep_1(X2,X3)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK5))))
                  & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK5))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,sK4)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK4)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK5)
      & v2_pre_topc(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f4746,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ( ~ r1_tmap_1(X2,sK5,k3_tmap_1(sK4,sK5,X3,X2,X4),X6)
                          | ~ r1_tmap_1(X3,sK5,X4,X5) )
                        & ( r1_tmap_1(X2,sK5,k3_tmap_1(sK4,sK5,X3,X2,X4),X6)
                          | r1_tmap_1(X3,sK5,X4,X5) )
                        & X5 = X6
                        & m1_subset_1(X6,u1_struct_0(X2)) )
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & m1_pre_topc(X2,X3)
                & v1_tsep_1(X2,X3)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK5))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK5))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,sK4)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK4)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ( ~ r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,X3,sK6,X4),X6)
                        | ~ r1_tmap_1(X3,sK5,X4,X5) )
                      & ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,X3,sK6,X4),X6)
                        | r1_tmap_1(X3,sK5,X4,X5) )
                      & X5 = X6
                      & m1_subset_1(X6,u1_struct_0(sK6)) )
                  & m1_subset_1(X5,u1_struct_0(X3)) )
              & m1_pre_topc(sK6,X3)
              & v1_tsep_1(sK6,X3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK5))))
              & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK5))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,sK4)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK6,sK4)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f4747,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ( ~ r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,X3,sK6,X4),X6)
                      | ~ r1_tmap_1(X3,sK5,X4,X5) )
                    & ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,X3,sK6,X4),X6)
                      | r1_tmap_1(X3,sK5,X4,X5) )
                    & X5 = X6
                    & m1_subset_1(X6,u1_struct_0(sK6)) )
                & m1_subset_1(X5,u1_struct_0(X3)) )
            & m1_pre_topc(sK6,X3)
            & v1_tsep_1(sK6,X3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK5))))
            & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK5))
            & v1_funct_1(X4) )
        & m1_pre_topc(X3,sK4)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,X4),X6)
                    | ~ r1_tmap_1(sK7,sK5,X4,X5) )
                  & ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,X4),X6)
                    | r1_tmap_1(sK7,sK5,X4,X5) )
                  & X5 = X6
                  & m1_subset_1(X6,u1_struct_0(sK6)) )
              & m1_subset_1(X5,u1_struct_0(sK7)) )
          & m1_pre_topc(sK6,sK7)
          & v1_tsep_1(sK6,sK7)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5))))
          & v1_funct_2(X4,u1_struct_0(sK7),u1_struct_0(sK5))
          & v1_funct_1(X4) )
      & m1_pre_topc(sK7,sK4)
      & ~ v2_struct_0(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f4748,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ( ~ r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,X4),X6)
                  | ~ r1_tmap_1(sK7,sK5,X4,X5) )
                & ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,X4),X6)
                  | r1_tmap_1(sK7,sK5,X4,X5) )
                & X5 = X6
                & m1_subset_1(X6,u1_struct_0(sK6)) )
            & m1_subset_1(X5,u1_struct_0(sK7)) )
        & m1_pre_topc(sK6,sK7)
        & v1_tsep_1(sK6,sK7)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5))))
        & v1_funct_2(X4,u1_struct_0(sK7),u1_struct_0(sK5))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ( ~ r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),X6)
                | ~ r1_tmap_1(sK7,sK5,sK8,X5) )
              & ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),X6)
                | r1_tmap_1(sK7,sK5,sK8,X5) )
              & X5 = X6
              & m1_subset_1(X6,u1_struct_0(sK6)) )
          & m1_subset_1(X5,u1_struct_0(sK7)) )
      & m1_pre_topc(sK6,sK7)
      & v1_tsep_1(sK6,sK7)
      & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5))))
      & v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5))
      & v1_funct_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f4749,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ( ~ r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),X6)
              | ~ r1_tmap_1(sK7,sK5,sK8,X5) )
            & ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),X6)
              | r1_tmap_1(sK7,sK5,sK8,X5) )
            & X5 = X6
            & m1_subset_1(X6,u1_struct_0(sK6)) )
        & m1_subset_1(X5,u1_struct_0(sK7)) )
   => ( ? [X6] :
          ( ( ~ r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),X6)
            | ~ r1_tmap_1(sK7,sK5,sK8,sK9) )
          & ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),X6)
            | r1_tmap_1(sK7,sK5,sK8,sK9) )
          & sK9 = X6
          & m1_subset_1(X6,u1_struct_0(sK6)) )
      & m1_subset_1(sK9,u1_struct_0(sK7)) ) ),
    introduced(choice_axiom,[])).

fof(f4750,plain,
    ( ? [X6] :
        ( ( ~ r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),X6)
          | ~ r1_tmap_1(sK7,sK5,sK8,sK9) )
        & ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),X6)
          | r1_tmap_1(sK7,sK5,sK8,sK9) )
        & sK9 = X6
        & m1_subset_1(X6,u1_struct_0(sK6)) )
   => ( ( ~ r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10)
        | ~ r1_tmap_1(sK7,sK5,sK8,sK9) )
      & ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10)
        | r1_tmap_1(sK7,sK5,sK8,sK9) )
      & sK9 = sK10
      & m1_subset_1(sK10,u1_struct_0(sK6)) ) ),
    introduced(choice_axiom,[])).

fof(f4743,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                | ~ r1_tmap_1(X3,X1,X4,X5) )
                              & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                | r1_tmap_1(X3,X1,X4,X5) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & v1_tsep_1(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f4742])).

fof(f4742,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                | ~ r1_tmap_1(X3,X1,X4,X5) )
                              & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                | r1_tmap_1(X3,X1,X4,X5) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & v1_tsep_1(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3468])).

fof(f3468,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & v1_tsep_1(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3467])).

fof(f3467,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <~> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & v1_tsep_1(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3440])).

fof(f3440,negated_conjecture,(
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
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( ( m1_pre_topc(X2,X3)
                            & v1_tsep_1(X2,X3) )
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X3))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X2))
                                 => ( X5 = X6
                                   => ( r1_tmap_1(X3,X1,X4,X5)
                                    <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3439])).

fof(f3439,conjecture,(
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
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( ( m1_pre_topc(X2,X3)
                          & v1_tsep_1(X2,X3) )
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( X5 = X6
                                 => ( r1_tmap_1(X3,X1,X4,X5)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tmap_1)).

fof(f5562,plain,
    ( ~ r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10)
    | ~ r1_tmap_1(sK7,sK5,sK8,sK9) ),
    inference(cnf_transformation,[],[f4751])).

fof(f8597,plain,
    ( spl495_20
    | spl495_21 ),
    inference(avatar_split_clause,[],[f8290,f8594,f8590])).

fof(f8290,plain,
    ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK9)
    | r1_tmap_1(sK7,sK5,sK8,sK9) ),
    inference(backward_demodulation,[],[f5561,f5560])).

fof(f5561,plain,
    ( r1_tmap_1(sK6,sK5,k3_tmap_1(sK4,sK5,sK7,sK6,sK8),sK10)
    | r1_tmap_1(sK7,sK5,sK8,sK9) ),
    inference(cnf_transformation,[],[f4751])).

fof(f8588,plain,(
    spl495_19 ),
    inference(avatar_split_clause,[],[f5555,f8585])).

fof(f5555,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK7),u1_struct_0(sK5)))) ),
    inference(cnf_transformation,[],[f4751])).

fof(f8578,plain,(
    spl495_17 ),
    inference(avatar_split_clause,[],[f5554,f8575])).

fof(f5554,plain,(
    v1_funct_2(sK8,u1_struct_0(sK7),u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f4751])).

fof(f8573,plain,(
    spl495_16 ),
    inference(avatar_split_clause,[],[f8292,f8570])).

fof(f8292,plain,(
    m1_subset_1(sK9,u1_struct_0(sK6)) ),
    inference(forward_demodulation,[],[f5559,f5560])).

fof(f5559,plain,(
    m1_subset_1(sK10,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f4751])).

fof(f8568,plain,(
    spl495_15 ),
    inference(avatar_split_clause,[],[f5558,f8565])).

fof(f5558,plain,(
    m1_subset_1(sK9,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f4751])).

fof(f8558,plain,(
    spl495_13 ),
    inference(avatar_split_clause,[],[f5557,f8555])).

fof(f5557,plain,(
    m1_pre_topc(sK6,sK7) ),
    inference(cnf_transformation,[],[f4751])).

fof(f8553,plain,(
    spl495_12 ),
    inference(avatar_split_clause,[],[f5556,f8550])).

fof(f5556,plain,(
    v1_tsep_1(sK6,sK7) ),
    inference(cnf_transformation,[],[f4751])).

fof(f8548,plain,(
    spl495_11 ),
    inference(avatar_split_clause,[],[f5552,f8545])).

fof(f5552,plain,(
    m1_pre_topc(sK7,sK4) ),
    inference(cnf_transformation,[],[f4751])).

fof(f8543,plain,(
    spl495_10 ),
    inference(avatar_split_clause,[],[f5550,f8540])).

fof(f5550,plain,(
    m1_pre_topc(sK6,sK4) ),
    inference(cnf_transformation,[],[f4751])).

fof(f8538,plain,(
    spl495_9 ),
    inference(avatar_split_clause,[],[f5553,f8535])).

fof(f5553,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f4751])).

fof(f8533,plain,(
    ~ spl495_8 ),
    inference(avatar_split_clause,[],[f5551,f8530])).

fof(f5551,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f4751])).

fof(f8528,plain,(
    ~ spl495_7 ),
    inference(avatar_split_clause,[],[f5549,f8525])).

fof(f5549,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f4751])).

fof(f8523,plain,(
    spl495_6 ),
    inference(avatar_split_clause,[],[f5548,f8520])).

fof(f5548,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f4751])).

fof(f8518,plain,(
    spl495_5 ),
    inference(avatar_split_clause,[],[f5547,f8515])).

fof(f5547,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f4751])).

fof(f8513,plain,(
    ~ spl495_4 ),
    inference(avatar_split_clause,[],[f5546,f8510])).

fof(f5546,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f4751])).

fof(f8508,plain,(
    spl495_3 ),
    inference(avatar_split_clause,[],[f5545,f8505])).

fof(f5545,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f4751])).

fof(f8503,plain,(
    spl495_2 ),
    inference(avatar_split_clause,[],[f5544,f8500])).

fof(f5544,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f4751])).

fof(f8498,plain,(
    ~ spl495_1 ),
    inference(avatar_split_clause,[],[f5543,f8495])).

fof(f5543,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f4751])).
%------------------------------------------------------------------------------
