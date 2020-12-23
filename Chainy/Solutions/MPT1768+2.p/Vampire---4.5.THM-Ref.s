%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1768+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:32 EST 2020

% Result     : Theorem 7.53s
% Output     : Refutation 7.53s
% Verified   : 
% Statistics : Number of formulae       :  186 ( 823 expanded)
%              Number of leaves         :   44 ( 417 expanded)
%              Depth                    :   11
%              Number of atoms          : 1158 (6174 expanded)
%              Number of equality atoms :   30 ( 120 expanded)
%              Maximal formula depth    :   27 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8807,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f5891,f5896,f5901,f5906,f5911,f5916,f5921,f5926,f5931,f5936,f5941,f5946,f5951,f5956,f5961,f5966,f5971,f5981,f6071,f6167,f6893,f7021,f7178,f7433,f7822,f7832,f7852,f8593,f8760])).

fof(f8760,plain,
    ( spl251_1
    | ~ spl251_2
    | ~ spl251_3
    | spl251_4
    | ~ spl251_5
    | ~ spl251_6
    | spl251_7
    | spl251_8
    | spl251_9
    | ~ spl251_10
    | ~ spl251_11
    | ~ spl251_13
    | ~ spl251_14
    | ~ spl251_15
    | ~ spl251_16
    | ~ spl251_17
    | ~ spl251_26
    | ~ spl251_36
    | ~ spl251_76
    | ~ spl251_92
    | ~ spl251_96
    | spl251_99
    | ~ spl251_101
    | ~ spl251_105
    | ~ spl251_116 ),
    inference(avatar_contradiction_clause,[],[f8759])).

fof(f8759,plain,
    ( $false
    | spl251_1
    | ~ spl251_2
    | ~ spl251_3
    | spl251_4
    | ~ spl251_5
    | ~ spl251_6
    | spl251_7
    | spl251_8
    | spl251_9
    | ~ spl251_10
    | ~ spl251_11
    | ~ spl251_13
    | ~ spl251_14
    | ~ spl251_15
    | ~ spl251_16
    | ~ spl251_17
    | ~ spl251_26
    | ~ spl251_36
    | ~ spl251_76
    | ~ spl251_92
    | ~ spl251_96
    | spl251_99
    | ~ spl251_101
    | ~ spl251_105
    | ~ spl251_116 ),
    inference(subsumption_resolution,[],[f8758,f8715])).

fof(f8715,plain,
    ( ~ r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK3),k7_relat_1(k7_relat_1(sK7,u1_struct_0(sK5)),u1_struct_0(sK6)),k7_relat_1(sK7,u1_struct_0(sK6)))
    | spl251_1
    | ~ spl251_2
    | ~ spl251_3
    | spl251_4
    | ~ spl251_5
    | ~ spl251_6
    | ~ spl251_10
    | ~ spl251_11
    | ~ spl251_13
    | ~ spl251_16
    | ~ spl251_17
    | spl251_99
    | ~ spl251_116 ),
    inference(backward_demodulation,[],[f7821,f8665])).

fof(f8665,plain,
    ( k3_tmap_1(sK2,sK3,sK4,sK6,sK7) = k7_relat_1(sK7,u1_struct_0(sK6))
    | spl251_1
    | ~ spl251_2
    | ~ spl251_3
    | spl251_4
    | ~ spl251_5
    | ~ spl251_6
    | ~ spl251_10
    | ~ spl251_11
    | ~ spl251_13
    | ~ spl251_16
    | ~ spl251_17
    | ~ spl251_116 ),
    inference(forward_demodulation,[],[f8631,f7715])).

fof(f7715,plain,
    ( ! [X0] : k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK7,X0) = k7_relat_1(sK7,X0)
    | ~ spl251_10
    | ~ spl251_17 ),
    inference(unit_resulting_resolution,[],[f5935,f5970,f4858])).

fof(f4858,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f3627])).

fof(f3627,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f3626])).

fof(f3626,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f5970,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ spl251_17 ),
    inference(avatar_component_clause,[],[f5968])).

fof(f5968,plain,
    ( spl251_17
  <=> m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl251_17])])).

fof(f5935,plain,
    ( v1_funct_1(sK7)
    | ~ spl251_10 ),
    inference(avatar_component_clause,[],[f5933])).

fof(f5933,plain,
    ( spl251_10
  <=> v1_funct_1(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl251_10])])).

fof(f8631,plain,
    ( k3_tmap_1(sK2,sK3,sK4,sK6,sK7) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK7,u1_struct_0(sK6))
    | spl251_1
    | ~ spl251_2
    | ~ spl251_3
    | spl251_4
    | ~ spl251_5
    | ~ spl251_6
    | ~ spl251_10
    | ~ spl251_11
    | ~ spl251_13
    | ~ spl251_16
    | ~ spl251_17
    | ~ spl251_116 ),
    inference(unit_resulting_resolution,[],[f5890,f5895,f5900,f5905,f5910,f5915,f5940,f5950,f5935,f5965,f5970,f8592,f4640])).

fof(f4640,plain,(
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
    inference(cnf_transformation,[],[f3469])).

fof(f3469,plain,(
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
    inference(flattening,[],[f3468])).

fof(f3468,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

fof(f8592,plain,
    ( m1_pre_topc(sK6,sK4)
    | ~ spl251_116 ),
    inference(avatar_component_clause,[],[f8590])).

fof(f8590,plain,
    ( spl251_116
  <=> m1_pre_topc(sK6,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl251_116])])).

fof(f5965,plain,
    ( v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ spl251_16 ),
    inference(avatar_component_clause,[],[f5963])).

fof(f5963,plain,
    ( spl251_16
  <=> v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl251_16])])).

fof(f5950,plain,
    ( m1_pre_topc(sK6,sK2)
    | ~ spl251_13 ),
    inference(avatar_component_clause,[],[f5948])).

fof(f5948,plain,
    ( spl251_13
  <=> m1_pre_topc(sK6,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl251_13])])).

fof(f5940,plain,
    ( m1_pre_topc(sK4,sK2)
    | ~ spl251_11 ),
    inference(avatar_component_clause,[],[f5938])).

fof(f5938,plain,
    ( spl251_11
  <=> m1_pre_topc(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl251_11])])).

fof(f5915,plain,
    ( l1_pre_topc(sK3)
    | ~ spl251_6 ),
    inference(avatar_component_clause,[],[f5913])).

fof(f5913,plain,
    ( spl251_6
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl251_6])])).

fof(f5910,plain,
    ( v2_pre_topc(sK3)
    | ~ spl251_5 ),
    inference(avatar_component_clause,[],[f5908])).

fof(f5908,plain,
    ( spl251_5
  <=> v2_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl251_5])])).

fof(f5905,plain,
    ( ~ v2_struct_0(sK3)
    | spl251_4 ),
    inference(avatar_component_clause,[],[f5903])).

fof(f5903,plain,
    ( spl251_4
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl251_4])])).

fof(f5900,plain,
    ( l1_pre_topc(sK2)
    | ~ spl251_3 ),
    inference(avatar_component_clause,[],[f5898])).

fof(f5898,plain,
    ( spl251_3
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl251_3])])).

fof(f5895,plain,
    ( v2_pre_topc(sK2)
    | ~ spl251_2 ),
    inference(avatar_component_clause,[],[f5893])).

fof(f5893,plain,
    ( spl251_2
  <=> v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl251_2])])).

fof(f5890,plain,
    ( ~ v2_struct_0(sK2)
    | spl251_1 ),
    inference(avatar_component_clause,[],[f5888])).

fof(f5888,plain,
    ( spl251_1
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl251_1])])).

fof(f7821,plain,
    ( ~ r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK3),k7_relat_1(k7_relat_1(sK7,u1_struct_0(sK5)),u1_struct_0(sK6)),k3_tmap_1(sK2,sK3,sK4,sK6,sK7))
    | spl251_99 ),
    inference(avatar_component_clause,[],[f7819])).

fof(f7819,plain,
    ( spl251_99
  <=> r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK3),k7_relat_1(k7_relat_1(sK7,u1_struct_0(sK5)),u1_struct_0(sK6)),k3_tmap_1(sK2,sK3,sK4,sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl251_99])])).

fof(f8758,plain,
    ( r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK3),k7_relat_1(k7_relat_1(sK7,u1_struct_0(sK5)),u1_struct_0(sK6)),k7_relat_1(sK7,u1_struct_0(sK6)))
    | spl251_4
    | ~ spl251_5
    | ~ spl251_6
    | spl251_7
    | spl251_8
    | spl251_9
    | ~ spl251_10
    | ~ spl251_14
    | ~ spl251_15
    | ~ spl251_16
    | ~ spl251_17
    | ~ spl251_26
    | ~ spl251_36
    | ~ spl251_76
    | ~ spl251_92
    | ~ spl251_96
    | ~ spl251_101
    | ~ spl251_105
    | ~ spl251_116 ),
    inference(forward_demodulation,[],[f8757,f8746])).

fof(f8746,plain,
    ( k7_relat_1(k7_relat_1(sK7,u1_struct_0(sK5)),u1_struct_0(sK6)) = k3_tmap_1(sK4,sK3,sK5,sK6,k7_relat_1(sK7,u1_struct_0(sK5)))
    | spl251_4
    | ~ spl251_5
    | ~ spl251_6
    | spl251_7
    | ~ spl251_10
    | ~ spl251_14
    | ~ spl251_15
    | ~ spl251_17
    | ~ spl251_26
    | ~ spl251_36
    | ~ spl251_76
    | ~ spl251_92
    | ~ spl251_96
    | ~ spl251_101
    | ~ spl251_105
    | ~ spl251_116 ),
    inference(forward_demodulation,[],[f8628,f7792])).

fof(f7792,plain,
    ( ! [X0] : k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3),k7_relat_1(sK7,u1_struct_0(sK5)),X0) = k7_relat_1(k7_relat_1(sK7,u1_struct_0(sK5)),X0)
    | ~ spl251_10
    | ~ spl251_17
    | ~ spl251_76
    | ~ spl251_92
    | ~ spl251_96 ),
    inference(forward_demodulation,[],[f7713,f7717])).

fof(f7717,plain,
    ( k3_tmap_1(sK2,sK3,sK4,sK5,sK7) = k7_relat_1(sK7,u1_struct_0(sK5))
    | ~ spl251_10
    | ~ spl251_17
    | ~ spl251_96 ),
    inference(backward_demodulation,[],[f7432,f7715])).

fof(f7432,plain,
    ( k3_tmap_1(sK2,sK3,sK4,sK5,sK7) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK7,u1_struct_0(sK5))
    | ~ spl251_96 ),
    inference(avatar_component_clause,[],[f7430])).

fof(f7430,plain,
    ( spl251_96
  <=> k3_tmap_1(sK2,sK3,sK4,sK5,sK7) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK7,u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl251_96])])).

fof(f7713,plain,
    ( ! [X0] : k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,sK5,sK7),X0) = k7_relat_1(k3_tmap_1(sK2,sK3,sK4,sK5,sK7),X0)
    | ~ spl251_76
    | ~ spl251_92 ),
    inference(unit_resulting_resolution,[],[f6892,f7177,f4858])).

fof(f7177,plain,
    ( m1_subset_1(k3_tmap_1(sK2,sK3,sK4,sK5,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ spl251_92 ),
    inference(avatar_component_clause,[],[f7175])).

fof(f7175,plain,
    ( spl251_92
  <=> m1_subset_1(k3_tmap_1(sK2,sK3,sK4,sK5,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl251_92])])).

fof(f6892,plain,
    ( v1_funct_1(k3_tmap_1(sK2,sK3,sK4,sK5,sK7))
    | ~ spl251_76 ),
    inference(avatar_component_clause,[],[f6890])).

fof(f6890,plain,
    ( spl251_76
  <=> v1_funct_1(k3_tmap_1(sK2,sK3,sK4,sK5,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl251_76])])).

fof(f8628,plain,
    ( k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3),k7_relat_1(sK7,u1_struct_0(sK5)),u1_struct_0(sK6)) = k3_tmap_1(sK4,sK3,sK5,sK6,k7_relat_1(sK7,u1_struct_0(sK5)))
    | spl251_4
    | ~ spl251_5
    | ~ spl251_6
    | spl251_7
    | ~ spl251_10
    | ~ spl251_14
    | ~ spl251_15
    | ~ spl251_17
    | ~ spl251_26
    | ~ spl251_36
    | ~ spl251_101
    | ~ spl251_105
    | ~ spl251_116 ),
    inference(unit_resulting_resolution,[],[f5920,f6166,f6070,f5905,f5910,f5915,f5955,f5960,f7718,f7831,f7851,f8592,f4640])).

fof(f7851,plain,
    ( m1_subset_1(k7_relat_1(sK7,u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ spl251_105 ),
    inference(avatar_component_clause,[],[f7849])).

fof(f7849,plain,
    ( spl251_105
  <=> m1_subset_1(k7_relat_1(sK7,u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl251_105])])).

fof(f7831,plain,
    ( v1_funct_2(k7_relat_1(sK7,u1_struct_0(sK5)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ spl251_101 ),
    inference(avatar_component_clause,[],[f7829])).

fof(f7829,plain,
    ( spl251_101
  <=> v1_funct_2(k7_relat_1(sK7,u1_struct_0(sK5)),u1_struct_0(sK5),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl251_101])])).

fof(f7718,plain,
    ( ! [X0] : v1_funct_1(k7_relat_1(sK7,X0))
    | ~ spl251_10
    | ~ spl251_17 ),
    inference(backward_demodulation,[],[f7519,f7715])).

fof(f7519,plain,
    ( ! [X0] : v1_funct_1(k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK7,X0))
    | ~ spl251_10
    | ~ spl251_17 ),
    inference(unit_resulting_resolution,[],[f5935,f5970,f4856])).

fof(f4856,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f3625])).

fof(f3625,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f3624])).

fof(f3624,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1500])).

fof(f1500,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f5960,plain,
    ( m1_pre_topc(sK6,sK5)
    | ~ spl251_15 ),
    inference(avatar_component_clause,[],[f5958])).

fof(f5958,plain,
    ( spl251_15
  <=> m1_pre_topc(sK6,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl251_15])])).

fof(f5955,plain,
    ( m1_pre_topc(sK5,sK4)
    | ~ spl251_14 ),
    inference(avatar_component_clause,[],[f5953])).

fof(f5953,plain,
    ( spl251_14
  <=> m1_pre_topc(sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl251_14])])).

fof(f6070,plain,
    ( l1_pre_topc(sK4)
    | ~ spl251_26 ),
    inference(avatar_component_clause,[],[f6068])).

fof(f6068,plain,
    ( spl251_26
  <=> l1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl251_26])])).

fof(f6166,plain,
    ( v2_pre_topc(sK4)
    | ~ spl251_36 ),
    inference(avatar_component_clause,[],[f6164])).

fof(f6164,plain,
    ( spl251_36
  <=> v2_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl251_36])])).

fof(f5920,plain,
    ( ~ v2_struct_0(sK4)
    | spl251_7 ),
    inference(avatar_component_clause,[],[f5918])).

fof(f5918,plain,
    ( spl251_7
  <=> v2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl251_7])])).

fof(f8757,plain,
    ( r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK3),k3_tmap_1(sK4,sK3,sK5,sK6,k7_relat_1(sK7,u1_struct_0(sK5))),k7_relat_1(sK7,u1_struct_0(sK6)))
    | spl251_4
    | ~ spl251_5
    | ~ spl251_6
    | spl251_7
    | spl251_8
    | spl251_9
    | ~ spl251_10
    | ~ spl251_14
    | ~ spl251_15
    | ~ spl251_16
    | ~ spl251_17
    | ~ spl251_26
    | ~ spl251_36
    | ~ spl251_116 ),
    inference(forward_demodulation,[],[f8756,f8498])).

fof(f8498,plain,
    ( k2_tmap_1(sK4,sK3,sK7,sK5) = k7_relat_1(sK7,u1_struct_0(sK5))
    | spl251_4
    | ~ spl251_5
    | ~ spl251_6
    | spl251_7
    | ~ spl251_10
    | ~ spl251_14
    | ~ spl251_16
    | ~ spl251_17
    | ~ spl251_26
    | ~ spl251_36 ),
    inference(forward_demodulation,[],[f8489,f7715])).

fof(f8489,plain,
    ( k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK7,u1_struct_0(sK5)) = k2_tmap_1(sK4,sK3,sK7,sK5)
    | spl251_4
    | ~ spl251_5
    | ~ spl251_6
    | spl251_7
    | ~ spl251_10
    | ~ spl251_14
    | ~ spl251_16
    | ~ spl251_17
    | ~ spl251_26
    | ~ spl251_36 ),
    inference(unit_resulting_resolution,[],[f5920,f6166,f6070,f5905,f5910,f5915,f5935,f5955,f5965,f5970,f4869])).

fof(f4869,plain,(
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
    inference(cnf_transformation,[],[f3635])).

fof(f3635,plain,(
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
    inference(flattening,[],[f3634])).

fof(f3634,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f8756,plain,
    ( r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK3),k3_tmap_1(sK4,sK3,sK5,sK6,k2_tmap_1(sK4,sK3,sK7,sK5)),k7_relat_1(sK7,u1_struct_0(sK6)))
    | spl251_4
    | ~ spl251_5
    | ~ spl251_6
    | spl251_7
    | spl251_8
    | spl251_9
    | ~ spl251_10
    | ~ spl251_14
    | ~ spl251_15
    | ~ spl251_16
    | ~ spl251_17
    | ~ spl251_26
    | ~ spl251_36
    | ~ spl251_116 ),
    inference(forward_demodulation,[],[f8623,f8661])).

fof(f8661,plain,
    ( k2_tmap_1(sK4,sK3,sK7,sK6) = k7_relat_1(sK7,u1_struct_0(sK6))
    | spl251_4
    | ~ spl251_5
    | ~ spl251_6
    | spl251_7
    | ~ spl251_10
    | ~ spl251_16
    | ~ spl251_17
    | ~ spl251_26
    | ~ spl251_36
    | ~ spl251_116 ),
    inference(forward_demodulation,[],[f8660,f7715])).

fof(f8660,plain,
    ( k2_tmap_1(sK4,sK3,sK7,sK6) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK7,u1_struct_0(sK6))
    | spl251_4
    | ~ spl251_5
    | ~ spl251_6
    | spl251_7
    | ~ spl251_10
    | ~ spl251_16
    | ~ spl251_17
    | ~ spl251_26
    | ~ spl251_36
    | ~ spl251_116 ),
    inference(unit_resulting_resolution,[],[f5920,f6166,f6070,f5905,f5910,f5915,f5935,f5965,f5970,f8592,f4869])).

fof(f8623,plain,
    ( r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK3),k3_tmap_1(sK4,sK3,sK5,sK6,k2_tmap_1(sK4,sK3,sK7,sK5)),k2_tmap_1(sK4,sK3,sK7,sK6))
    | spl251_4
    | ~ spl251_5
    | ~ spl251_6
    | spl251_7
    | spl251_8
    | spl251_9
    | ~ spl251_10
    | ~ spl251_14
    | ~ spl251_15
    | ~ spl251_16
    | ~ spl251_17
    | ~ spl251_26
    | ~ spl251_36
    | ~ spl251_116 ),
    inference(unit_resulting_resolution,[],[f5920,f6166,f6070,f5905,f5910,f5915,f5930,f5925,f5960,f5955,f5935,f5965,f5970,f8592,f4639])).

fof(f4639,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))
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
    inference(cnf_transformation,[],[f3467])).

fof(f3467,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
    inference(flattening,[],[f3466])).

fof(f3466,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2))
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
    inference(ennf_transformation,[],[f3429])).

fof(f3429,axiom,(
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
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X2,X3)
                       => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X2,k2_tmap_1(X0,X1,X4,X3)),k2_tmap_1(X0,X1,X4,X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_tmap_1)).

fof(f5925,plain,
    ( ~ v2_struct_0(sK5)
    | spl251_8 ),
    inference(avatar_component_clause,[],[f5923])).

fof(f5923,plain,
    ( spl251_8
  <=> v2_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl251_8])])).

fof(f5930,plain,
    ( ~ v2_struct_0(sK6)
    | spl251_9 ),
    inference(avatar_component_clause,[],[f5928])).

fof(f5928,plain,
    ( spl251_9
  <=> v2_struct_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl251_9])])).

fof(f8593,plain,
    ( spl251_116
    | ~ spl251_14
    | ~ spl251_15
    | ~ spl251_26
    | ~ spl251_36 ),
    inference(avatar_split_clause,[],[f6168,f6164,f6068,f5958,f5953,f8590])).

fof(f6168,plain,
    ( m1_pre_topc(sK6,sK4)
    | ~ spl251_14
    | ~ spl251_15
    | ~ spl251_26
    | ~ spl251_36 ),
    inference(unit_resulting_resolution,[],[f6070,f5960,f5955,f6166,f4660])).

fof(f4660,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | m1_pre_topc(X2,X0) ) ),
    inference(cnf_transformation,[],[f3481])).

fof(f3481,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f3480])).

fof(f3480,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3433])).

fof(f3433,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f7852,plain,
    ( spl251_105
    | ~ spl251_10
    | ~ spl251_17
    | ~ spl251_92
    | ~ spl251_96 ),
    inference(avatar_split_clause,[],[f7726,f7430,f7175,f5968,f5933,f7849])).

fof(f7726,plain,
    ( m1_subset_1(k7_relat_1(sK7,u1_struct_0(sK5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ spl251_10
    | ~ spl251_17
    | ~ spl251_92
    | ~ spl251_96 ),
    inference(backward_demodulation,[],[f7177,f7717])).

fof(f7832,plain,
    ( spl251_101
    | ~ spl251_10
    | ~ spl251_17
    | ~ spl251_84
    | ~ spl251_96 ),
    inference(avatar_split_clause,[],[f7725,f7430,f7018,f5968,f5933,f7829])).

fof(f7018,plain,
    ( spl251_84
  <=> v1_funct_2(k3_tmap_1(sK2,sK3,sK4,sK5,sK7),u1_struct_0(sK5),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl251_84])])).

fof(f7725,plain,
    ( v1_funct_2(k7_relat_1(sK7,u1_struct_0(sK5)),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ spl251_10
    | ~ spl251_17
    | ~ spl251_84
    | ~ spl251_96 ),
    inference(backward_demodulation,[],[f7020,f7717])).

fof(f7020,plain,
    ( v1_funct_2(k3_tmap_1(sK2,sK3,sK4,sK5,sK7),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ spl251_84 ),
    inference(avatar_component_clause,[],[f7018])).

fof(f7822,plain,
    ( ~ spl251_99
    | spl251_1
    | ~ spl251_2
    | ~ spl251_3
    | spl251_4
    | ~ spl251_5
    | ~ spl251_6
    | ~ spl251_10
    | ~ spl251_12
    | ~ spl251_13
    | ~ spl251_15
    | ~ spl251_17
    | spl251_19
    | ~ spl251_76
    | ~ spl251_84
    | ~ spl251_92
    | ~ spl251_96 ),
    inference(avatar_split_clause,[],[f7797,f7430,f7175,f7018,f6890,f5978,f5968,f5958,f5948,f5943,f5933,f5913,f5908,f5903,f5898,f5893,f5888,f7819])).

fof(f5943,plain,
    ( spl251_12
  <=> m1_pre_topc(sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl251_12])])).

fof(f5978,plain,
    ( spl251_19
  <=> r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK5,sK6,k3_tmap_1(sK2,sK3,sK4,sK5,sK7)),k3_tmap_1(sK2,sK3,sK4,sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl251_19])])).

fof(f7797,plain,
    ( ~ r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK3),k7_relat_1(k7_relat_1(sK7,u1_struct_0(sK5)),u1_struct_0(sK6)),k3_tmap_1(sK2,sK3,sK4,sK6,sK7))
    | spl251_1
    | ~ spl251_2
    | ~ spl251_3
    | spl251_4
    | ~ spl251_5
    | ~ spl251_6
    | ~ spl251_10
    | ~ spl251_12
    | ~ spl251_13
    | ~ spl251_15
    | ~ spl251_17
    | spl251_19
    | ~ spl251_76
    | ~ spl251_84
    | ~ spl251_92
    | ~ spl251_96 ),
    inference(backward_demodulation,[],[f7722,f7793])).

fof(f7793,plain,
    ( k3_tmap_1(sK2,sK3,sK5,sK6,k7_relat_1(sK7,u1_struct_0(sK5))) = k7_relat_1(k7_relat_1(sK7,u1_struct_0(sK5)),u1_struct_0(sK6))
    | spl251_1
    | ~ spl251_2
    | ~ spl251_3
    | spl251_4
    | ~ spl251_5
    | ~ spl251_6
    | ~ spl251_10
    | ~ spl251_12
    | ~ spl251_13
    | ~ spl251_15
    | ~ spl251_17
    | ~ spl251_76
    | ~ spl251_84
    | ~ spl251_92
    | ~ spl251_96 ),
    inference(backward_demodulation,[],[f7748,f7792])).

fof(f7748,plain,
    ( k3_tmap_1(sK2,sK3,sK5,sK6,k7_relat_1(sK7,u1_struct_0(sK5))) = k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3),k7_relat_1(sK7,u1_struct_0(sK5)),u1_struct_0(sK6))
    | spl251_1
    | ~ spl251_2
    | ~ spl251_3
    | spl251_4
    | ~ spl251_5
    | ~ spl251_6
    | ~ spl251_10
    | ~ spl251_12
    | ~ spl251_13
    | ~ spl251_15
    | ~ spl251_17
    | ~ spl251_76
    | ~ spl251_84
    | ~ spl251_92
    | ~ spl251_96 ),
    inference(backward_demodulation,[],[f7223,f7717])).

fof(f7223,plain,
    ( k3_tmap_1(sK2,sK3,sK5,sK6,k3_tmap_1(sK2,sK3,sK4,sK5,sK7)) = k2_partfun1(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,sK5,sK7),u1_struct_0(sK6))
    | spl251_1
    | ~ spl251_2
    | ~ spl251_3
    | spl251_4
    | ~ spl251_5
    | ~ spl251_6
    | ~ spl251_12
    | ~ spl251_13
    | ~ spl251_15
    | ~ spl251_76
    | ~ spl251_84
    | ~ spl251_92 ),
    inference(unit_resulting_resolution,[],[f5890,f5895,f5900,f5905,f5910,f5915,f5945,f5950,f5960,f6892,f7020,f7177,f4640])).

fof(f5945,plain,
    ( m1_pre_topc(sK5,sK2)
    | ~ spl251_12 ),
    inference(avatar_component_clause,[],[f5943])).

fof(f7722,plain,
    ( ~ r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK5,sK6,k7_relat_1(sK7,u1_struct_0(sK5))),k3_tmap_1(sK2,sK3,sK4,sK6,sK7))
    | ~ spl251_10
    | ~ spl251_17
    | spl251_19
    | ~ spl251_96 ),
    inference(backward_demodulation,[],[f5980,f7717])).

fof(f5980,plain,
    ( ~ r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK5,sK6,k3_tmap_1(sK2,sK3,sK4,sK5,sK7)),k3_tmap_1(sK2,sK3,sK4,sK6,sK7))
    | spl251_19 ),
    inference(avatar_component_clause,[],[f5978])).

fof(f7433,plain,
    ( spl251_96
    | spl251_1
    | ~ spl251_2
    | ~ spl251_3
    | spl251_4
    | ~ spl251_5
    | ~ spl251_6
    | ~ spl251_10
    | ~ spl251_11
    | ~ spl251_12
    | ~ spl251_14
    | ~ spl251_16
    | ~ spl251_17 ),
    inference(avatar_split_clause,[],[f6100,f5968,f5963,f5953,f5943,f5938,f5933,f5913,f5908,f5903,f5898,f5893,f5888,f7430])).

fof(f6100,plain,
    ( k3_tmap_1(sK2,sK3,sK4,sK5,sK7) = k2_partfun1(u1_struct_0(sK4),u1_struct_0(sK3),sK7,u1_struct_0(sK5))
    | spl251_1
    | ~ spl251_2
    | ~ spl251_3
    | spl251_4
    | ~ spl251_5
    | ~ spl251_6
    | ~ spl251_10
    | ~ spl251_11
    | ~ spl251_12
    | ~ spl251_14
    | ~ spl251_16
    | ~ spl251_17 ),
    inference(unit_resulting_resolution,[],[f5890,f5895,f5900,f5905,f5910,f5915,f5940,f5945,f5935,f5955,f5965,f5970,f4640])).

fof(f7178,plain,
    ( spl251_92
    | spl251_1
    | ~ spl251_2
    | ~ spl251_3
    | spl251_4
    | ~ spl251_5
    | ~ spl251_6
    | ~ spl251_10
    | ~ spl251_11
    | ~ spl251_12
    | ~ spl251_16
    | ~ spl251_17 ),
    inference(avatar_split_clause,[],[f6098,f5968,f5963,f5943,f5938,f5933,f5913,f5908,f5903,f5898,f5893,f5888,f7175])).

fof(f6098,plain,
    ( m1_subset_1(k3_tmap_1(sK2,sK3,sK4,sK5,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | spl251_1
    | ~ spl251_2
    | ~ spl251_3
    | spl251_4
    | ~ spl251_5
    | ~ spl251_6
    | ~ spl251_10
    | ~ spl251_11
    | ~ spl251_12
    | ~ spl251_16
    | ~ spl251_17 ),
    inference(unit_resulting_resolution,[],[f5890,f5895,f5900,f5905,f5910,f5915,f5945,f5940,f5935,f5965,f5970,f4630])).

fof(f4630,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3453])).

fof(f3453,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3452])).

fof(f3452,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3337])).

fof(f3337,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(X4)
        & m1_pre_topc(X3,X0)
        & m1_pre_topc(X2,X0)
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_tmap_1)).

fof(f7021,plain,
    ( spl251_84
    | spl251_1
    | ~ spl251_2
    | ~ spl251_3
    | spl251_4
    | ~ spl251_5
    | ~ spl251_6
    | ~ spl251_10
    | ~ spl251_11
    | ~ spl251_12
    | ~ spl251_16
    | ~ spl251_17 ),
    inference(avatar_split_clause,[],[f6088,f5968,f5963,f5943,f5938,f5933,f5913,f5908,f5903,f5898,f5893,f5888,f7018])).

fof(f6088,plain,
    ( v1_funct_2(k3_tmap_1(sK2,sK3,sK4,sK5,sK7),u1_struct_0(sK5),u1_struct_0(sK3))
    | spl251_1
    | ~ spl251_2
    | ~ spl251_3
    | spl251_4
    | ~ spl251_5
    | ~ spl251_6
    | ~ spl251_10
    | ~ spl251_11
    | ~ spl251_12
    | ~ spl251_16
    | ~ spl251_17 ),
    inference(unit_resulting_resolution,[],[f5890,f5895,f5900,f5905,f5910,f5915,f5945,f5940,f5935,f5965,f5970,f4629])).

fof(f4629,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3453])).

fof(f6893,plain,
    ( spl251_76
    | spl251_1
    | ~ spl251_2
    | ~ spl251_3
    | spl251_4
    | ~ spl251_5
    | ~ spl251_6
    | ~ spl251_10
    | ~ spl251_11
    | ~ spl251_12
    | ~ spl251_16
    | ~ spl251_17 ),
    inference(avatar_split_clause,[],[f6082,f5968,f5963,f5943,f5938,f5933,f5913,f5908,f5903,f5898,f5893,f5888,f6890])).

fof(f6082,plain,
    ( v1_funct_1(k3_tmap_1(sK2,sK3,sK4,sK5,sK7))
    | spl251_1
    | ~ spl251_2
    | ~ spl251_3
    | spl251_4
    | ~ spl251_5
    | ~ spl251_6
    | ~ spl251_10
    | ~ spl251_11
    | ~ spl251_12
    | ~ spl251_16
    | ~ spl251_17 ),
    inference(unit_resulting_resolution,[],[f5890,f5895,f5900,f5905,f5910,f5915,f5945,f5940,f5935,f5965,f5970,f4628])).

fof(f4628,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3453])).

fof(f6167,plain,
    ( spl251_36
    | ~ spl251_2
    | ~ spl251_3
    | ~ spl251_11 ),
    inference(avatar_split_clause,[],[f6013,f5938,f5898,f5893,f6164])).

fof(f6013,plain,
    ( v2_pre_topc(sK4)
    | ~ spl251_2
    | ~ spl251_3
    | ~ spl251_11 ),
    inference(unit_resulting_resolution,[],[f5900,f5940,f5895,f4661])).

fof(f4661,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f3483])).

fof(f3483,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f3482])).

fof(f3482,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f6071,plain,
    ( spl251_26
    | ~ spl251_3
    | ~ spl251_11 ),
    inference(avatar_split_clause,[],[f6008,f5938,f5898,f6068])).

fof(f6008,plain,
    ( l1_pre_topc(sK4)
    | ~ spl251_3
    | ~ spl251_11 ),
    inference(unit_resulting_resolution,[],[f5940,f5900,f4670])).

fof(f4670,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f3493])).

fof(f3493,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f5981,plain,(
    ~ spl251_19 ),
    inference(avatar_split_clause,[],[f4620,f5978])).

fof(f4620,plain,(
    ~ r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK5,sK6,k3_tmap_1(sK2,sK3,sK4,sK5,sK7)),k3_tmap_1(sK2,sK3,sK4,sK6,sK7)) ),
    inference(cnf_transformation,[],[f4143])).

fof(f4143,plain,
    ( ~ r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK5,sK6,k3_tmap_1(sK2,sK3,sK4,sK5,sK7)),k3_tmap_1(sK2,sK3,sK4,sK6,sK7))
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    & v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK3))
    & v1_funct_1(sK7)
    & m1_pre_topc(sK6,sK5)
    & m1_pre_topc(sK5,sK4)
    & m1_pre_topc(sK6,sK2)
    & ~ v2_struct_0(sK6)
    & m1_pre_topc(sK5,sK2)
    & ~ v2_struct_0(sK5)
    & m1_pre_topc(sK4,sK2)
    & ~ v2_struct_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f3443,f4142,f4141,f4140,f4139,f4138,f4137])).

fof(f4137,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5))
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                        & m1_pre_topc(X4,X3)
                        & m1_pre_topc(X3,X2)
                        & m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
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
                          ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(sK2,X1,X3,X4,k3_tmap_1(sK2,X1,X2,X3,X5)),k3_tmap_1(sK2,X1,X2,X4,X5))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_pre_topc(X4,X3)
                      & m1_pre_topc(X3,X2)
                      & m1_pre_topc(X4,sK2)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,sK2)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f4138,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(sK2,X1,X3,X4,k3_tmap_1(sK2,X1,X2,X3,X5)),k3_tmap_1(sK2,X1,X2,X4,X5))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X5) )
                    & m1_pre_topc(X4,X3)
                    & m1_pre_topc(X3,X2)
                    & m1_pre_topc(X4,sK2)
                    & ~ v2_struct_0(X4) )
                & m1_pre_topc(X3,sK2)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK2)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,X3,X4,k3_tmap_1(sK2,sK3,X2,X3,X5)),k3_tmap_1(sK2,sK3,X2,X4,X5))
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3))))
                      & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK3))
                      & v1_funct_1(X5) )
                  & m1_pre_topc(X4,X3)
                  & m1_pre_topc(X3,X2)
                  & m1_pre_topc(X4,sK2)
                  & ~ v2_struct_0(X4) )
              & m1_pre_topc(X3,sK2)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK2)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f4139,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,X3,X4,k3_tmap_1(sK2,sK3,X2,X3,X5)),k3_tmap_1(sK2,sK3,X2,X4,X5))
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3))))
                    & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(sK3))
                    & v1_funct_1(X5) )
                & m1_pre_topc(X4,X3)
                & m1_pre_topc(X3,X2)
                & m1_pre_topc(X4,sK2)
                & ~ v2_struct_0(X4) )
            & m1_pre_topc(X3,sK2)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK2)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,X3,X4,k3_tmap_1(sK2,sK3,sK4,X3,X5)),k3_tmap_1(sK2,sK3,sK4,X4,X5))
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
                  & v1_funct_2(X5,u1_struct_0(sK4),u1_struct_0(sK3))
                  & v1_funct_1(X5) )
              & m1_pre_topc(X4,X3)
              & m1_pre_topc(X3,sK4)
              & m1_pre_topc(X4,sK2)
              & ~ v2_struct_0(X4) )
          & m1_pre_topc(X3,sK2)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK4,sK2)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f4140,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,X3,X4,k3_tmap_1(sK2,sK3,sK4,X3,X5)),k3_tmap_1(sK2,sK3,sK4,X4,X5))
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
                & v1_funct_2(X5,u1_struct_0(sK4),u1_struct_0(sK3))
                & v1_funct_1(X5) )
            & m1_pre_topc(X4,X3)
            & m1_pre_topc(X3,sK4)
            & m1_pre_topc(X4,sK2)
            & ~ v2_struct_0(X4) )
        & m1_pre_topc(X3,sK2)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK5,X4,k3_tmap_1(sK2,sK3,sK4,sK5,X5)),k3_tmap_1(sK2,sK3,sK4,X4,X5))
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
              & v1_funct_2(X5,u1_struct_0(sK4),u1_struct_0(sK3))
              & v1_funct_1(X5) )
          & m1_pre_topc(X4,sK5)
          & m1_pre_topc(sK5,sK4)
          & m1_pre_topc(X4,sK2)
          & ~ v2_struct_0(X4) )
      & m1_pre_topc(sK5,sK2)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f4141,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK5,X4,k3_tmap_1(sK2,sK3,sK4,sK5,X5)),k3_tmap_1(sK2,sK3,sK4,X4,X5))
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
            & v1_funct_2(X5,u1_struct_0(sK4),u1_struct_0(sK3))
            & v1_funct_1(X5) )
        & m1_pre_topc(X4,sK5)
        & m1_pre_topc(sK5,sK4)
        & m1_pre_topc(X4,sK2)
        & ~ v2_struct_0(X4) )
   => ( ? [X5] :
          ( ~ r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK5,sK6,k3_tmap_1(sK2,sK3,sK4,sK5,X5)),k3_tmap_1(sK2,sK3,sK4,sK6,X5))
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
          & v1_funct_2(X5,u1_struct_0(sK4),u1_struct_0(sK3))
          & v1_funct_1(X5) )
      & m1_pre_topc(sK6,sK5)
      & m1_pre_topc(sK5,sK4)
      & m1_pre_topc(sK6,sK2)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f4142,plain,
    ( ? [X5] :
        ( ~ r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK5,sK6,k3_tmap_1(sK2,sK3,sK4,sK5,X5)),k3_tmap_1(sK2,sK3,sK4,sK6,X5))
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
        & v1_funct_2(X5,u1_struct_0(sK4),u1_struct_0(sK3))
        & v1_funct_1(X5) )
   => ( ~ r2_funct_2(u1_struct_0(sK6),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK5,sK6,k3_tmap_1(sK2,sK3,sK4,sK5,sK7)),k3_tmap_1(sK2,sK3,sK4,sK6,sK7))
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
      & v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK3))
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f3443,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_pre_topc(X4,X3)
                      & m1_pre_topc(X3,X2)
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
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
    inference(flattening,[],[f3442])).

fof(f3442,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_pre_topc(X4,X3)
                      & m1_pre_topc(X3,X2)
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
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
    inference(ennf_transformation,[],[f3431])).

fof(f3431,negated_conjecture,(
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
                        ( ( m1_pre_topc(X4,X0)
                          & ~ v2_struct_0(X4) )
                       => ( ( m1_pre_topc(X4,X3)
                            & m1_pre_topc(X3,X2) )
                         => ! [X5] :
                              ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                                & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                                & v1_funct_1(X5) )
                             => r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3430])).

fof(f3430,conjecture,(
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
                      ( ( m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( ( m1_pre_topc(X4,X3)
                          & m1_pre_topc(X3,X2) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                              & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => r2_funct_2(u1_struct_0(X4),u1_struct_0(X1),k3_tmap_1(X0,X1,X3,X4,k3_tmap_1(X0,X1,X2,X3,X5)),k3_tmap_1(X0,X1,X2,X4,X5)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_tmap_1)).

fof(f5971,plain,(
    spl251_17 ),
    inference(avatar_split_clause,[],[f4619,f5968])).

fof(f4619,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f4143])).

fof(f5966,plain,(
    spl251_16 ),
    inference(avatar_split_clause,[],[f4618,f5963])).

fof(f4618,plain,(
    v1_funct_2(sK7,u1_struct_0(sK4),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f4143])).

fof(f5961,plain,(
    spl251_15 ),
    inference(avatar_split_clause,[],[f4616,f5958])).

fof(f4616,plain,(
    m1_pre_topc(sK6,sK5) ),
    inference(cnf_transformation,[],[f4143])).

fof(f5956,plain,(
    spl251_14 ),
    inference(avatar_split_clause,[],[f4615,f5953])).

fof(f4615,plain,(
    m1_pre_topc(sK5,sK4) ),
    inference(cnf_transformation,[],[f4143])).

fof(f5951,plain,(
    spl251_13 ),
    inference(avatar_split_clause,[],[f4614,f5948])).

fof(f4614,plain,(
    m1_pre_topc(sK6,sK2) ),
    inference(cnf_transformation,[],[f4143])).

fof(f5946,plain,(
    spl251_12 ),
    inference(avatar_split_clause,[],[f4612,f5943])).

fof(f4612,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f4143])).

fof(f5941,plain,(
    spl251_11 ),
    inference(avatar_split_clause,[],[f4610,f5938])).

fof(f4610,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f4143])).

fof(f5936,plain,(
    spl251_10 ),
    inference(avatar_split_clause,[],[f4617,f5933])).

fof(f4617,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f4143])).

fof(f5931,plain,(
    ~ spl251_9 ),
    inference(avatar_split_clause,[],[f4613,f5928])).

fof(f4613,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f4143])).

fof(f5926,plain,(
    ~ spl251_8 ),
    inference(avatar_split_clause,[],[f4611,f5923])).

fof(f4611,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f4143])).

fof(f5921,plain,(
    ~ spl251_7 ),
    inference(avatar_split_clause,[],[f4609,f5918])).

fof(f4609,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f4143])).

fof(f5916,plain,(
    spl251_6 ),
    inference(avatar_split_clause,[],[f4608,f5913])).

fof(f4608,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f4143])).

fof(f5911,plain,(
    spl251_5 ),
    inference(avatar_split_clause,[],[f4607,f5908])).

fof(f4607,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f4143])).

fof(f5906,plain,(
    ~ spl251_4 ),
    inference(avatar_split_clause,[],[f4606,f5903])).

fof(f4606,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f4143])).

fof(f5901,plain,(
    spl251_3 ),
    inference(avatar_split_clause,[],[f4605,f5898])).

fof(f4605,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f4143])).

fof(f5896,plain,(
    spl251_2 ),
    inference(avatar_split_clause,[],[f4604,f5893])).

fof(f4604,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f4143])).

fof(f5891,plain,(
    ~ spl251_1 ),
    inference(avatar_split_clause,[],[f4603,f5888])).

fof(f4603,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f4143])).
%------------------------------------------------------------------------------
