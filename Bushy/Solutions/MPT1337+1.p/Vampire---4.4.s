%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_2__t60_tops_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:42 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 282 expanded)
%              Number of leaves         :   28 (  99 expanded)
%              Depth                    :   16
%              Number of atoms          :  569 (1264 expanded)
%              Number of equality atoms :   30 (  91 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f717,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f106,f110,f114,f118,f122,f126,f130,f134,f138,f142,f158,f169,f178,f199,f310,f422,f439,f700,f704,f715])).

fof(f715,plain,
    ( ~ spl12_0
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_16
    | ~ spl12_18
    | spl12_23
    | ~ spl12_24
    | ~ spl12_88
    | ~ spl12_120
    | ~ spl12_122 ),
    inference(avatar_contradiction_clause,[],[f714])).

fof(f714,plain,
    ( $false
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_8
    | ~ spl12_10
    | ~ spl12_16
    | ~ spl12_18
    | ~ spl12_23
    | ~ spl12_24
    | ~ spl12_88
    | ~ spl12_120
    | ~ spl12_122 ),
    inference(subsumption_resolution,[],[f713,f712])).

fof(f712,plain,
    ( ~ v4_pre_topc(sK7(k3_funct_3(sK2),sK3,sK8(sK0,sK4)),sK1)
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_10
    | ~ spl12_18
    | ~ spl12_23
    | ~ spl12_24
    | ~ spl12_120
    | ~ spl12_122 ),
    inference(subsumption_resolution,[],[f711,f168])).

fof(f168,plain,
    ( ~ v4_pre_topc(sK8(sK0,sK4),sK0)
    | ~ spl12_23 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl12_23
  <=> ~ v4_pre_topc(sK8(sK0,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_23])])).

fof(f711,plain,
    ( v4_pre_topc(sK8(sK0,sK4),sK0)
    | ~ v4_pre_topc(sK7(k3_funct_3(sK2),sK3,sK8(sK0,sK4)),sK1)
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_10
    | ~ spl12_18
    | ~ spl12_24
    | ~ spl12_120
    | ~ spl12_122 ),
    inference(forward_demodulation,[],[f710,f703])).

fof(f703,plain,
    ( k10_relat_1(sK2,sK7(k3_funct_3(sK2),sK3,sK8(sK0,sK4))) = sK8(sK0,sK4)
    | ~ spl12_122 ),
    inference(avatar_component_clause,[],[f702])).

fof(f702,plain,
    ( spl12_122
  <=> k10_relat_1(sK2,sK7(k3_funct_3(sK2),sK3,sK8(sK0,sK4))) = sK8(sK0,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_122])])).

fof(f710,plain,
    ( v4_pre_topc(k10_relat_1(sK2,sK7(k3_funct_3(sK2),sK3,sK8(sK0,sK4))),sK0)
    | ~ v4_pre_topc(sK7(k3_funct_3(sK2),sK3,sK8(sK0,sK4)),sK1)
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_10
    | ~ spl12_18
    | ~ spl12_24
    | ~ spl12_120 ),
    inference(forward_demodulation,[],[f705,f186])).

fof(f186,plain,
    ( ! [X1] : k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1) = k10_relat_1(sK2,X1)
    | ~ spl12_24 ),
    inference(resolution,[],[f177,f99])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t60_tops_2.p',redefinition_k8_relset_1)).

fof(f177,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl12_24 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl12_24
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_24])])).

fof(f705,plain,
    ( ~ v4_pre_topc(sK7(k3_funct_3(sK2),sK3,sK8(sK0,sK4)),sK1)
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK7(k3_funct_3(sK2),sK3,sK8(sK0,sK4))),sK0)
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_10
    | ~ spl12_18
    | ~ spl12_24
    | ~ spl12_120 ),
    inference(resolution,[],[f699,f194])).

fof(f194,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v4_pre_topc(X0,sK1)
        | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0) )
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_10
    | ~ spl12_18
    | ~ spl12_24 ),
    inference(subsumption_resolution,[],[f193,f125])).

fof(f125,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ spl12_10 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl12_10
  <=> v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).

fof(f193,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v4_pre_topc(X0,sK1)
        | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0)
        | ~ v5_pre_topc(sK2,sK0,sK1) )
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_18
    | ~ spl12_24 ),
    inference(subsumption_resolution,[],[f192,f113])).

fof(f113,plain,
    ( l1_pre_topc(sK0)
    | ~ spl12_4 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl12_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).

fof(f192,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v4_pre_topc(X0,sK1)
        | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0)
        | ~ v5_pre_topc(sK2,sK0,sK1) )
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_18
    | ~ spl12_24 ),
    inference(subsumption_resolution,[],[f191,f141])).

fof(f141,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl12_18 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl12_18
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_18])])).

fof(f191,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v4_pre_topc(X0,sK1)
        | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0)
        | ~ v5_pre_topc(sK2,sK0,sK1) )
    | ~ spl12_0
    | ~ spl12_2
    | ~ spl12_24 ),
    inference(subsumption_resolution,[],[f190,f105])).

fof(f105,plain,
    ( v1_funct_1(sK2)
    | ~ spl12_0 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl12_0
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_0])])).

fof(f190,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v4_pre_topc(X0,sK1)
        | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0)
        | ~ v5_pre_topc(sK2,sK0,sK1) )
    | ~ spl12_2
    | ~ spl12_24 ),
    inference(subsumption_resolution,[],[f183,f109])).

fof(f109,plain,
    ( l1_pre_topc(sK1)
    | ~ spl12_2 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl12_2
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f183,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v4_pre_topc(X0,sK1)
        | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0)
        | ~ v5_pre_topc(sK2,sK0,sK1) )
    | ~ spl12_24 ),
    inference(resolution,[],[f177,f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v4_pre_topc(X3,X1)
      | v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
      | ~ v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/tops_2__t60_tops_2.p',d12_pre_topc)).

fof(f699,plain,
    ( m1_subset_1(sK7(k3_funct_3(sK2),sK3,sK8(sK0,sK4)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl12_120 ),
    inference(avatar_component_clause,[],[f698])).

fof(f698,plain,
    ( spl12_120
  <=> m1_subset_1(sK7(k3_funct_3(sK2),sK3,sK8(sK0,sK4)),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_120])])).

fof(f713,plain,
    ( v4_pre_topc(sK7(k3_funct_3(sK2),sK3,sK8(sK0,sK4)),sK1)
    | ~ spl12_2
    | ~ spl12_8
    | ~ spl12_16
    | ~ spl12_88
    | ~ spl12_120 ),
    inference(subsumption_resolution,[],[f706,f421])).

fof(f421,plain,
    ( r2_hidden(sK7(k3_funct_3(sK2),sK3,sK8(sK0,sK4)),sK3)
    | ~ spl12_88 ),
    inference(avatar_component_clause,[],[f420])).

fof(f420,plain,
    ( spl12_88
  <=> r2_hidden(sK7(k3_funct_3(sK2),sK3,sK8(sK0,sK4)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_88])])).

fof(f706,plain,
    ( ~ r2_hidden(sK7(k3_funct_3(sK2),sK3,sK8(sK0,sK4)),sK3)
    | v4_pre_topc(sK7(k3_funct_3(sK2),sK3,sK8(sK0,sK4)),sK1)
    | ~ spl12_2
    | ~ spl12_8
    | ~ spl12_16
    | ~ spl12_120 ),
    inference(resolution,[],[f699,f165])).

fof(f165,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ r2_hidden(X0,sK3)
        | v4_pre_topc(X0,sK1) )
    | ~ spl12_2
    | ~ spl12_8
    | ~ spl12_16 ),
    inference(subsumption_resolution,[],[f164,f121])).

fof(f121,plain,
    ( v2_tops_2(sK3,sK1)
    | ~ spl12_8 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl12_8
  <=> v2_tops_2(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).

fof(f164,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ r2_hidden(X0,sK3)
        | v4_pre_topc(X0,sK1)
        | ~ v2_tops_2(sK3,sK1) )
    | ~ spl12_2
    | ~ spl12_16 ),
    inference(subsumption_resolution,[],[f159,f109])).

fof(f159,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ r2_hidden(X0,sK3)
        | v4_pre_topc(X0,sK1)
        | ~ v2_tops_2(sK3,sK1) )
    | ~ spl12_16 ),
    inference(resolution,[],[f137,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,X1)
      | v4_pre_topc(X2,X0)
      | ~ v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v4_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t60_tops_2.p',d2_tops_2)).

fof(f137,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl12_16 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl12_16
  <=> m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_16])])).

fof(f704,plain,
    ( spl12_122
    | ~ spl12_0
    | ~ spl12_28
    | ~ spl12_62
    | ~ spl12_94 ),
    inference(avatar_split_clause,[],[f454,f437,f308,f197,f104,f702])).

fof(f197,plain,
    ( spl12_28
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_28])])).

fof(f308,plain,
    ( spl12_62
  <=> sP6(sK8(sK0,sK4),sK3,k3_funct_3(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_62])])).

fof(f437,plain,
    ( spl12_94
  <=> r2_hidden(sK7(k3_funct_3(sK2),sK3,sK8(sK0,sK4)),k1_relat_1(k3_funct_3(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_94])])).

fof(f454,plain,
    ( k10_relat_1(sK2,sK7(k3_funct_3(sK2),sK3,sK8(sK0,sK4))) = sK8(sK0,sK4)
    | ~ spl12_0
    | ~ spl12_28
    | ~ spl12_62
    | ~ spl12_94 ),
    inference(forward_demodulation,[],[f453,f340])).

fof(f340,plain,
    ( k1_funct_1(k3_funct_3(sK2),sK7(k3_funct_3(sK2),sK3,sK8(sK0,sK4))) = sK8(sK0,sK4)
    | ~ spl12_62 ),
    inference(resolution,[],[f309,f73])).

fof(f73,plain,(
    ! [X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | k1_funct_1(X0,sK7(X0,X1,X3)) = X3 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t60_tops_2.p',d12_funct_1)).

fof(f309,plain,
    ( sP6(sK8(sK0,sK4),sK3,k3_funct_3(sK2))
    | ~ spl12_62 ),
    inference(avatar_component_clause,[],[f308])).

fof(f453,plain,
    ( k1_funct_1(k3_funct_3(sK2),sK7(k3_funct_3(sK2),sK3,sK8(sK0,sK4))) = k10_relat_1(sK2,sK7(k3_funct_3(sK2),sK3,sK8(sK0,sK4)))
    | ~ spl12_0
    | ~ spl12_28
    | ~ spl12_94 ),
    inference(subsumption_resolution,[],[f452,f198])).

fof(f198,plain,
    ( v1_relat_1(sK2)
    | ~ spl12_28 ),
    inference(avatar_component_clause,[],[f197])).

fof(f452,plain,
    ( ~ v1_relat_1(sK2)
    | k1_funct_1(k3_funct_3(sK2),sK7(k3_funct_3(sK2),sK3,sK8(sK0,sK4))) = k10_relat_1(sK2,sK7(k3_funct_3(sK2),sK3,sK8(sK0,sK4)))
    | ~ spl12_0
    | ~ spl12_94 ),
    inference(subsumption_resolution,[],[f445,f105])).

fof(f445,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_funct_1(k3_funct_3(sK2),sK7(k3_funct_3(sK2),sK3,sK8(sK0,sK4))) = k10_relat_1(sK2,sK7(k3_funct_3(sK2),sK3,sK8(sK0,sK4)))
    | ~ spl12_94 ),
    inference(resolution,[],[f438,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k3_funct_3(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k1_funct_1(k3_funct_3(X1),X0) = k10_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k3_funct_3(X1),X0) = k10_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(k3_funct_3(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k3_funct_3(X1),X0) = k10_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(k3_funct_3(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(k3_funct_3(X1)))
       => k1_funct_1(k3_funct_3(X1),X0) = k10_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t60_tops_2.p',t24_funct_3)).

fof(f438,plain,
    ( r2_hidden(sK7(k3_funct_3(sK2),sK3,sK8(sK0,sK4)),k1_relat_1(k3_funct_3(sK2)))
    | ~ spl12_94 ),
    inference(avatar_component_clause,[],[f437])).

fof(f700,plain,
    ( spl12_120
    | ~ spl12_16
    | ~ spl12_88 ),
    inference(avatar_split_clause,[],[f696,f420,f136,f698])).

fof(f696,plain,
    ( m1_subset_1(sK7(k3_funct_3(sK2),sK3,sK8(sK0,sK4)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl12_16
    | ~ spl12_88 ),
    inference(resolution,[],[f431,f137])).

fof(f431,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X1))
        | m1_subset_1(sK7(k3_funct_3(sK2),sK3,sK8(sK0,sK4)),X1) )
    | ~ spl12_88 ),
    inference(resolution,[],[f421,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t60_tops_2.p',t4_subset)).

fof(f439,plain,
    ( spl12_94
    | ~ spl12_62 ),
    inference(avatar_split_clause,[],[f338,f308,f437])).

fof(f338,plain,
    ( r2_hidden(sK7(k3_funct_3(sK2),sK3,sK8(sK0,sK4)),k1_relat_1(k3_funct_3(sK2)))
    | ~ spl12_62 ),
    inference(resolution,[],[f309,f71])).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | r2_hidden(sK7(X0,X1,X3),k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f422,plain,
    ( spl12_88
    | ~ spl12_62 ),
    inference(avatar_split_clause,[],[f339,f308,f420])).

fof(f339,plain,
    ( r2_hidden(sK7(k3_funct_3(sK2),sK3,sK8(sK0,sK4)),sK3)
    | ~ spl12_62 ),
    inference(resolution,[],[f309,f72])).

fof(f72,plain,(
    ! [X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | r2_hidden(sK7(X0,X1,X3),X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f310,plain,
    ( spl12_62
    | ~ spl12_0
    | ~ spl12_14
    | ~ spl12_20
    | ~ spl12_28 ),
    inference(avatar_split_clause,[],[f228,f197,f156,f132,f104,f308])).

fof(f132,plain,
    ( spl12_14
  <=> k9_relat_1(k3_funct_3(sK2),sK3) = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_14])])).

fof(f156,plain,
    ( spl12_20
  <=> r2_hidden(sK8(sK0,sK4),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_20])])).

fof(f228,plain,
    ( sP6(sK8(sK0,sK4),sK3,k3_funct_3(sK2))
    | ~ spl12_0
    | ~ spl12_14
    | ~ spl12_20
    | ~ spl12_28 ),
    inference(resolution,[],[f206,f157])).

fof(f157,plain,
    ( r2_hidden(sK8(sK0,sK4),sK4)
    | ~ spl12_20 ),
    inference(avatar_component_clause,[],[f156])).

fof(f206,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK4)
        | sP6(X0,sK3,k3_funct_3(sK2)) )
    | ~ spl12_0
    | ~ spl12_14
    | ~ spl12_28 ),
    inference(subsumption_resolution,[],[f204,f205])).

fof(f205,plain,
    ( v1_funct_1(k3_funct_3(sK2))
    | ~ spl12_0
    | ~ spl12_28 ),
    inference(subsumption_resolution,[],[f201,f105])).

fof(f201,plain,
    ( ~ v1_funct_1(sK2)
    | v1_funct_1(k3_funct_3(sK2))
    | ~ spl12_28 ),
    inference(resolution,[],[f198,f80])).

fof(f80,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_funct_1(k3_funct_3(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_funct_1(k3_funct_3(X0))
        & v1_relat_1(k3_funct_3(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_funct_1(k3_funct_3(X0))
        & v1_relat_1(k3_funct_3(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k3_funct_3(X0))
        & v1_relat_1(k3_funct_3(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t60_tops_2.p',dt_k3_funct_3)).

fof(f204,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK4)
        | ~ v1_funct_1(k3_funct_3(sK2))
        | sP6(X0,sK3,k3_funct_3(sK2)) )
    | ~ spl12_0
    | ~ spl12_14
    | ~ spl12_28 ),
    inference(subsumption_resolution,[],[f154,f203])).

fof(f203,plain,
    ( v1_relat_1(k3_funct_3(sK2))
    | ~ spl12_0
    | ~ spl12_28 ),
    inference(subsumption_resolution,[],[f200,f105])).

fof(f200,plain,
    ( ~ v1_funct_1(sK2)
    | v1_relat_1(k3_funct_3(sK2))
    | ~ spl12_28 ),
    inference(resolution,[],[f198,f79])).

fof(f79,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_relat_1(k3_funct_3(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f154,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK4)
        | ~ v1_funct_1(k3_funct_3(sK2))
        | sP6(X0,sK3,k3_funct_3(sK2))
        | ~ v1_relat_1(k3_funct_3(sK2)) )
    | ~ spl12_14 ),
    inference(superposition,[],[f100,f133])).

fof(f133,plain,
    ( k9_relat_1(k3_funct_3(sK2),sK3) = sK4
    | ~ spl12_14 ),
    inference(avatar_component_clause,[],[f132])).

fof(f100,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | sP6(X3,X1,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | sP6(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f199,plain,
    ( spl12_28
    | ~ spl12_24 ),
    inference(avatar_split_clause,[],[f187,f176,f197])).

fof(f187,plain,
    ( v1_relat_1(sK2)
    | ~ spl12_24 ),
    inference(resolution,[],[f177,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t60_tops_2.p',cc1_relset_1)).

fof(f178,plain,(
    spl12_24 ),
    inference(avatar_split_clause,[],[f66,f176])).

fof(f66,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ v2_tops_2(X4,X0)
                      & k9_relat_1(k3_funct_3(X2),X3) = X4
                      & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                  & v2_tops_2(X3,X1)
                  & v5_pre_topc(X2,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ v2_tops_2(X4,X0)
                      & k9_relat_1(k3_funct_3(X2),X3) = X4
                      & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                  & v2_tops_2(X3,X1)
                  & v5_pre_topc(X2,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                   => ( ( v2_tops_2(X3,X1)
                        & v5_pre_topc(X2,X0,X1) )
                     => ! [X4] :
                          ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                         => ( k9_relat_1(k3_funct_3(X2),X3) = X4
                           => v2_tops_2(X4,X0) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                 => ( ( v2_tops_2(X3,X1)
                      & v5_pre_topc(X2,X0,X1) )
                   => ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                       => ( k9_relat_1(k3_funct_3(X2),X3) = X4
                         => v2_tops_2(X4,X0) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t60_tops_2.p',t60_tops_2)).

fof(f169,plain,
    ( ~ spl12_23
    | ~ spl12_4
    | spl12_7
    | ~ spl12_12 ),
    inference(avatar_split_clause,[],[f153,f128,f116,f112,f167])).

fof(f116,plain,
    ( spl12_7
  <=> ~ v2_tops_2(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_7])])).

fof(f128,plain,
    ( spl12_12
  <=> m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_12])])).

fof(f153,plain,
    ( ~ v4_pre_topc(sK8(sK0,sK4),sK0)
    | ~ spl12_4
    | ~ spl12_7
    | ~ spl12_12 ),
    inference(subsumption_resolution,[],[f152,f117])).

fof(f117,plain,
    ( ~ v2_tops_2(sK4,sK0)
    | ~ spl12_7 ),
    inference(avatar_component_clause,[],[f116])).

fof(f152,plain,
    ( ~ v4_pre_topc(sK8(sK0,sK4),sK0)
    | v2_tops_2(sK4,sK0)
    | ~ spl12_4
    | ~ spl12_12 ),
    inference(subsumption_resolution,[],[f146,f113])).

fof(f146,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v4_pre_topc(sK8(sK0,sK4),sK0)
    | v2_tops_2(sK4,sK0)
    | ~ spl12_12 ),
    inference(resolution,[],[f129,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(sK8(X0,X1),X0)
      | v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f129,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl12_12 ),
    inference(avatar_component_clause,[],[f128])).

fof(f158,plain,
    ( spl12_20
    | ~ spl12_4
    | spl12_7
    | ~ spl12_12 ),
    inference(avatar_split_clause,[],[f151,f128,f116,f112,f156])).

fof(f151,plain,
    ( r2_hidden(sK8(sK0,sK4),sK4)
    | ~ spl12_4
    | ~ spl12_7
    | ~ spl12_12 ),
    inference(subsumption_resolution,[],[f150,f117])).

fof(f150,plain,
    ( r2_hidden(sK8(sK0,sK4),sK4)
    | v2_tops_2(sK4,sK0)
    | ~ spl12_4
    | ~ spl12_12 ),
    inference(subsumption_resolution,[],[f145,f113])).

fof(f145,plain,
    ( ~ l1_pre_topc(sK0)
    | r2_hidden(sK8(sK0,sK4),sK4)
    | v2_tops_2(sK4,sK0)
    | ~ spl12_12 ),
    inference(resolution,[],[f129,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | r2_hidden(sK8(X0,X1),X1)
      | v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f142,plain,(
    spl12_18 ),
    inference(avatar_split_clause,[],[f65,f140])).

fof(f65,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f138,plain,(
    spl12_16 ),
    inference(avatar_split_clause,[],[f61,f136])).

fof(f61,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f35])).

fof(f134,plain,(
    spl12_14 ),
    inference(avatar_split_clause,[],[f59,f132])).

fof(f59,plain,(
    k9_relat_1(k3_funct_3(sK2),sK3) = sK4 ),
    inference(cnf_transformation,[],[f35])).

fof(f130,plain,(
    spl12_12 ),
    inference(avatar_split_clause,[],[f58,f128])).

fof(f58,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f35])).

fof(f126,plain,(
    spl12_10 ),
    inference(avatar_split_clause,[],[f62,f124])).

fof(f62,plain,(
    v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f122,plain,(
    spl12_8 ),
    inference(avatar_split_clause,[],[f63,f120])).

fof(f63,plain,(
    v2_tops_2(sK3,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f118,plain,(
    ~ spl12_7 ),
    inference(avatar_split_clause,[],[f60,f116])).

fof(f60,plain,(
    ~ v2_tops_2(sK4,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f114,plain,(
    spl12_4 ),
    inference(avatar_split_clause,[],[f68,f112])).

fof(f68,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f110,plain,(
    spl12_2 ),
    inference(avatar_split_clause,[],[f67,f108])).

fof(f67,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f106,plain,(
    spl12_0 ),
    inference(avatar_split_clause,[],[f64,f104])).

fof(f64,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
