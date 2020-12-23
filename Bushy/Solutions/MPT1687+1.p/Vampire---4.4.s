%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_0__t67_waybel_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:01 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  171 ( 406 expanded)
%              Number of leaves         :   39 ( 165 expanded)
%              Depth                    :   16
%              Number of atoms          :  708 (1724 expanded)
%              Number of equality atoms :   82 ( 178 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f608,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f131,f135,f139,f143,f147,f153,f157,f165,f169,f215,f228,f232,f253,f261,f303,f330,f336,f443,f471,f472,f523,f528,f606,f607])).

fof(f607,plain,
    ( u1_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k1_relat_1(sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2)))) ),
    introduced(theory_axiom,[])).

fof(f606,plain,
    ( spl8_112
    | ~ spl8_0
    | spl8_3
    | ~ spl8_4
    | spl8_7
    | ~ spl8_8
    | ~ spl8_12
    | ~ spl8_16
    | ~ spl8_18
    | ~ spl8_20
    | ~ spl8_28
    | ~ spl8_30
    | ~ spl8_32 ),
    inference(avatar_split_clause,[],[f273,f251,f230,f259,f213,f167,f163,f155,f145,f141,f137,f133,f129,f604])).

fof(f604,plain,
    ( spl8_112
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_112])])).

fof(f129,plain,
    ( spl8_0
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_0])])).

fof(f133,plain,
    ( spl8_3
  <=> ~ v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f137,plain,
    ( spl8_4
  <=> l1_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f141,plain,
    ( spl8_7
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f145,plain,
    ( spl8_8
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f155,plain,
    ( spl8_12
  <=> v23_waybel_0(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f163,plain,
    ( spl8_16
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f167,plain,
    ( spl8_18
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f213,plain,
    ( spl8_20
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f259,plain,
    ( spl8_28
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f230,plain,
    ( spl8_30
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f251,plain,
    ( spl8_32
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f273,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2))))
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_12
    | ~ spl8_16
    | ~ spl8_18
    | ~ spl8_20
    | ~ spl8_28
    | ~ spl8_30
    | ~ spl8_32 ),
    inference(forward_demodulation,[],[f272,f247])).

fof(f247,plain,
    ( u1_struct_0(sK1) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_12
    | ~ spl8_16
    | ~ spl8_18
    | ~ spl8_20
    | ~ spl8_30 ),
    inference(forward_demodulation,[],[f246,f206])).

fof(f206,plain,
    ( u1_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_12
    | ~ spl8_16
    | ~ spl8_18 ),
    inference(forward_demodulation,[],[f176,f205])).

fof(f205,plain,
    ( u1_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_12
    | ~ spl8_16
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f204,f156])).

fof(f156,plain,
    ( v23_waybel_0(sK2,sK0,sK1)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f155])).

fof(f204,plain,
    ( u1_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_16
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f203,f142])).

fof(f142,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f141])).

fof(f203,plain,
    ( v2_struct_0(sK0)
    | u1_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_16
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f202,f164])).

fof(f164,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f163])).

fof(f202,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | u1_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f201,f130])).

fof(f130,plain,
    ( v1_funct_1(sK2)
    | ~ spl8_0 ),
    inference(avatar_component_clause,[],[f129])).

fof(f201,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | u1_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f200,f138])).

fof(f138,plain,
    ( l1_orders_2(sK1)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f137])).

fof(f200,plain,
    ( ~ l1_orders_2(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | u1_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl8_3
    | ~ spl8_8
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f199,f134])).

fof(f134,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f133])).

fof(f199,plain,
    ( v2_struct_0(sK1)
    | ~ l1_orders_2(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | u1_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl8_8
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f175,f146])).

fof(f146,plain,
    ( l1_orders_2(sK0)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f145])).

fof(f175,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | u1_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl8_18 ),
    inference(resolution,[],[f168,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v2_struct_0(X0)
      | u1_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | ~ v23_waybel_0(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v23_waybel_0(X2,X0,X1)
              <=> ( ! [X3] :
                      ( ! [X4] :
                          ( ( r1_orders_2(X0,X3,X4)
                          <=> r1_orders_2(X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) )
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & u1_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & v2_funct_1(X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v23_waybel_0(X2,X0,X1)
              <=> ( ! [X3] :
                      ( ! [X4] :
                          ( ( r1_orders_2(X0,X3,X4)
                          <=> r1_orders_2(X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) )
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & u1_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & v2_funct_1(X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v23_waybel_0(X2,X0,X1)
              <=> ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( r1_orders_2(X0,X3,X4)
                          <=> r1_orders_2(X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) ) ) )
                  & u1_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & v2_funct_1(X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t67_waybel_0.p',t66_waybel_0)).

fof(f168,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f167])).

fof(f176,plain,
    ( k2_relat_1(sK2) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl8_18 ),
    inference(resolution,[],[f168,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t67_waybel_0.p',redefinition_k2_relset_1)).

fof(f246,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl8_0
    | ~ spl8_20
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f245,f214])).

fof(f214,plain,
    ( v1_relat_1(sK2)
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f213])).

fof(f245,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl8_0
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f243,f130])).

fof(f243,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl8_30 ),
    inference(resolution,[],[f231,f85])).

fof(f85,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t67_waybel_0.p',t55_funct_1)).

fof(f231,plain,
    ( v2_funct_1(sK2)
    | ~ spl8_30 ),
    inference(avatar_component_clause,[],[f230])).

fof(f272,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))))
    | ~ spl8_0
    | ~ spl8_20
    | ~ spl8_28
    | ~ spl8_30
    | ~ spl8_32 ),
    inference(forward_demodulation,[],[f271,f249])).

fof(f249,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | ~ spl8_0
    | ~ spl8_20
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f248,f214])).

fof(f248,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | ~ spl8_0
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f244,f130])).

fof(f244,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | ~ spl8_30 ),
    inference(resolution,[],[f231,f86])).

fof(f86,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f271,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))
    | ~ spl8_28
    | ~ spl8_32 ),
    inference(subsumption_resolution,[],[f265,f260])).

fof(f260,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f259])).

fof(f265,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))
    | ~ spl8_32 ),
    inference(resolution,[],[f252,f88])).

fof(f88,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t67_waybel_0.p',t3_funct_2)).

fof(f252,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl8_32 ),
    inference(avatar_component_clause,[],[f251])).

fof(f528,plain,
    ( spl8_26
    | ~ spl8_56
    | ~ spl8_88 ),
    inference(avatar_split_clause,[],[f524,f521,f332,f526])).

fof(f526,plain,
    ( spl8_26
  <=> v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f332,plain,
    ( spl8_56
  <=> u1_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_56])])).

fof(f521,plain,
    ( spl8_88
  <=> v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_88])])).

fof(f524,plain,
    ( v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl8_56
    | ~ spl8_88 ),
    inference(forward_demodulation,[],[f522,f333])).

fof(f333,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl8_56 ),
    inference(avatar_component_clause,[],[f332])).

fof(f522,plain,
    ( v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),k1_relat_1(sK2))
    | ~ spl8_88 ),
    inference(avatar_component_clause,[],[f521])).

fof(f523,plain,
    ( spl8_88
    | ~ spl8_0
    | spl8_3
    | ~ spl8_4
    | spl8_7
    | ~ spl8_8
    | ~ spl8_12
    | ~ spl8_16
    | ~ spl8_18
    | ~ spl8_20
    | ~ spl8_28
    | ~ spl8_30
    | ~ spl8_32 ),
    inference(avatar_split_clause,[],[f270,f251,f230,f259,f213,f167,f163,f155,f145,f141,f137,f133,f129,f521])).

fof(f270,plain,
    ( v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),k1_relat_1(sK2))
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_12
    | ~ spl8_16
    | ~ spl8_18
    | ~ spl8_20
    | ~ spl8_28
    | ~ spl8_30
    | ~ spl8_32 ),
    inference(forward_demodulation,[],[f269,f247])).

fof(f269,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))
    | ~ spl8_0
    | ~ spl8_20
    | ~ spl8_28
    | ~ spl8_30
    | ~ spl8_32 ),
    inference(forward_demodulation,[],[f268,f249])).

fof(f268,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))
    | ~ spl8_28
    | ~ spl8_32 ),
    inference(subsumption_resolution,[],[f264,f260])).

fof(f264,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))
    | ~ spl8_32 ),
    inference(resolution,[],[f252,f87])).

fof(f87,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f472,plain,
    ( u1_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
    | u1_struct_0(sK0) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(theory_axiom,[])).

fof(f471,plain,
    ( spl8_72
    | ~ spl8_0
    | ~ spl8_20
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f249,f230,f213,f129,f469])).

fof(f469,plain,
    ( spl8_72
  <=> k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_72])])).

fof(f443,plain,
    ( spl8_3
    | ~ spl8_10
    | ~ spl8_54 ),
    inference(avatar_contradiction_clause,[],[f442])).

fof(f442,plain,
    ( $false
    | ~ spl8_3
    | ~ spl8_10
    | ~ spl8_54 ),
    inference(subsumption_resolution,[],[f441,f134])).

fof(f441,plain,
    ( v2_struct_0(sK1)
    | ~ spl8_10
    | ~ spl8_54 ),
    inference(subsumption_resolution,[],[f440,f152])).

fof(f152,plain,
    ( l1_struct_0(sK1)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl8_10
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f440,plain,
    ( ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl8_54 ),
    inference(subsumption_resolution,[],[f367,f118])).

fof(f118,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t67_waybel_0.p',fc1_xboole_0)).

fof(f367,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl8_54 ),
    inference(superposition,[],[f107,f329])).

fof(f329,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | ~ spl8_54 ),
    inference(avatar_component_clause,[],[f328])).

fof(f328,plain,
    ( spl8_54
  <=> u1_struct_0(sK1) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_54])])).

fof(f107,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t67_waybel_0.p',fc2_struct_0)).

fof(f336,plain,
    ( spl8_56
    | ~ spl8_44
    | ~ spl8_52 ),
    inference(avatar_split_clause,[],[f334,f325,f301,f332])).

fof(f301,plain,
    ( spl8_44
  <=> k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_44])])).

fof(f325,plain,
    ( spl8_52
  <=> u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_52])])).

fof(f334,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl8_44
    | ~ spl8_52 ),
    inference(superposition,[],[f326,f302])).

fof(f302,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k1_relat_1(sK2)
    | ~ spl8_44 ),
    inference(avatar_component_clause,[],[f301])).

fof(f326,plain,
    ( u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl8_52 ),
    inference(avatar_component_clause,[],[f325])).

fof(f330,plain,
    ( spl8_52
    | spl8_54
    | ~ spl8_16
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f209,f167,f163,f328,f325])).

fof(f209,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl8_16
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f179,f164])).

fof(f179,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl8_18 ),
    inference(resolution,[],[f168,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t67_waybel_0.p',d1_funct_2)).

fof(f303,plain,
    ( spl8_44
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f181,f167,f301])).

fof(f181,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k1_relat_1(sK2)
    | ~ spl8_18 ),
    inference(resolution,[],[f168,f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t67_waybel_0.p',redefinition_k1_relset_1)).

fof(f261,plain,
    ( spl8_28
    | ~ spl8_0
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f238,f213,f129,f259])).

fof(f238,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl8_0
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f234,f130])).

fof(f234,plain,
    ( ~ v1_funct_1(sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ spl8_20 ),
    inference(resolution,[],[f214,f90])).

fof(f90,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_funct_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t67_waybel_0.p',dt_k2_funct_1)).

fof(f253,plain,
    ( spl8_32
    | ~ spl8_0
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f237,f213,f129,f251])).

fof(f237,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl8_0
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f233,f130])).

fof(f233,plain,
    ( ~ v1_funct_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ spl8_20 ),
    inference(resolution,[],[f214,f89])).

fof(f89,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f232,plain,
    ( spl8_30
    | ~ spl8_0
    | spl8_3
    | ~ spl8_4
    | spl8_7
    | ~ spl8_8
    | ~ spl8_12
    | ~ spl8_16
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f198,f167,f163,f155,f145,f141,f137,f133,f129,f230])).

fof(f198,plain,
    ( v2_funct_1(sK2)
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_12
    | ~ spl8_16
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f197,f156])).

fof(f197,plain,
    ( v2_funct_1(sK2)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_16
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f196,f142])).

fof(f196,plain,
    ( v2_struct_0(sK0)
    | v2_funct_1(sK2)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_16
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f195,f164])).

fof(f195,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | v2_funct_1(sK2)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl8_0
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f194,f130])).

fof(f194,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | v2_funct_1(sK2)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f193,f138])).

fof(f193,plain,
    ( ~ l1_orders_2(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | v2_funct_1(sK2)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl8_3
    | ~ spl8_8
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f192,f134])).

fof(f192,plain,
    ( v2_struct_0(sK1)
    | ~ l1_orders_2(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | v2_funct_1(sK2)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl8_8
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f174,f146])).

fof(f174,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | v2_funct_1(sK2)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl8_18 ),
    inference(resolution,[],[f168,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v2_struct_0(X0)
      | v2_funct_1(X2)
      | ~ v23_waybel_0(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f228,plain,
    ( ~ spl8_23
    | ~ spl8_25
    | ~ spl8_27
    | ~ spl8_29 ),
    inference(avatar_split_clause,[],[f74,f226,f223,f220,f217])).

fof(f217,plain,
    ( spl8_23
  <=> u1_struct_0(sK0) != k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f220,plain,
    ( spl8_25
  <=> ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f223,plain,
    ( spl8_27
  <=> ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f226,plain,
    ( spl8_29
  <=> ~ v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).

fof(f74,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | u1_struct_0(sK0) != k2_relat_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( u1_struct_0(X0) != k2_relat_1(k2_funct_1(X2))
                | ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                | ~ v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0))
                | ~ v1_funct_1(k2_funct_1(X2)) )
              & v23_waybel_0(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( u1_struct_0(X0) != k2_relat_1(k2_funct_1(X2))
                | ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                | ~ v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0))
                | ~ v1_funct_1(k2_funct_1(X2)) )
              & v23_waybel_0(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( v23_waybel_0(X2,X0,X1)
                 => ( u1_struct_0(X0) = k2_relat_1(k2_funct_1(X2))
                    & m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                    & v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0))
                    & v1_funct_1(k2_funct_1(X2)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v23_waybel_0(X2,X0,X1)
               => ( u1_struct_0(X0) = k2_relat_1(k2_funct_1(X2))
                  & m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(k2_funct_1(X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t67_waybel_0.p',t67_waybel_0)).

fof(f215,plain,
    ( spl8_20
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f182,f167,f213])).

fof(f182,plain,
    ( v1_relat_1(sK2)
    | ~ spl8_18 ),
    inference(resolution,[],[f168,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t67_waybel_0.p',cc1_relset_1)).

fof(f169,plain,(
    spl8_18 ),
    inference(avatar_split_clause,[],[f77,f167])).

fof(f77,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f43])).

fof(f165,plain,(
    spl8_16 ),
    inference(avatar_split_clause,[],[f76,f163])).

fof(f76,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f43])).

fof(f157,plain,(
    spl8_12 ),
    inference(avatar_split_clause,[],[f78,f155])).

fof(f78,plain,(
    v23_waybel_0(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f153,plain,
    ( spl8_10
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f148,f137,f151])).

fof(f148,plain,
    ( l1_struct_0(sK1)
    | ~ spl8_4 ),
    inference(resolution,[],[f138,f109])).

fof(f109,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t67_waybel_0.p',dt_l1_orders_2)).

fof(f147,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f82,f145])).

fof(f82,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f143,plain,(
    ~ spl8_7 ),
    inference(avatar_split_clause,[],[f81,f141])).

fof(f81,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f139,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f80,f137])).

fof(f80,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f135,plain,(
    ~ spl8_3 ),
    inference(avatar_split_clause,[],[f79,f133])).

fof(f79,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f131,plain,(
    spl8_0 ),
    inference(avatar_split_clause,[],[f75,f129])).

fof(f75,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
