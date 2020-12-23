%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1688+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:29 EST 2020

% Result     : Theorem 11.83s
% Output     : Refutation 11.83s
% Verified   : 
% Statistics : Number of formulae       :  192 ( 475 expanded)
%              Number of leaves         :   50 ( 242 expanded)
%              Depth                    :   15
%              Number of atoms          :  972 (3378 expanded)
%              Number of equality atoms :   73 ( 302 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15199,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f4306,f4311,f4316,f4321,f4326,f4331,f4336,f4341,f4346,f4351,f4356,f4361,f4366,f4705,f5011,f6098,f9078,f9083,f11460,f11646,f11647,f11649,f11861,f11863,f11871,f11946,f12013,f12097,f15151,f15170,f15196,f15197,f15198])).

fof(f15198,plain,
    ( sK11 != sK27(sK8,sK9,sK10)
    | v5_orders_3(sK11,sK9,sK8)
    | ~ v5_orders_3(sK27(sK8,sK9,sK10),sK9,sK8) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f15197,plain,
    ( spl117_746
    | spl117_13
    | spl117_11
    | ~ spl117_6
    | ~ spl117_250 ),
    inference(avatar_split_clause,[],[f15164,f9080,f4328,f4353,f4363,f15148])).

fof(f15148,plain,
    ( spl117_746
  <=> v5_orders_3(sK10,sK8,sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_746])])).

fof(f4363,plain,
    ( spl117_13
  <=> v2_struct_0(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_13])])).

fof(f4353,plain,
    ( spl117_11
  <=> v2_struct_0(sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_11])])).

fof(f4328,plain,
    ( spl117_6
  <=> v23_waybel_0(sK10,sK8,sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_6])])).

fof(f9080,plain,
    ( spl117_250
  <=> sP2(sK8,sK9,sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_250])])).

fof(f15164,plain,
    ( ~ v23_waybel_0(sK10,sK8,sK9)
    | v2_struct_0(sK9)
    | v2_struct_0(sK8)
    | v5_orders_3(sK10,sK8,sK9)
    | ~ spl117_250 ),
    inference(resolution,[],[f9082,f3888])).

fof(f3888,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | ~ v23_waybel_0(X2,X0,X1)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | v5_orders_3(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f3624])).

fof(f3624,plain,(
    ! [X0,X1,X2] :
      ( ( ( v23_waybel_0(X2,X0,X1)
          | ! [X3] :
              ( ~ v5_orders_3(X3,X1,X0)
              | k2_funct_1(X2) != X3
              | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X3) )
          | ~ v5_orders_3(X2,X0,X1)
          | ~ v2_funct_1(X2) )
        & ( ( v5_orders_3(sK27(X0,X1,X2),X1,X0)
            & k2_funct_1(X2) = sK27(X0,X1,X2)
            & m1_subset_1(sK27(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
            & v1_funct_2(sK27(X0,X1,X2),u1_struct_0(X1),u1_struct_0(X0))
            & v1_funct_1(sK27(X0,X1,X2))
            & v5_orders_3(X2,X0,X1)
            & v2_funct_1(X2) )
          | ~ v23_waybel_0(X2,X0,X1) ) )
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ sP2(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK27])],[f3622,f3623])).

fof(f3623,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( v5_orders_3(X4,X1,X0)
          & k2_funct_1(X2) = X4
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(X4) )
     => ( v5_orders_3(sK27(X0,X1,X2),X1,X0)
        & k2_funct_1(X2) = sK27(X0,X1,X2)
        & m1_subset_1(sK27(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(sK27(X0,X1,X2),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(sK27(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3622,plain,(
    ! [X0,X1,X2] :
      ( ( ( v23_waybel_0(X2,X0,X1)
          | ! [X3] :
              ( ~ v5_orders_3(X3,X1,X0)
              | k2_funct_1(X2) != X3
              | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X3) )
          | ~ v5_orders_3(X2,X0,X1)
          | ~ v2_funct_1(X2) )
        & ( ( ? [X4] :
                ( v5_orders_3(X4,X1,X0)
                & k2_funct_1(X2) = X4
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X4) )
            & v5_orders_3(X2,X0,X1)
            & v2_funct_1(X2) )
          | ~ v23_waybel_0(X2,X0,X1) ) )
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f3621])).

fof(f3621,plain,(
    ! [X0,X1,X2] :
      ( ( ( v23_waybel_0(X2,X0,X1)
          | ! [X3] :
              ( ~ v5_orders_3(X3,X1,X0)
              | k2_funct_1(X2) != X3
              | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X3) )
          | ~ v5_orders_3(X2,X0,X1)
          | ~ v2_funct_1(X2) )
        & ( ( ? [X3] :
                ( v5_orders_3(X3,X1,X0)
                & k2_funct_1(X2) = X3
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X3) )
            & v5_orders_3(X2,X0,X1)
            & v2_funct_1(X2) )
          | ~ v23_waybel_0(X2,X0,X1) ) )
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ sP2(X0,X1,X2) ) ),
    inference(flattening,[],[f3620])).

fof(f3620,plain,(
    ! [X0,X1,X2] :
      ( ( ( v23_waybel_0(X2,X0,X1)
          | ! [X3] :
              ( ~ v5_orders_3(X3,X1,X0)
              | k2_funct_1(X2) != X3
              | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X3) )
          | ~ v5_orders_3(X2,X0,X1)
          | ~ v2_funct_1(X2) )
        & ( ( ? [X3] :
                ( v5_orders_3(X3,X1,X0)
                & k2_funct_1(X2) = X3
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X3) )
            & v5_orders_3(X2,X0,X1)
            & v2_funct_1(X2) )
          | ~ v23_waybel_0(X2,X0,X1) ) )
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ sP2(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f3558])).

fof(f3558,plain,(
    ! [X0,X1,X2] :
      ( ( v23_waybel_0(X2,X0,X1)
      <=> ( ? [X3] :
              ( v5_orders_3(X3,X1,X0)
              & k2_funct_1(X2) = X3
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X3) )
          & v5_orders_3(X2,X0,X1)
          & v2_funct_1(X2) ) )
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ sP2(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f9082,plain,
    ( sP2(sK8,sK9,sK10)
    | ~ spl117_250 ),
    inference(avatar_component_clause,[],[f9080])).

fof(f15196,plain,
    ( spl117_13
    | spl117_11
    | ~ spl117_6
    | spl117_748
    | ~ spl117_2
    | ~ spl117_250 ),
    inference(avatar_split_clause,[],[f15195,f9080,f4308,f15173,f4328,f4353,f4363])).

fof(f15173,plain,
    ( spl117_748
  <=> sK11 = sK27(sK8,sK9,sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_748])])).

fof(f4308,plain,
    ( spl117_2
  <=> k2_funct_1(sK10) = sK11 ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_2])])).

fof(f15195,plain,
    ( sK11 = sK27(sK8,sK9,sK10)
    | ~ v23_waybel_0(sK10,sK8,sK9)
    | v2_struct_0(sK9)
    | v2_struct_0(sK8)
    | ~ spl117_2
    | ~ spl117_250 ),
    inference(forward_demodulation,[],[f15163,f4310])).

fof(f4310,plain,
    ( k2_funct_1(sK10) = sK11
    | ~ spl117_2 ),
    inference(avatar_component_clause,[],[f4308])).

fof(f15163,plain,
    ( ~ v23_waybel_0(sK10,sK8,sK9)
    | v2_struct_0(sK9)
    | v2_struct_0(sK8)
    | k2_funct_1(sK10) = sK27(sK8,sK9,sK10)
    | ~ spl117_250 ),
    inference(resolution,[],[f9082,f3892])).

fof(f3892,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | ~ v23_waybel_0(X2,X0,X1)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | k2_funct_1(X2) = sK27(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f3624])).

fof(f15170,plain,
    ( spl117_747
    | ~ spl117_6
    | spl117_11
    | spl117_13
    | ~ spl117_250 ),
    inference(avatar_split_clause,[],[f15161,f9080,f4363,f4353,f4328,f15167])).

fof(f15167,plain,
    ( spl117_747
  <=> v5_orders_3(sK27(sK8,sK9,sK10),sK9,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_747])])).

fof(f15161,plain,
    ( v5_orders_3(sK27(sK8,sK9,sK10),sK9,sK8)
    | ~ spl117_6
    | spl117_11
    | spl117_13
    | ~ spl117_250 ),
    inference(unit_resulting_resolution,[],[f4355,f4365,f4330,f9082,f3893])).

fof(f3893,plain,(
    ! [X2,X0,X1] :
      ( v5_orders_3(sK27(X0,X1,X2),X1,X0)
      | ~ v23_waybel_0(X2,X0,X1)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f3624])).

fof(f4330,plain,
    ( v23_waybel_0(sK10,sK8,sK9)
    | ~ spl117_6 ),
    inference(avatar_component_clause,[],[f4328])).

fof(f4365,plain,
    ( ~ v2_struct_0(sK8)
    | spl117_13 ),
    inference(avatar_component_clause,[],[f4363])).

fof(f4355,plain,
    ( ~ v2_struct_0(sK9)
    | spl117_11 ),
    inference(avatar_component_clause,[],[f4353])).

fof(f15151,plain,
    ( spl117_1
    | spl117_11
    | spl117_13
    | ~ spl117_465
    | ~ spl117_745
    | ~ spl117_746
    | ~ spl117_469
    | ~ spl117_478
    | ~ spl117_9
    | ~ spl117_249
    | ~ spl117_443
    | ~ spl117_475 ),
    inference(avatar_split_clause,[],[f15142,f12010,f11730,f9075,f4343,f12094,f11943,f15148,f15144,f11868,f4363,f4353,f4303])).

fof(f4303,plain,
    ( spl117_1
  <=> v23_waybel_0(sK11,sK9,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_1])])).

fof(f11868,plain,
    ( spl117_465
  <=> v2_funct_1(sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_465])])).

fof(f15144,plain,
    ( spl117_745
  <=> v5_orders_3(sK11,sK9,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_745])])).

fof(f11943,plain,
    ( spl117_469
  <=> m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK11),u1_struct_0(sK9)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_469])])).

fof(f12094,plain,
    ( spl117_478
  <=> v1_funct_2(sK10,k2_relat_1(sK11),u1_struct_0(sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_478])])).

fof(f4343,plain,
    ( spl117_9
  <=> v1_funct_1(sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_9])])).

fof(f9075,plain,
    ( spl117_249
  <=> sP2(sK9,sK8,sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_249])])).

fof(f11730,plain,
    ( spl117_443
  <=> sK10 = k2_funct_1(sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_443])])).

fof(f12010,plain,
    ( spl117_475
  <=> u1_struct_0(sK8) = k2_relat_1(sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_475])])).

fof(f15142,plain,
    ( ~ v1_funct_1(sK10)
    | ~ v1_funct_2(sK10,k2_relat_1(sK11),u1_struct_0(sK9))
    | ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK11),u1_struct_0(sK9))))
    | ~ v5_orders_3(sK10,sK8,sK9)
    | ~ v5_orders_3(sK11,sK9,sK8)
    | ~ v2_funct_1(sK11)
    | v2_struct_0(sK8)
    | v2_struct_0(sK9)
    | v23_waybel_0(sK11,sK9,sK8)
    | ~ spl117_249
    | ~ spl117_443
    | ~ spl117_475 ),
    inference(forward_demodulation,[],[f15141,f11732])).

fof(f11732,plain,
    ( sK10 = k2_funct_1(sK11)
    | ~ spl117_443 ),
    inference(avatar_component_clause,[],[f11730])).

fof(f15141,plain,
    ( ~ v1_funct_2(sK10,k2_relat_1(sK11),u1_struct_0(sK9))
    | ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK11),u1_struct_0(sK9))))
    | ~ v5_orders_3(sK10,sK8,sK9)
    | ~ v1_funct_1(k2_funct_1(sK11))
    | ~ v5_orders_3(sK11,sK9,sK8)
    | ~ v2_funct_1(sK11)
    | v2_struct_0(sK8)
    | v2_struct_0(sK9)
    | v23_waybel_0(sK11,sK9,sK8)
    | ~ spl117_249
    | ~ spl117_443
    | ~ spl117_475 ),
    inference(forward_demodulation,[],[f15140,f11732])).

fof(f15140,plain,
    ( ~ v1_funct_2(k2_funct_1(sK11),k2_relat_1(sK11),u1_struct_0(sK9))
    | ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK11),u1_struct_0(sK9))))
    | ~ v5_orders_3(sK10,sK8,sK9)
    | ~ v1_funct_1(k2_funct_1(sK11))
    | ~ v5_orders_3(sK11,sK9,sK8)
    | ~ v2_funct_1(sK11)
    | v2_struct_0(sK8)
    | v2_struct_0(sK9)
    | v23_waybel_0(sK11,sK9,sK8)
    | ~ spl117_249
    | ~ spl117_443
    | ~ spl117_475 ),
    inference(forward_demodulation,[],[f15139,f12012])).

fof(f12012,plain,
    ( u1_struct_0(sK8) = k2_relat_1(sK11)
    | ~ spl117_475 ),
    inference(avatar_component_clause,[],[f12010])).

fof(f15139,plain,
    ( ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK11),u1_struct_0(sK9))))
    | ~ v5_orders_3(sK10,sK8,sK9)
    | ~ v1_funct_2(k2_funct_1(sK11),u1_struct_0(sK8),u1_struct_0(sK9))
    | ~ v1_funct_1(k2_funct_1(sK11))
    | ~ v5_orders_3(sK11,sK9,sK8)
    | ~ v2_funct_1(sK11)
    | v2_struct_0(sK8)
    | v2_struct_0(sK9)
    | v23_waybel_0(sK11,sK9,sK8)
    | ~ spl117_249
    | ~ spl117_443
    | ~ spl117_475 ),
    inference(forward_demodulation,[],[f15138,f11732])).

fof(f15138,plain,
    ( ~ m1_subset_1(k2_funct_1(sK11),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK11),u1_struct_0(sK9))))
    | ~ v5_orders_3(sK10,sK8,sK9)
    | ~ v1_funct_2(k2_funct_1(sK11),u1_struct_0(sK8),u1_struct_0(sK9))
    | ~ v1_funct_1(k2_funct_1(sK11))
    | ~ v5_orders_3(sK11,sK9,sK8)
    | ~ v2_funct_1(sK11)
    | v2_struct_0(sK8)
    | v2_struct_0(sK9)
    | v23_waybel_0(sK11,sK9,sK8)
    | ~ spl117_249
    | ~ spl117_443
    | ~ spl117_475 ),
    inference(forward_demodulation,[],[f15137,f12012])).

fof(f15137,plain,
    ( ~ v5_orders_3(sK10,sK8,sK9)
    | ~ m1_subset_1(k2_funct_1(sK11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9))))
    | ~ v1_funct_2(k2_funct_1(sK11),u1_struct_0(sK8),u1_struct_0(sK9))
    | ~ v1_funct_1(k2_funct_1(sK11))
    | ~ v5_orders_3(sK11,sK9,sK8)
    | ~ v2_funct_1(sK11)
    | v2_struct_0(sK8)
    | v2_struct_0(sK9)
    | v23_waybel_0(sK11,sK9,sK8)
    | ~ spl117_249
    | ~ spl117_443 ),
    inference(forward_demodulation,[],[f15133,f11732])).

fof(f15133,plain,
    ( ~ v5_orders_3(k2_funct_1(sK11),sK8,sK9)
    | ~ m1_subset_1(k2_funct_1(sK11),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9))))
    | ~ v1_funct_2(k2_funct_1(sK11),u1_struct_0(sK8),u1_struct_0(sK9))
    | ~ v1_funct_1(k2_funct_1(sK11))
    | ~ v5_orders_3(sK11,sK9,sK8)
    | ~ v2_funct_1(sK11)
    | v2_struct_0(sK8)
    | v2_struct_0(sK9)
    | v23_waybel_0(sK11,sK9,sK8)
    | ~ spl117_249 ),
    inference(resolution,[],[f9077,f4224])).

fof(f4224,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | ~ v5_orders_3(k2_funct_1(X2),X1,X0)
      | ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(k2_funct_1(X2))
      | ~ v5_orders_3(X2,X0,X1)
      | ~ v2_funct_1(X2)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | v23_waybel_0(X2,X0,X1) ) ),
    inference(equality_resolution,[],[f3894])).

fof(f3894,plain,(
    ! [X2,X0,X3,X1] :
      ( v23_waybel_0(X2,X0,X1)
      | ~ v5_orders_3(X3,X1,X0)
      | k2_funct_1(X2) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X3)
      | ~ v5_orders_3(X2,X0,X1)
      | ~ v2_funct_1(X2)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f3624])).

fof(f9077,plain,
    ( sP2(sK9,sK8,sK11)
    | ~ spl117_249 ),
    inference(avatar_component_clause,[],[f9075])).

fof(f12097,plain,
    ( spl117_478
    | ~ spl117_8
    | ~ spl117_475 ),
    inference(avatar_split_clause,[],[f12021,f12010,f4338,f12094])).

fof(f4338,plain,
    ( spl117_8
  <=> v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_8])])).

fof(f12021,plain,
    ( v1_funct_2(sK10,k2_relat_1(sK11),u1_struct_0(sK9))
    | ~ spl117_8
    | ~ spl117_475 ),
    inference(backward_demodulation,[],[f4340,f12012])).

fof(f4340,plain,
    ( v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK9))
    | ~ spl117_8 ),
    inference(avatar_component_clause,[],[f4338])).

fof(f12013,plain,
    ( spl117_13
    | ~ spl117_12
    | spl117_11
    | ~ spl117_10
    | ~ spl117_9
    | ~ spl117_8
    | ~ spl117_7
    | spl117_475
    | ~ spl117_2
    | ~ spl117_6 ),
    inference(avatar_split_clause,[],[f12008,f4328,f4308,f12010,f4333,f4338,f4343,f4348,f4353,f4358,f4363])).

fof(f4358,plain,
    ( spl117_12
  <=> l1_orders_2(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_12])])).

fof(f4348,plain,
    ( spl117_10
  <=> l1_orders_2(sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_10])])).

fof(f4333,plain,
    ( spl117_7
  <=> m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_7])])).

fof(f12008,plain,
    ( u1_struct_0(sK8) = k2_relat_1(sK11)
    | ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9))))
    | ~ v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK9))
    | ~ v1_funct_1(sK10)
    | ~ l1_orders_2(sK9)
    | v2_struct_0(sK9)
    | ~ l1_orders_2(sK8)
    | v2_struct_0(sK8)
    | ~ spl117_2
    | ~ spl117_6 ),
    inference(forward_demodulation,[],[f12006,f4310])).

fof(f12006,plain,
    ( u1_struct_0(sK8) = k2_relat_1(k2_funct_1(sK10))
    | ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9))))
    | ~ v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK9))
    | ~ v1_funct_1(sK10)
    | ~ l1_orders_2(sK9)
    | v2_struct_0(sK9)
    | ~ l1_orders_2(sK8)
    | v2_struct_0(sK8)
    | ~ spl117_6 ),
    inference(resolution,[],[f4330,f3886])).

fof(f3886,plain,(
    ! [X2,X0,X1] :
      ( ~ v23_waybel_0(X2,X0,X1)
      | u1_struct_0(X0) = k2_relat_1(k2_funct_1(X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3391])).

fof(f3391,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( u1_struct_0(X0) = k2_relat_1(k2_funct_1(X2))
                & m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(k2_funct_1(X2)) )
              | ~ v23_waybel_0(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3390])).

fof(f3390,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( u1_struct_0(X0) = k2_relat_1(k2_funct_1(X2))
                & m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(k2_funct_1(X2)) )
              | ~ v23_waybel_0(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3297])).

fof(f3297,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_waybel_0)).

fof(f11946,plain,
    ( spl117_469
    | ~ spl117_118
    | ~ spl117_447 ),
    inference(avatar_split_clause,[],[f11905,f11746,f6095,f11943])).

fof(f6095,plain,
    ( spl117_118
  <=> m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK10),u1_struct_0(sK9)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_118])])).

fof(f11746,plain,
    ( spl117_447
  <=> k1_relat_1(sK10) = k2_relat_1(sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_447])])).

fof(f11905,plain,
    ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK11),u1_struct_0(sK9))))
    | ~ spl117_118
    | ~ spl117_447 ),
    inference(backward_demodulation,[],[f6097,f11748])).

fof(f11748,plain,
    ( k1_relat_1(sK10) = k2_relat_1(sK11)
    | ~ spl117_447 ),
    inference(avatar_component_clause,[],[f11746])).

fof(f6097,plain,
    ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK10),u1_struct_0(sK9))))
    | ~ spl117_118 ),
    inference(avatar_component_clause,[],[f6095])).

fof(f11871,plain,
    ( spl117_465
    | ~ spl117_2
    | ~ spl117_403 ),
    inference(avatar_split_clause,[],[f11866,f11493,f4308,f11868])).

fof(f11493,plain,
    ( spl117_403
  <=> v2_funct_1(k2_funct_1(sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_403])])).

fof(f11866,plain,
    ( v2_funct_1(sK11)
    | ~ spl117_2
    | ~ spl117_403 ),
    inference(forward_demodulation,[],[f11495,f4310])).

fof(f11495,plain,
    ( v2_funct_1(k2_funct_1(sK10))
    | ~ spl117_403 ),
    inference(avatar_component_clause,[],[f11493])).

fof(f11863,plain,
    ( spl117_443
    | ~ spl117_2
    | ~ spl117_405 ),
    inference(avatar_split_clause,[],[f11862,f11503,f4308,f11730])).

fof(f11503,plain,
    ( spl117_405
  <=> sK10 = k2_funct_1(k2_funct_1(sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_405])])).

fof(f11862,plain,
    ( sK10 = k2_funct_1(sK11)
    | ~ spl117_2
    | ~ spl117_405 ),
    inference(forward_demodulation,[],[f11505,f4310])).

fof(f11505,plain,
    ( sK10 = k2_funct_1(k2_funct_1(sK10))
    | ~ spl117_405 ),
    inference(avatar_component_clause,[],[f11503])).

fof(f11861,plain,
    ( spl117_447
    | ~ spl117_2
    | ~ spl117_406 ),
    inference(avatar_split_clause,[],[f11860,f11508,f4308,f11746])).

fof(f11508,plain,
    ( spl117_406
  <=> k1_relat_1(sK10) = k2_relat_1(k2_funct_1(sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_406])])).

fof(f11860,plain,
    ( k1_relat_1(sK10) = k2_relat_1(sK11)
    | ~ spl117_2
    | ~ spl117_406 ),
    inference(forward_demodulation,[],[f11510,f4310])).

fof(f11510,plain,
    ( k1_relat_1(sK10) = k2_relat_1(k2_funct_1(sK10))
    | ~ spl117_406 ),
    inference(avatar_component_clause,[],[f11508])).

fof(f11649,plain,
    ( spl117_403
    | ~ spl117_9
    | ~ spl117_26
    | ~ spl117_324 ),
    inference(avatar_split_clause,[],[f10677,f10634,f4514,f4343,f11493])).

fof(f4514,plain,
    ( spl117_26
  <=> v1_relat_1(sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_26])])).

fof(f10634,plain,
    ( spl117_324
  <=> v2_funct_1(sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_324])])).

fof(f10677,plain,
    ( v2_funct_1(k2_funct_1(sK10))
    | ~ spl117_9
    | ~ spl117_26
    | ~ spl117_324 ),
    inference(unit_resulting_resolution,[],[f4515,f4345,f10636,f3863])).

fof(f3863,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | v2_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f3379])).

fof(f3379,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f3378])).

fof(f3378,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1033])).

fof(f1033,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => v2_funct_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_1)).

fof(f10636,plain,
    ( v2_funct_1(sK10)
    | ~ spl117_324 ),
    inference(avatar_component_clause,[],[f10634])).

fof(f4345,plain,
    ( v1_funct_1(sK10)
    | ~ spl117_9 ),
    inference(avatar_component_clause,[],[f4343])).

fof(f4515,plain,
    ( v1_relat_1(sK10)
    | ~ spl117_26 ),
    inference(avatar_component_clause,[],[f4514])).

fof(f11647,plain,
    ( spl117_405
    | ~ spl117_9
    | ~ spl117_26
    | ~ spl117_324 ),
    inference(avatar_split_clause,[],[f10675,f10634,f4514,f4343,f11503])).

fof(f10675,plain,
    ( sK10 = k2_funct_1(k2_funct_1(sK10))
    | ~ spl117_9
    | ~ spl117_26
    | ~ spl117_324 ),
    inference(unit_resulting_resolution,[],[f4515,f4345,f10636,f3861])).

fof(f3861,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f3375])).

fof(f3375,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f3374])).

fof(f3374,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1036])).

fof(f1036,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

fof(f11646,plain,
    ( spl117_406
    | ~ spl117_9
    | ~ spl117_26
    | ~ spl117_324 ),
    inference(avatar_split_clause,[],[f10674,f10634,f4514,f4343,f11508])).

fof(f10674,plain,
    ( k1_relat_1(sK10) = k2_relat_1(k2_funct_1(sK10))
    | ~ spl117_9
    | ~ spl117_26
    | ~ spl117_324 ),
    inference(unit_resulting_resolution,[],[f4515,f4345,f10636,f3860])).

fof(f3860,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f3373])).

fof(f3373,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f3372])).

fof(f3372,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1026])).

fof(f1026,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f11460,plain,
    ( spl117_13
    | ~ spl117_12
    | spl117_11
    | ~ spl117_10
    | ~ spl117_7
    | ~ spl117_9
    | ~ spl117_8
    | spl117_324
    | ~ spl117_6 ),
    inference(avatar_split_clause,[],[f10629,f4328,f10634,f4338,f4343,f4333,f4348,f4353,f4358,f4363])).

fof(f10629,plain,
    ( v2_funct_1(sK10)
    | ~ v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK9))
    | ~ v1_funct_1(sK10)
    | ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9))))
    | ~ l1_orders_2(sK9)
    | v2_struct_0(sK9)
    | ~ l1_orders_2(sK8)
    | v2_struct_0(sK8)
    | ~ spl117_6 ),
    inference(resolution,[],[f3872,f4330])).

fof(f3872,plain,(
    ! [X2,X0,X1] :
      ( ~ v23_waybel_0(X2,X0,X1)
      | v2_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3387])).

fof(f3387,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v5_orders_3(X2,X0,X1)
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
            & v2_funct_1(X2)
            & v1_funct_1(X2) )
          | ~ v23_waybel_0(X2,X0,X1)
          | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) )
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3386])).

fof(f3386,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v5_orders_3(X2,X0,X1)
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
            & v2_funct_1(X2)
            & v1_funct_1(X2) )
          | ~ v23_waybel_0(X2,X0,X1)
          | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) )
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3155])).

fof(f3155,axiom,(
    ! [X0,X1] :
      ( ( l1_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
         => ( ( v23_waybel_0(X2,X0,X1)
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
           => ( v5_orders_3(X2,X0,X1)
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v2_funct_1(X2)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc9_waybel_0)).

fof(f9083,plain,
    ( spl117_250
    | ~ spl117_7
    | ~ spl117_8
    | ~ spl117_9
    | ~ spl117_10
    | ~ spl117_12 ),
    inference(avatar_split_clause,[],[f9069,f4358,f4348,f4343,f4338,f4333,f9080])).

fof(f9069,plain,
    ( sP2(sK8,sK9,sK10)
    | ~ spl117_7
    | ~ spl117_8
    | ~ spl117_9
    | ~ spl117_10
    | ~ spl117_12 ),
    inference(unit_resulting_resolution,[],[f4360,f4350,f4345,f4340,f4335,f3895])).

fof(f3895,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | sP2(X0,X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3626])).

fof(f3626,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( ( v23_waybel_0(X2,X0,X1)
                      | ~ v2_struct_0(X1)
                      | ~ v2_struct_0(X0) )
                    & ( ( v2_struct_0(X1)
                        & v2_struct_0(X0) )
                      | ~ v23_waybel_0(X2,X0,X1) ) )
                  | ( ~ v2_struct_0(X1)
                    & ~ v2_struct_0(X0) ) )
                & sP2(X0,X1,X2) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f3625])).

fof(f3625,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( ( v23_waybel_0(X2,X0,X1)
                      | ~ v2_struct_0(X1)
                      | ~ v2_struct_0(X0) )
                    & ( ( v2_struct_0(X1)
                        & v2_struct_0(X0) )
                      | ~ v23_waybel_0(X2,X0,X1) ) )
                  | ( ~ v2_struct_0(X1)
                    & ~ v2_struct_0(X0) ) )
                & sP2(X0,X1,X2) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f3559])).

fof(f3559,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( v23_waybel_0(X2,X0,X1)
                  <=> ( v2_struct_0(X1)
                      & v2_struct_0(X0) ) )
                  | ( ~ v2_struct_0(X1)
                    & ~ v2_struct_0(X0) ) )
                & sP2(X0,X1,X2) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f3393,f3558])).

fof(f3393,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( v23_waybel_0(X2,X0,X1)
                  <=> ( v2_struct_0(X1)
                      & v2_struct_0(X0) ) )
                  | ( ~ v2_struct_0(X1)
                    & ~ v2_struct_0(X0) ) )
                & ( ( v23_waybel_0(X2,X0,X1)
                  <=> ( ? [X3] :
                          ( v5_orders_3(X3,X1,X0)
                          & k2_funct_1(X2) = X3
                          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                          & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                          & v1_funct_1(X3) )
                      & v5_orders_3(X2,X0,X1)
                      & v2_funct_1(X2) ) )
                  | v2_struct_0(X1)
                  | v2_struct_0(X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f3392])).

fof(f3392,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( v23_waybel_0(X2,X0,X1)
                  <=> ( v2_struct_0(X1)
                      & v2_struct_0(X0) ) )
                  | ( ~ v2_struct_0(X1)
                    & ~ v2_struct_0(X0) ) )
                & ( ( v23_waybel_0(X2,X0,X1)
                  <=> ( ? [X3] :
                          ( v5_orders_3(X3,X1,X0)
                          & k2_funct_1(X2) = X3
                          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                          & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                          & v1_funct_1(X3) )
                      & v5_orders_3(X2,X0,X1)
                      & v2_funct_1(X2) ) )
                  | v2_struct_0(X1)
                  | v2_struct_0(X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3175])).

fof(f3175,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( ~ ( ~ v2_struct_0(X1)
                      & ~ v2_struct_0(X0) )
                 => ( v23_waybel_0(X2,X0,X1)
                  <=> ( v2_struct_0(X1)
                      & v2_struct_0(X0) ) ) )
                & ~ ( ~ ( v23_waybel_0(X2,X0,X1)
                      <=> ( ? [X3] :
                              ( v5_orders_3(X3,X1,X0)
                              & k2_funct_1(X2) = X3
                              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                              & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                              & v1_funct_1(X3) )
                          & v5_orders_3(X2,X0,X1)
                          & v2_funct_1(X2) ) )
                    & ~ v2_struct_0(X1)
                    & ~ v2_struct_0(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d38_waybel_0)).

fof(f4335,plain,
    ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9))))
    | ~ spl117_7 ),
    inference(avatar_component_clause,[],[f4333])).

fof(f4350,plain,
    ( l1_orders_2(sK9)
    | ~ spl117_10 ),
    inference(avatar_component_clause,[],[f4348])).

fof(f4360,plain,
    ( l1_orders_2(sK8)
    | ~ spl117_12 ),
    inference(avatar_component_clause,[],[f4358])).

fof(f9078,plain,
    ( spl117_249
    | ~ spl117_3
    | ~ spl117_4
    | ~ spl117_5
    | ~ spl117_10
    | ~ spl117_12 ),
    inference(avatar_split_clause,[],[f9070,f4358,f4348,f4323,f4318,f4313,f9075])).

fof(f4313,plain,
    ( spl117_3
  <=> m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK8)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_3])])).

fof(f4318,plain,
    ( spl117_4
  <=> v1_funct_2(sK11,u1_struct_0(sK9),u1_struct_0(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_4])])).

fof(f4323,plain,
    ( spl117_5
  <=> v1_funct_1(sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_5])])).

fof(f9070,plain,
    ( sP2(sK9,sK8,sK11)
    | ~ spl117_3
    | ~ spl117_4
    | ~ spl117_5
    | ~ spl117_10
    | ~ spl117_12 ),
    inference(unit_resulting_resolution,[],[f4350,f4360,f4325,f4320,f4315,f3895])).

fof(f4315,plain,
    ( m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK8))))
    | ~ spl117_3 ),
    inference(avatar_component_clause,[],[f4313])).

fof(f4320,plain,
    ( v1_funct_2(sK11,u1_struct_0(sK9),u1_struct_0(sK8))
    | ~ spl117_4 ),
    inference(avatar_component_clause,[],[f4318])).

fof(f4325,plain,
    ( v1_funct_1(sK11)
    | ~ spl117_5 ),
    inference(avatar_component_clause,[],[f4323])).

fof(f6098,plain,
    ( spl117_118
    | ~ spl117_68 ),
    inference(avatar_split_clause,[],[f6090,f5008,f6095])).

fof(f5008,plain,
    ( spl117_68
  <=> sP109(sK10,u1_struct_0(sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl117_68])])).

fof(f6090,plain,
    ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK10),u1_struct_0(sK9))))
    | ~ spl117_68 ),
    inference(unit_resulting_resolution,[],[f5010,f4212,f4283])).

fof(f4283,plain,(
    ! [X2,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ sP109(X3,X2) ) ),
    inference(general_splitting,[],[f3987,f4282_D])).

fof(f4282,plain,(
    ! [X2,X0,X3] :
      ( sP109(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f4282_D])).

fof(f4282_D,plain,(
    ! [X2,X3] :
      ( ! [X0] : ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
    <=> ~ sP109(X3,X2) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP109])])).

fof(f3987,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f3450])).

fof(f3450,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f3449])).

fof(f3449,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f1241])).

fof(f1241,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).

fof(f4212,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f3791])).

fof(f3791,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3580])).

fof(f3580,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f3579])).

fof(f3579,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f5010,plain,
    ( sP109(sK10,u1_struct_0(sK9))
    | ~ spl117_68 ),
    inference(avatar_component_clause,[],[f5008])).

fof(f5011,plain,
    ( spl117_68
    | ~ spl117_7 ),
    inference(avatar_split_clause,[],[f4999,f4333,f5008])).

fof(f4999,plain,
    ( sP109(sK10,u1_struct_0(sK9))
    | ~ spl117_7 ),
    inference(unit_resulting_resolution,[],[f4335,f4282])).

fof(f4705,plain,
    ( spl117_26
    | ~ spl117_7 ),
    inference(avatar_split_clause,[],[f4698,f4333,f4514])).

fof(f4698,plain,
    ( v1_relat_1(sK10)
    | ~ spl117_7 ),
    inference(unit_resulting_resolution,[],[f4335,f3906])).

fof(f3906,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f3401])).

fof(f3401,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1210])).

fof(f1210,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f4366,plain,(
    ~ spl117_13 ),
    inference(avatar_split_clause,[],[f3763,f4363])).

fof(f3763,plain,(
    ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f3572])).

fof(f3572,plain,
    ( ~ v23_waybel_0(sK11,sK9,sK8)
    & k2_funct_1(sK10) = sK11
    & m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK8))))
    & v1_funct_2(sK11,u1_struct_0(sK9),u1_struct_0(sK8))
    & v1_funct_1(sK11)
    & v23_waybel_0(sK10,sK8,sK9)
    & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9))))
    & v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK9))
    & v1_funct_1(sK10)
    & l1_orders_2(sK9)
    & ~ v2_struct_0(sK9)
    & l1_orders_2(sK8)
    & ~ v2_struct_0(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10,sK11])],[f3311,f3571,f3570,f3569,f3568])).

fof(f3568,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ v23_waybel_0(X3,X1,X0)
                    & k2_funct_1(X2) = X3
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                    & v1_funct_1(X3) )
                & v23_waybel_0(X2,X0,X1)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_orders_2(X1)
            & ~ v2_struct_0(X1) )
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v23_waybel_0(X3,X1,sK8)
                  & k2_funct_1(X2) = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK8))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK8))
                  & v1_funct_1(X3) )
              & v23_waybel_0(X2,sK8,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK8),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(sK8)
      & ~ v2_struct_0(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f3569,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ v23_waybel_0(X3,X1,sK8)
                & k2_funct_1(X2) = X3
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK8))))
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK8))
                & v1_funct_1(X3) )
            & v23_waybel_0(X2,sK8,X1)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK8),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_orders_2(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ v23_waybel_0(X3,sK9,sK8)
              & k2_funct_1(X2) = X3
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK8))))
              & v1_funct_2(X3,u1_struct_0(sK9),u1_struct_0(sK8))
              & v1_funct_1(X3) )
          & v23_waybel_0(X2,sK8,sK9)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9))))
          & v1_funct_2(X2,u1_struct_0(sK8),u1_struct_0(sK9))
          & v1_funct_1(X2) )
      & l1_orders_2(sK9)
      & ~ v2_struct_0(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f3570,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ v23_waybel_0(X3,sK9,sK8)
            & k2_funct_1(X2) = X3
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK8))))
            & v1_funct_2(X3,u1_struct_0(sK9),u1_struct_0(sK8))
            & v1_funct_1(X3) )
        & v23_waybel_0(X2,sK8,sK9)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9))))
        & v1_funct_2(X2,u1_struct_0(sK8),u1_struct_0(sK9))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ v23_waybel_0(X3,sK9,sK8)
          & k2_funct_1(sK10) = X3
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK8))))
          & v1_funct_2(X3,u1_struct_0(sK9),u1_struct_0(sK8))
          & v1_funct_1(X3) )
      & v23_waybel_0(sK10,sK8,sK9)
      & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9))))
      & v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK9))
      & v1_funct_1(sK10) ) ),
    introduced(choice_axiom,[])).

fof(f3571,plain,
    ( ? [X3] :
        ( ~ v23_waybel_0(X3,sK9,sK8)
        & k2_funct_1(sK10) = X3
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK8))))
        & v1_funct_2(X3,u1_struct_0(sK9),u1_struct_0(sK8))
        & v1_funct_1(X3) )
   => ( ~ v23_waybel_0(sK11,sK9,sK8)
      & k2_funct_1(sK10) = sK11
      & m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK8))))
      & v1_funct_2(sK11,u1_struct_0(sK9),u1_struct_0(sK8))
      & v1_funct_1(sK11) ) ),
    introduced(choice_axiom,[])).

fof(f3311,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v23_waybel_0(X3,X1,X0)
                  & k2_funct_1(X2) = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & v23_waybel_0(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3310])).

fof(f3310,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v23_waybel_0(X3,X1,X0)
                  & k2_funct_1(X2) = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & v23_waybel_0(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3299])).

fof(f3299,negated_conjecture,(
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
                 => ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                        & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                        & v1_funct_1(X3) )
                     => ( k2_funct_1(X2) = X3
                       => v23_waybel_0(X3,X1,X0) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3298])).

fof(f3298,conjecture,(
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
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                      & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                      & v1_funct_1(X3) )
                   => ( k2_funct_1(X2) = X3
                     => v23_waybel_0(X3,X1,X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_waybel_0)).

fof(f4361,plain,(
    spl117_12 ),
    inference(avatar_split_clause,[],[f3764,f4358])).

fof(f3764,plain,(
    l1_orders_2(sK8) ),
    inference(cnf_transformation,[],[f3572])).

fof(f4356,plain,(
    ~ spl117_11 ),
    inference(avatar_split_clause,[],[f3765,f4353])).

fof(f3765,plain,(
    ~ v2_struct_0(sK9) ),
    inference(cnf_transformation,[],[f3572])).

fof(f4351,plain,(
    spl117_10 ),
    inference(avatar_split_clause,[],[f3766,f4348])).

fof(f3766,plain,(
    l1_orders_2(sK9) ),
    inference(cnf_transformation,[],[f3572])).

fof(f4346,plain,(
    spl117_9 ),
    inference(avatar_split_clause,[],[f3767,f4343])).

fof(f3767,plain,(
    v1_funct_1(sK10) ),
    inference(cnf_transformation,[],[f3572])).

fof(f4341,plain,(
    spl117_8 ),
    inference(avatar_split_clause,[],[f3768,f4338])).

fof(f3768,plain,(
    v1_funct_2(sK10,u1_struct_0(sK8),u1_struct_0(sK9)) ),
    inference(cnf_transformation,[],[f3572])).

fof(f4336,plain,(
    spl117_7 ),
    inference(avatar_split_clause,[],[f3769,f4333])).

fof(f3769,plain,(
    m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK9)))) ),
    inference(cnf_transformation,[],[f3572])).

fof(f4331,plain,(
    spl117_6 ),
    inference(avatar_split_clause,[],[f3770,f4328])).

fof(f3770,plain,(
    v23_waybel_0(sK10,sK8,sK9) ),
    inference(cnf_transformation,[],[f3572])).

fof(f4326,plain,(
    spl117_5 ),
    inference(avatar_split_clause,[],[f3771,f4323])).

fof(f3771,plain,(
    v1_funct_1(sK11) ),
    inference(cnf_transformation,[],[f3572])).

fof(f4321,plain,(
    spl117_4 ),
    inference(avatar_split_clause,[],[f3772,f4318])).

fof(f3772,plain,(
    v1_funct_2(sK11,u1_struct_0(sK9),u1_struct_0(sK8)) ),
    inference(cnf_transformation,[],[f3572])).

fof(f4316,plain,(
    spl117_3 ),
    inference(avatar_split_clause,[],[f3773,f4313])).

fof(f3773,plain,(
    m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK9),u1_struct_0(sK8)))) ),
    inference(cnf_transformation,[],[f3572])).

fof(f4311,plain,(
    spl117_2 ),
    inference(avatar_split_clause,[],[f3774,f4308])).

fof(f3774,plain,(
    k2_funct_1(sK10) = sK11 ),
    inference(cnf_transformation,[],[f3572])).

fof(f4306,plain,(
    ~ spl117_1 ),
    inference(avatar_split_clause,[],[f3775,f4303])).

fof(f3775,plain,(
    ~ v23_waybel_0(sK11,sK9,sK8) ),
    inference(cnf_transformation,[],[f3572])).
%------------------------------------------------------------------------------
