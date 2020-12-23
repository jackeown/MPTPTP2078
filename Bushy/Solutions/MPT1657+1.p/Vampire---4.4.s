%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_0__t37_waybel_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:49 EDT 2019

% Result     : Theorem 50.73s
% Output     : Refutation 50.73s
% Verified   : 
% Statistics : Number of formulae       :  178 ( 448 expanded)
%              Number of leaves         :   32 ( 198 expanded)
%              Depth                    :   14
%              Number of atoms          : 1076 (2393 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f24247,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f339,f346,f353,f360,f517,f627,f4375,f5011,f5088,f5381,f5544,f6424,f6516,f10035,f10482,f10686,f15872,f18867,f19013,f20899,f20909,f22337,f23197,f24220,f24239,f24246])).

fof(f24246,plain,
    ( spl23_1
    | ~ spl23_6
    | spl23_103
    | ~ spl23_104
    | ~ spl23_806
    | spl23_3519 ),
    inference(avatar_contradiction_clause,[],[f24245])).

fof(f24245,plain,
    ( $false
    | ~ spl23_1
    | ~ spl23_6
    | ~ spl23_103
    | ~ spl23_104
    | ~ spl23_806
    | ~ spl23_3519 ),
    inference(subsumption_resolution,[],[f24244,f338])).

fof(f338,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl23_1 ),
    inference(avatar_component_clause,[],[f337])).

fof(f337,plain,
    ( spl23_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_1])])).

fof(f24244,plain,
    ( v2_struct_0(sK0)
    | ~ spl23_6
    | ~ spl23_103
    | ~ spl23_104
    | ~ spl23_806
    | ~ spl23_3519 ),
    inference(subsumption_resolution,[],[f24243,f359])).

fof(f359,plain,
    ( l1_orders_2(sK0)
    | ~ spl23_6 ),
    inference(avatar_component_clause,[],[f358])).

fof(f358,plain,
    ( spl23_6
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_6])])).

fof(f24243,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl23_103
    | ~ spl23_104
    | ~ spl23_806
    | ~ spl23_3519 ),
    inference(subsumption_resolution,[],[f24242,f617])).

fof(f617,plain,
    ( ~ r2_yellow_0(sK0,sK1)
    | ~ spl23_103 ),
    inference(avatar_component_clause,[],[f616])).

fof(f616,plain,
    ( spl23_103
  <=> ~ r2_yellow_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_103])])).

fof(f24242,plain,
    ( r2_yellow_0(sK0,sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl23_104
    | ~ spl23_806
    | ~ spl23_3519 ),
    inference(subsumption_resolution,[],[f24240,f626])).

fof(f626,plain,
    ( r2_yellow_0(sK0,k4_waybel_0(sK0,sK1))
    | ~ spl23_104 ),
    inference(avatar_component_clause,[],[f625])).

fof(f625,plain,
    ( spl23_104
  <=> r2_yellow_0(sK0,k4_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_104])])).

fof(f24240,plain,
    ( ~ r2_yellow_0(sK0,k4_waybel_0(sK0,sK1))
    | r2_yellow_0(sK0,sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl23_806
    | ~ spl23_3519 ),
    inference(resolution,[],[f24238,f4374])).

fof(f4374,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0))
        | ~ r2_yellow_0(X0,X1)
        | r2_yellow_0(X0,X2)
        | ~ l1_orders_2(X0)
        | v2_struct_0(X0) )
    | ~ spl23_806 ),
    inference(avatar_component_clause,[],[f4373])).

fof(f4373,plain,
    ( spl23_806
  <=> ! [X1,X0,X2] :
        ( r2_yellow_0(X0,X2)
        | ~ r2_yellow_0(X0,X1)
        | m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0))
        | ~ l1_orders_2(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_806])])).

fof(f24238,plain,
    ( ~ m1_subset_1(sK9(sK0,k4_waybel_0(sK0,sK1),sK1),u1_struct_0(sK0))
    | ~ spl23_3519 ),
    inference(avatar_component_clause,[],[f24237])).

fof(f24237,plain,
    ( spl23_3519
  <=> ~ m1_subset_1(sK9(sK0,k4_waybel_0(sK0,sK1),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_3519])])).

fof(f24239,plain,
    ( ~ spl23_3519
    | spl23_1
    | ~ spl23_2
    | ~ spl23_4
    | ~ spl23_6
    | ~ spl23_56
    | spl23_103
    | ~ spl23_104
    | ~ spl23_932
    | ~ spl23_992
    | ~ spl23_3516 ),
    inference(avatar_split_clause,[],[f24232,f24218,f5379,f5086,f625,f616,f515,f358,f351,f344,f337,f24237])).

fof(f344,plain,
    ( spl23_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_2])])).

fof(f351,plain,
    ( spl23_4
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_4])])).

fof(f515,plain,
    ( spl23_56
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_56])])).

fof(f5086,plain,
    ( spl23_932
  <=> ! [X1,X0,X2] :
        ( r2_yellow_0(X0,X2)
        | ~ r2_yellow_0(X0,X1)
        | ~ r1_lattice3(X0,X2,sK9(X0,X1,X2))
        | ~ r1_lattice3(X0,X1,sK9(X0,X1,X2))
        | ~ l1_orders_2(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_932])])).

fof(f5379,plain,
    ( spl23_992
  <=> ! [X1,X0,X2] :
        ( r1_lattice3(X0,k4_waybel_0(X0,X1),X2)
        | ~ r1_lattice3(X0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_992])])).

fof(f24218,plain,
    ( spl23_3516
  <=> r1_lattice3(sK0,sK1,sK9(sK0,k4_waybel_0(sK0,sK1),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_3516])])).

fof(f24232,plain,
    ( ~ m1_subset_1(sK9(sK0,k4_waybel_0(sK0,sK1),sK1),u1_struct_0(sK0))
    | ~ spl23_1
    | ~ spl23_2
    | ~ spl23_4
    | ~ spl23_6
    | ~ spl23_56
    | ~ spl23_103
    | ~ spl23_104
    | ~ spl23_932
    | ~ spl23_992
    | ~ spl23_3516 ),
    inference(subsumption_resolution,[],[f24231,f338])).

fof(f24231,plain,
    ( ~ m1_subset_1(sK9(sK0,k4_waybel_0(sK0,sK1),sK1),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl23_1
    | ~ spl23_2
    | ~ spl23_4
    | ~ spl23_6
    | ~ spl23_56
    | ~ spl23_103
    | ~ spl23_104
    | ~ spl23_932
    | ~ spl23_992
    | ~ spl23_3516 ),
    inference(subsumption_resolution,[],[f24230,f345])).

fof(f345,plain,
    ( v3_orders_2(sK0)
    | ~ spl23_2 ),
    inference(avatar_component_clause,[],[f344])).

fof(f24230,plain,
    ( ~ m1_subset_1(sK9(sK0,k4_waybel_0(sK0,sK1),sK1),u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl23_1
    | ~ spl23_4
    | ~ spl23_6
    | ~ spl23_56
    | ~ spl23_103
    | ~ spl23_104
    | ~ spl23_932
    | ~ spl23_992
    | ~ spl23_3516 ),
    inference(subsumption_resolution,[],[f24229,f352])).

fof(f352,plain,
    ( v4_orders_2(sK0)
    | ~ spl23_4 ),
    inference(avatar_component_clause,[],[f351])).

fof(f24229,plain,
    ( ~ m1_subset_1(sK9(sK0,k4_waybel_0(sK0,sK1),sK1),u1_struct_0(sK0))
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl23_1
    | ~ spl23_6
    | ~ spl23_56
    | ~ spl23_103
    | ~ spl23_104
    | ~ spl23_932
    | ~ spl23_992
    | ~ spl23_3516 ),
    inference(subsumption_resolution,[],[f24228,f359])).

fof(f24228,plain,
    ( ~ m1_subset_1(sK9(sK0,k4_waybel_0(sK0,sK1),sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl23_1
    | ~ spl23_6
    | ~ spl23_56
    | ~ spl23_103
    | ~ spl23_104
    | ~ spl23_932
    | ~ spl23_992
    | ~ spl23_3516 ),
    inference(subsumption_resolution,[],[f24227,f516])).

fof(f516,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl23_56 ),
    inference(avatar_component_clause,[],[f515])).

fof(f24227,plain,
    ( ~ m1_subset_1(sK9(sK0,k4_waybel_0(sK0,sK1),sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl23_1
    | ~ spl23_6
    | ~ spl23_103
    | ~ spl23_104
    | ~ spl23_932
    | ~ spl23_992
    | ~ spl23_3516 ),
    inference(subsumption_resolution,[],[f24222,f24226])).

fof(f24226,plain,
    ( ~ r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK9(sK0,k4_waybel_0(sK0,sK1),sK1))
    | ~ spl23_1
    | ~ spl23_6
    | ~ spl23_103
    | ~ spl23_104
    | ~ spl23_932
    | ~ spl23_3516 ),
    inference(subsumption_resolution,[],[f24225,f338])).

fof(f24225,plain,
    ( ~ r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK9(sK0,k4_waybel_0(sK0,sK1),sK1))
    | v2_struct_0(sK0)
    | ~ spl23_6
    | ~ spl23_103
    | ~ spl23_104
    | ~ spl23_932
    | ~ spl23_3516 ),
    inference(subsumption_resolution,[],[f24224,f359])).

fof(f24224,plain,
    ( ~ r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK9(sK0,k4_waybel_0(sK0,sK1),sK1))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl23_103
    | ~ spl23_104
    | ~ spl23_932
    | ~ spl23_3516 ),
    inference(subsumption_resolution,[],[f24223,f617])).

fof(f24223,plain,
    ( r2_yellow_0(sK0,sK1)
    | ~ r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK9(sK0,k4_waybel_0(sK0,sK1),sK1))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl23_104
    | ~ spl23_932
    | ~ spl23_3516 ),
    inference(subsumption_resolution,[],[f24221,f626])).

fof(f24221,plain,
    ( ~ r2_yellow_0(sK0,k4_waybel_0(sK0,sK1))
    | r2_yellow_0(sK0,sK1)
    | ~ r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK9(sK0,k4_waybel_0(sK0,sK1),sK1))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl23_932
    | ~ spl23_3516 ),
    inference(resolution,[],[f24219,f5087])).

fof(f5087,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_lattice3(X0,X2,sK9(X0,X1,X2))
        | ~ r2_yellow_0(X0,X1)
        | r2_yellow_0(X0,X2)
        | ~ r1_lattice3(X0,X1,sK9(X0,X1,X2))
        | ~ l1_orders_2(X0)
        | v2_struct_0(X0) )
    | ~ spl23_932 ),
    inference(avatar_component_clause,[],[f5086])).

fof(f24219,plain,
    ( r1_lattice3(sK0,sK1,sK9(sK0,k4_waybel_0(sK0,sK1),sK1))
    | ~ spl23_3516 ),
    inference(avatar_component_clause,[],[f24218])).

fof(f24222,plain,
    ( r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK9(sK0,k4_waybel_0(sK0,sK1),sK1))
    | ~ m1_subset_1(sK9(sK0,k4_waybel_0(sK0,sK1),sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl23_992
    | ~ spl23_3516 ),
    inference(resolution,[],[f24219,f5380])).

fof(f5380,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_lattice3(X0,X1,X2)
        | r1_lattice3(X0,k4_waybel_0(X0,X1),X2)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0)
        | v2_struct_0(X0) )
    | ~ spl23_992 ),
    inference(avatar_component_clause,[],[f5379])).

fof(f24220,plain,
    ( spl23_3516
    | spl23_103
    | ~ spl23_3198 ),
    inference(avatar_split_clause,[],[f24213,f22335,f616,f24218])).

fof(f22335,plain,
    ( spl23_3198
  <=> ! [X0] :
        ( r2_yellow_0(sK0,X0)
        | r1_lattice3(sK0,X0,sK9(sK0,k4_waybel_0(sK0,sK1),X0))
        | r1_lattice3(sK0,sK1,sK9(sK0,k4_waybel_0(sK0,sK1),X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_3198])])).

fof(f24213,plain,
    ( r1_lattice3(sK0,sK1,sK9(sK0,k4_waybel_0(sK0,sK1),sK1))
    | ~ spl23_103
    | ~ spl23_3198 ),
    inference(subsumption_resolution,[],[f24200,f617])).

fof(f24200,plain,
    ( r1_lattice3(sK0,sK1,sK9(sK0,k4_waybel_0(sK0,sK1),sK1))
    | r2_yellow_0(sK0,sK1)
    | ~ spl23_3198 ),
    inference(factoring,[],[f22336])).

fof(f22336,plain,
    ( ! [X0] :
        ( r1_lattice3(sK0,X0,sK9(sK0,k4_waybel_0(sK0,sK1),X0))
        | r1_lattice3(sK0,sK1,sK9(sK0,k4_waybel_0(sK0,sK1),X0))
        | r2_yellow_0(sK0,X0) )
    | ~ spl23_3198 ),
    inference(avatar_component_clause,[],[f22335])).

fof(f23197,plain,
    ( ~ spl23_103
    | spl23_1
    | ~ spl23_6
    | ~ spl23_932
    | ~ spl23_2808
    | ~ spl23_3016 ),
    inference(avatar_split_clause,[],[f23195,f20897,f19011,f5086,f358,f337,f616])).

fof(f19011,plain,
    ( spl23_2808
  <=> r1_lattice3(sK0,sK1,sK9(sK0,sK1,k4_waybel_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_2808])])).

fof(f20897,plain,
    ( spl23_3016
  <=> r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK9(sK0,sK1,k4_waybel_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_3016])])).

fof(f23195,plain,
    ( ~ r2_yellow_0(sK0,sK1)
    | ~ spl23_1
    | ~ spl23_6
    | ~ spl23_932
    | ~ spl23_2808
    | ~ spl23_3016 ),
    inference(subsumption_resolution,[],[f229,f23194])).

fof(f23194,plain,
    ( ~ r2_yellow_0(sK0,sK1)
    | r2_yellow_0(sK0,k4_waybel_0(sK0,sK1))
    | ~ spl23_1
    | ~ spl23_6
    | ~ spl23_932
    | ~ spl23_2808
    | ~ spl23_3016 ),
    inference(subsumption_resolution,[],[f23193,f338])).

fof(f23193,plain,
    ( ~ r2_yellow_0(sK0,sK1)
    | r2_yellow_0(sK0,k4_waybel_0(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ spl23_6
    | ~ spl23_932
    | ~ spl23_2808
    | ~ spl23_3016 ),
    inference(subsumption_resolution,[],[f23192,f359])).

fof(f23192,plain,
    ( ~ r2_yellow_0(sK0,sK1)
    | r2_yellow_0(sK0,k4_waybel_0(sK0,sK1))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl23_932
    | ~ spl23_2808
    | ~ spl23_3016 ),
    inference(subsumption_resolution,[],[f23179,f19012])).

fof(f19012,plain,
    ( r1_lattice3(sK0,sK1,sK9(sK0,sK1,k4_waybel_0(sK0,sK1)))
    | ~ spl23_2808 ),
    inference(avatar_component_clause,[],[f19011])).

fof(f23179,plain,
    ( ~ r2_yellow_0(sK0,sK1)
    | r2_yellow_0(sK0,k4_waybel_0(sK0,sK1))
    | ~ r1_lattice3(sK0,sK1,sK9(sK0,sK1,k4_waybel_0(sK0,sK1)))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl23_932
    | ~ spl23_3016 ),
    inference(resolution,[],[f20898,f5087])).

fof(f20898,plain,
    ( r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK9(sK0,sK1,k4_waybel_0(sK0,sK1)))
    | ~ spl23_3016 ),
    inference(avatar_component_clause,[],[f20897])).

fof(f229,plain,
    ( ~ r2_yellow_0(sK0,k4_waybel_0(sK0,sK1))
    | ~ r2_yellow_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f177])).

fof(f177,plain,
    ( ( ~ r2_yellow_0(sK0,k4_waybel_0(sK0,sK1))
      | ~ r2_yellow_0(sK0,sK1) )
    & ( r2_yellow_0(sK0,k4_waybel_0(sK0,sK1))
      | r2_yellow_0(sK0,sK1) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f174,f176,f175])).

fof(f175,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r2_yellow_0(X0,k4_waybel_0(X0,X1))
              | ~ r2_yellow_0(X0,X1) )
            & ( r2_yellow_0(X0,k4_waybel_0(X0,X1))
              | r2_yellow_0(X0,X1) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ r2_yellow_0(sK0,k4_waybel_0(sK0,X1))
            | ~ r2_yellow_0(sK0,X1) )
          & ( r2_yellow_0(sK0,k4_waybel_0(sK0,X1))
            | r2_yellow_0(sK0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f176,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ r2_yellow_0(X0,k4_waybel_0(X0,X1))
            | ~ r2_yellow_0(X0,X1) )
          & ( r2_yellow_0(X0,k4_waybel_0(X0,X1))
            | r2_yellow_0(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ r2_yellow_0(X0,k4_waybel_0(X0,sK1))
          | ~ r2_yellow_0(X0,sK1) )
        & ( r2_yellow_0(X0,k4_waybel_0(X0,sK1))
          | r2_yellow_0(X0,sK1) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f174,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r2_yellow_0(X0,k4_waybel_0(X0,X1))
            | ~ r2_yellow_0(X0,X1) )
          & ( r2_yellow_0(X0,k4_waybel_0(X0,X1))
            | r2_yellow_0(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f173])).

fof(f173,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r2_yellow_0(X0,k4_waybel_0(X0,X1))
            | ~ r2_yellow_0(X0,X1) )
          & ( r2_yellow_0(X0,k4_waybel_0(X0,X1))
            | r2_yellow_0(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f89])).

fof(f89,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_yellow_0(X0,X1)
          <~> r2_yellow_0(X0,k4_waybel_0(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f88])).

fof(f88,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_yellow_0(X0,X1)
          <~> r2_yellow_0(X0,k4_waybel_0(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( r2_yellow_0(X0,X1)
            <=> r2_yellow_0(X0,k4_waybel_0(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_yellow_0(X0,X1)
          <=> r2_yellow_0(X0,k4_waybel_0(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t37_waybel_0.p',t37_waybel_0)).

fof(f22337,plain,
    ( ~ spl23_105
    | spl23_3198
    | spl23_1
    | ~ spl23_6
    | ~ spl23_806
    | ~ spl23_1748 ),
    inference(avatar_split_clause,[],[f21647,f10480,f4373,f358,f337,f22335,f622])).

fof(f622,plain,
    ( spl23_105
  <=> ~ r2_yellow_0(sK0,k4_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_105])])).

fof(f10480,plain,
    ( spl23_1748
  <=> ! [X0] :
        ( r1_lattice3(sK0,X0,sK9(sK0,k4_waybel_0(sK0,sK1),X0))
        | r2_yellow_0(sK0,X0)
        | r1_lattice3(sK0,sK1,sK9(sK0,k4_waybel_0(sK0,sK1),X0))
        | ~ m1_subset_1(sK9(sK0,k4_waybel_0(sK0,sK1),X0),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_1748])])).

fof(f21647,plain,
    ( ! [X0] :
        ( r2_yellow_0(sK0,X0)
        | r1_lattice3(sK0,sK1,sK9(sK0,k4_waybel_0(sK0,sK1),X0))
        | r1_lattice3(sK0,X0,sK9(sK0,k4_waybel_0(sK0,sK1),X0))
        | ~ r2_yellow_0(sK0,k4_waybel_0(sK0,sK1)) )
    | ~ spl23_1
    | ~ spl23_6
    | ~ spl23_806
    | ~ spl23_1748 ),
    inference(subsumption_resolution,[],[f21646,f338])).

fof(f21646,plain,
    ( ! [X0] :
        ( r2_yellow_0(sK0,X0)
        | r1_lattice3(sK0,sK1,sK9(sK0,k4_waybel_0(sK0,sK1),X0))
        | r1_lattice3(sK0,X0,sK9(sK0,k4_waybel_0(sK0,sK1),X0))
        | ~ r2_yellow_0(sK0,k4_waybel_0(sK0,sK1))
        | v2_struct_0(sK0) )
    | ~ spl23_6
    | ~ spl23_806
    | ~ spl23_1748 ),
    inference(subsumption_resolution,[],[f21095,f359])).

fof(f21095,plain,
    ( ! [X0] :
        ( r2_yellow_0(sK0,X0)
        | r1_lattice3(sK0,sK1,sK9(sK0,k4_waybel_0(sK0,sK1),X0))
        | r1_lattice3(sK0,X0,sK9(sK0,k4_waybel_0(sK0,sK1),X0))
        | ~ r2_yellow_0(sK0,k4_waybel_0(sK0,sK1))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl23_806
    | ~ spl23_1748 ),
    inference(duplicate_literal_removal,[],[f21093])).

fof(f21093,plain,
    ( ! [X0] :
        ( r2_yellow_0(sK0,X0)
        | r1_lattice3(sK0,sK1,sK9(sK0,k4_waybel_0(sK0,sK1),X0))
        | r1_lattice3(sK0,X0,sK9(sK0,k4_waybel_0(sK0,sK1),X0))
        | ~ r2_yellow_0(sK0,k4_waybel_0(sK0,sK1))
        | r2_yellow_0(sK0,X0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl23_806
    | ~ spl23_1748 ),
    inference(resolution,[],[f10481,f4374])).

fof(f10481,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK9(sK0,k4_waybel_0(sK0,sK1),X0),u1_struct_0(sK0))
        | r2_yellow_0(sK0,X0)
        | r1_lattice3(sK0,sK1,sK9(sK0,k4_waybel_0(sK0,sK1),X0))
        | r1_lattice3(sK0,X0,sK9(sK0,k4_waybel_0(sK0,sK1),X0)) )
    | ~ spl23_1748 ),
    inference(avatar_component_clause,[],[f10480])).

fof(f20909,plain,
    ( ~ spl23_103
    | ~ spl23_104 ),
    inference(avatar_split_clause,[],[f20907,f625,f616])).

fof(f20907,plain,
    ( ~ r2_yellow_0(sK0,sK1)
    | ~ spl23_104 ),
    inference(subsumption_resolution,[],[f229,f626])).

fof(f20899,plain,
    ( spl23_3016
    | spl23_105
    | ~ spl23_2484 ),
    inference(avatar_split_clause,[],[f16040,f15870,f622,f20897])).

fof(f15870,plain,
    ( spl23_2484
  <=> ! [X0] :
        ( r2_yellow_0(sK0,X0)
        | r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK9(sK0,sK1,X0))
        | r1_lattice3(sK0,X0,sK9(sK0,sK1,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_2484])])).

fof(f16040,plain,
    ( r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK9(sK0,sK1,k4_waybel_0(sK0,sK1)))
    | ~ spl23_105
    | ~ spl23_2484 ),
    inference(subsumption_resolution,[],[f16023,f623])).

fof(f623,plain,
    ( ~ r2_yellow_0(sK0,k4_waybel_0(sK0,sK1))
    | ~ spl23_105 ),
    inference(avatar_component_clause,[],[f622])).

fof(f16023,plain,
    ( r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK9(sK0,sK1,k4_waybel_0(sK0,sK1)))
    | r2_yellow_0(sK0,k4_waybel_0(sK0,sK1))
    | ~ spl23_2484 ),
    inference(factoring,[],[f15871])).

fof(f15871,plain,
    ( ! [X0] :
        ( r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK9(sK0,sK1,X0))
        | r1_lattice3(sK0,X0,sK9(sK0,sK1,X0))
        | r2_yellow_0(sK0,X0) )
    | ~ spl23_2484 ),
    inference(avatar_component_clause,[],[f15870])).

fof(f19013,plain,
    ( spl23_2808
    | ~ spl23_56
    | spl23_105
    | ~ spl23_2786 ),
    inference(avatar_split_clause,[],[f18979,f18865,f622,f515,f19011])).

fof(f18865,plain,
    ( spl23_2786
  <=> ! [X0] :
        ( r2_yellow_0(sK0,k4_waybel_0(sK0,X0))
        | r1_lattice3(sK0,X0,sK9(sK0,sK1,k4_waybel_0(sK0,X0)))
        | r1_lattice3(sK0,sK1,sK9(sK0,sK1,k4_waybel_0(sK0,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_2786])])).

fof(f18979,plain,
    ( r1_lattice3(sK0,sK1,sK9(sK0,sK1,k4_waybel_0(sK0,sK1)))
    | ~ spl23_56
    | ~ spl23_105
    | ~ spl23_2786 ),
    inference(subsumption_resolution,[],[f18976,f623])).

fof(f18976,plain,
    ( r1_lattice3(sK0,sK1,sK9(sK0,sK1,k4_waybel_0(sK0,sK1)))
    | r2_yellow_0(sK0,k4_waybel_0(sK0,sK1))
    | ~ spl23_56
    | ~ spl23_2786 ),
    inference(duplicate_literal_removal,[],[f18950])).

fof(f18950,plain,
    ( r1_lattice3(sK0,sK1,sK9(sK0,sK1,k4_waybel_0(sK0,sK1)))
    | r1_lattice3(sK0,sK1,sK9(sK0,sK1,k4_waybel_0(sK0,sK1)))
    | r2_yellow_0(sK0,k4_waybel_0(sK0,sK1))
    | ~ spl23_56
    | ~ spl23_2786 ),
    inference(resolution,[],[f18866,f516])).

fof(f18866,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_lattice3(sK0,X0,sK9(sK0,sK1,k4_waybel_0(sK0,X0)))
        | r1_lattice3(sK0,sK1,sK9(sK0,sK1,k4_waybel_0(sK0,X0)))
        | r2_yellow_0(sK0,k4_waybel_0(sK0,X0)) )
    | ~ spl23_2786 ),
    inference(avatar_component_clause,[],[f18865])).

fof(f18867,plain,
    ( spl23_2786
    | spl23_1
    | ~ spl23_6
    | ~ spl23_102
    | ~ spl23_806
    | ~ spl23_1790 ),
    inference(avatar_split_clause,[],[f11245,f10684,f4373,f619,f358,f337,f18865])).

fof(f619,plain,
    ( spl23_102
  <=> r2_yellow_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_102])])).

fof(f10684,plain,
    ( spl23_1790
  <=> ! [X2] :
        ( r1_lattice3(sK0,sK1,sK9(sK0,sK1,k4_waybel_0(sK0,X2)))
        | r2_yellow_0(sK0,k4_waybel_0(sK0,X2))
        | r1_lattice3(sK0,X2,sK9(sK0,sK1,k4_waybel_0(sK0,X2)))
        | ~ m1_subset_1(sK9(sK0,sK1,k4_waybel_0(sK0,X2)),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_1790])])).

fof(f11245,plain,
    ( ! [X0] :
        ( r2_yellow_0(sK0,k4_waybel_0(sK0,X0))
        | r1_lattice3(sK0,X0,sK9(sK0,sK1,k4_waybel_0(sK0,X0)))
        | r1_lattice3(sK0,sK1,sK9(sK0,sK1,k4_waybel_0(sK0,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl23_1
    | ~ spl23_6
    | ~ spl23_102
    | ~ spl23_806
    | ~ spl23_1790 ),
    inference(subsumption_resolution,[],[f11244,f338])).

fof(f11244,plain,
    ( ! [X0] :
        ( r2_yellow_0(sK0,k4_waybel_0(sK0,X0))
        | r1_lattice3(sK0,X0,sK9(sK0,sK1,k4_waybel_0(sK0,X0)))
        | r1_lattice3(sK0,sK1,sK9(sK0,sK1,k4_waybel_0(sK0,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl23_6
    | ~ spl23_102
    | ~ spl23_806
    | ~ spl23_1790 ),
    inference(subsumption_resolution,[],[f11243,f359])).

fof(f11243,plain,
    ( ! [X0] :
        ( r2_yellow_0(sK0,k4_waybel_0(sK0,X0))
        | r1_lattice3(sK0,X0,sK9(sK0,sK1,k4_waybel_0(sK0,X0)))
        | r1_lattice3(sK0,sK1,sK9(sK0,sK1,k4_waybel_0(sK0,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl23_102
    | ~ spl23_806
    | ~ spl23_1790 ),
    inference(subsumption_resolution,[],[f11242,f620])).

fof(f620,plain,
    ( r2_yellow_0(sK0,sK1)
    | ~ spl23_102 ),
    inference(avatar_component_clause,[],[f619])).

fof(f11242,plain,
    ( ! [X0] :
        ( r2_yellow_0(sK0,k4_waybel_0(sK0,X0))
        | r1_lattice3(sK0,X0,sK9(sK0,sK1,k4_waybel_0(sK0,X0)))
        | r1_lattice3(sK0,sK1,sK9(sK0,sK1,k4_waybel_0(sK0,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_yellow_0(sK0,sK1)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl23_806
    | ~ spl23_1790 ),
    inference(duplicate_literal_removal,[],[f11240])).

fof(f11240,plain,
    ( ! [X0] :
        ( r2_yellow_0(sK0,k4_waybel_0(sK0,X0))
        | r1_lattice3(sK0,X0,sK9(sK0,sK1,k4_waybel_0(sK0,X0)))
        | r1_lattice3(sK0,sK1,sK9(sK0,sK1,k4_waybel_0(sK0,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_yellow_0(sK0,sK1)
        | r2_yellow_0(sK0,k4_waybel_0(sK0,X0))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl23_806
    | ~ spl23_1790 ),
    inference(resolution,[],[f10685,f4374])).

fof(f10685,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(sK9(sK0,sK1,k4_waybel_0(sK0,X2)),u1_struct_0(sK0))
        | r2_yellow_0(sK0,k4_waybel_0(sK0,X2))
        | r1_lattice3(sK0,X2,sK9(sK0,sK1,k4_waybel_0(sK0,X2)))
        | r1_lattice3(sK0,sK1,sK9(sK0,sK1,k4_waybel_0(sK0,X2)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl23_1790 ),
    inference(avatar_component_clause,[],[f10684])).

fof(f15872,plain,
    ( spl23_2484
    | spl23_1
    | ~ spl23_6
    | ~ spl23_102
    | ~ spl23_806
    | ~ spl23_1638 ),
    inference(avatar_split_clause,[],[f10484,f10033,f4373,f619,f358,f337,f15870])).

fof(f10033,plain,
    ( spl23_1638
  <=> ! [X0] :
        ( r1_lattice3(sK0,X0,sK9(sK0,sK1,X0))
        | r2_yellow_0(sK0,X0)
        | r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK9(sK0,sK1,X0))
        | ~ m1_subset_1(sK9(sK0,sK1,X0),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_1638])])).

fof(f10484,plain,
    ( ! [X0] :
        ( r2_yellow_0(sK0,X0)
        | r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK9(sK0,sK1,X0))
        | r1_lattice3(sK0,X0,sK9(sK0,sK1,X0)) )
    | ~ spl23_1
    | ~ spl23_6
    | ~ spl23_102
    | ~ spl23_806
    | ~ spl23_1638 ),
    inference(subsumption_resolution,[],[f10237,f620])).

fof(f10237,plain,
    ( ! [X0] :
        ( r2_yellow_0(sK0,X0)
        | r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK9(sK0,sK1,X0))
        | r1_lattice3(sK0,X0,sK9(sK0,sK1,X0))
        | ~ r2_yellow_0(sK0,sK1) )
    | ~ spl23_1
    | ~ spl23_6
    | ~ spl23_806
    | ~ spl23_1638 ),
    inference(subsumption_resolution,[],[f10236,f338])).

fof(f10236,plain,
    ( ! [X0] :
        ( r2_yellow_0(sK0,X0)
        | r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK9(sK0,sK1,X0))
        | r1_lattice3(sK0,X0,sK9(sK0,sK1,X0))
        | ~ r2_yellow_0(sK0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl23_6
    | ~ spl23_806
    | ~ spl23_1638 ),
    inference(subsumption_resolution,[],[f10178,f359])).

fof(f10178,plain,
    ( ! [X0] :
        ( r2_yellow_0(sK0,X0)
        | r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK9(sK0,sK1,X0))
        | r1_lattice3(sK0,X0,sK9(sK0,sK1,X0))
        | ~ r2_yellow_0(sK0,sK1)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl23_806
    | ~ spl23_1638 ),
    inference(duplicate_literal_removal,[],[f10176])).

fof(f10176,plain,
    ( ! [X0] :
        ( r2_yellow_0(sK0,X0)
        | r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK9(sK0,sK1,X0))
        | r1_lattice3(sK0,X0,sK9(sK0,sK1,X0))
        | ~ r2_yellow_0(sK0,sK1)
        | r2_yellow_0(sK0,X0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl23_806
    | ~ spl23_1638 ),
    inference(resolution,[],[f10034,f4374])).

fof(f10034,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK9(sK0,sK1,X0),u1_struct_0(sK0))
        | r2_yellow_0(sK0,X0)
        | r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK9(sK0,sK1,X0))
        | r1_lattice3(sK0,X0,sK9(sK0,sK1,X0)) )
    | ~ spl23_1638 ),
    inference(avatar_component_clause,[],[f10033])).

fof(f10686,plain,
    ( spl23_1790
    | spl23_1
    | ~ spl23_2
    | ~ spl23_4
    | ~ spl23_6
    | ~ spl23_1014
    | ~ spl23_1156 ),
    inference(avatar_split_clause,[],[f10568,f6514,f5542,f358,f351,f344,f337,f10684])).

fof(f5542,plain,
    ( spl23_1014
  <=> ! [X1,X0,X2] :
        ( r1_lattice3(X0,X1,X2)
        | ~ r1_lattice3(X0,k4_waybel_0(X0,X1),X2)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_1014])])).

fof(f6514,plain,
    ( spl23_1156
  <=> ! [X0] :
        ( r2_yellow_0(sK0,X0)
        | r1_lattice3(sK0,X0,sK9(sK0,sK1,X0))
        | r1_lattice3(sK0,sK1,sK9(sK0,sK1,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_1156])])).

fof(f10568,plain,
    ( ! [X2] :
        ( r1_lattice3(sK0,sK1,sK9(sK0,sK1,k4_waybel_0(sK0,X2)))
        | r2_yellow_0(sK0,k4_waybel_0(sK0,X2))
        | r1_lattice3(sK0,X2,sK9(sK0,sK1,k4_waybel_0(sK0,X2)))
        | ~ m1_subset_1(sK9(sK0,sK1,k4_waybel_0(sK0,X2)),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl23_1
    | ~ spl23_2
    | ~ spl23_4
    | ~ spl23_6
    | ~ spl23_1014
    | ~ spl23_1156 ),
    inference(subsumption_resolution,[],[f10567,f338])).

fof(f10567,plain,
    ( ! [X2] :
        ( r1_lattice3(sK0,sK1,sK9(sK0,sK1,k4_waybel_0(sK0,X2)))
        | r2_yellow_0(sK0,k4_waybel_0(sK0,X2))
        | r1_lattice3(sK0,X2,sK9(sK0,sK1,k4_waybel_0(sK0,X2)))
        | ~ m1_subset_1(sK9(sK0,sK1,k4_waybel_0(sK0,X2)),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl23_2
    | ~ spl23_4
    | ~ spl23_6
    | ~ spl23_1014
    | ~ spl23_1156 ),
    inference(subsumption_resolution,[],[f10566,f345])).

fof(f10566,plain,
    ( ! [X2] :
        ( r1_lattice3(sK0,sK1,sK9(sK0,sK1,k4_waybel_0(sK0,X2)))
        | r2_yellow_0(sK0,k4_waybel_0(sK0,X2))
        | r1_lattice3(sK0,X2,sK9(sK0,sK1,k4_waybel_0(sK0,X2)))
        | ~ m1_subset_1(sK9(sK0,sK1,k4_waybel_0(sK0,X2)),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl23_4
    | ~ spl23_6
    | ~ spl23_1014
    | ~ spl23_1156 ),
    inference(subsumption_resolution,[],[f10565,f352])).

fof(f10565,plain,
    ( ! [X2] :
        ( r1_lattice3(sK0,sK1,sK9(sK0,sK1,k4_waybel_0(sK0,X2)))
        | r2_yellow_0(sK0,k4_waybel_0(sK0,X2))
        | r1_lattice3(sK0,X2,sK9(sK0,sK1,k4_waybel_0(sK0,X2)))
        | ~ m1_subset_1(sK9(sK0,sK1,k4_waybel_0(sK0,X2)),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl23_6
    | ~ spl23_1014
    | ~ spl23_1156 ),
    inference(subsumption_resolution,[],[f10560,f359])).

fof(f10560,plain,
    ( ! [X2] :
        ( r1_lattice3(sK0,sK1,sK9(sK0,sK1,k4_waybel_0(sK0,X2)))
        | r2_yellow_0(sK0,k4_waybel_0(sK0,X2))
        | r1_lattice3(sK0,X2,sK9(sK0,sK1,k4_waybel_0(sK0,X2)))
        | ~ m1_subset_1(sK9(sK0,sK1,k4_waybel_0(sK0,X2)),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl23_1014
    | ~ spl23_1156 ),
    inference(resolution,[],[f6515,f5543])).

fof(f5543,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_lattice3(X0,k4_waybel_0(X0,X1),X2)
        | r1_lattice3(X0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_orders_2(X0)
        | ~ v4_orders_2(X0)
        | ~ v3_orders_2(X0)
        | v2_struct_0(X0) )
    | ~ spl23_1014 ),
    inference(avatar_component_clause,[],[f5542])).

fof(f6515,plain,
    ( ! [X0] :
        ( r1_lattice3(sK0,X0,sK9(sK0,sK1,X0))
        | r1_lattice3(sK0,sK1,sK9(sK0,sK1,X0))
        | r2_yellow_0(sK0,X0) )
    | ~ spl23_1156 ),
    inference(avatar_component_clause,[],[f6514])).

fof(f10482,plain,
    ( spl23_1748
    | spl23_1
    | ~ spl23_2
    | ~ spl23_4
    | ~ spl23_6
    | ~ spl23_56
    | ~ spl23_1014
    | ~ spl23_1138 ),
    inference(avatar_split_clause,[],[f10334,f6422,f5542,f515,f358,f351,f344,f337,f10480])).

fof(f6422,plain,
    ( spl23_1138
  <=> ! [X0] :
        ( r2_yellow_0(sK0,X0)
        | r1_lattice3(sK0,X0,sK9(sK0,k4_waybel_0(sK0,sK1),X0))
        | r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK9(sK0,k4_waybel_0(sK0,sK1),X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_1138])])).

fof(f10334,plain,
    ( ! [X0] :
        ( r1_lattice3(sK0,X0,sK9(sK0,k4_waybel_0(sK0,sK1),X0))
        | r2_yellow_0(sK0,X0)
        | r1_lattice3(sK0,sK1,sK9(sK0,k4_waybel_0(sK0,sK1),X0))
        | ~ m1_subset_1(sK9(sK0,k4_waybel_0(sK0,sK1),X0),u1_struct_0(sK0)) )
    | ~ spl23_1
    | ~ spl23_2
    | ~ spl23_4
    | ~ spl23_6
    | ~ spl23_56
    | ~ spl23_1014
    | ~ spl23_1138 ),
    inference(subsumption_resolution,[],[f10333,f338])).

fof(f10333,plain,
    ( ! [X0] :
        ( r1_lattice3(sK0,X0,sK9(sK0,k4_waybel_0(sK0,sK1),X0))
        | r2_yellow_0(sK0,X0)
        | r1_lattice3(sK0,sK1,sK9(sK0,k4_waybel_0(sK0,sK1),X0))
        | ~ m1_subset_1(sK9(sK0,k4_waybel_0(sK0,sK1),X0),u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl23_2
    | ~ spl23_4
    | ~ spl23_6
    | ~ spl23_56
    | ~ spl23_1014
    | ~ spl23_1138 ),
    inference(subsumption_resolution,[],[f10332,f345])).

fof(f10332,plain,
    ( ! [X0] :
        ( r1_lattice3(sK0,X0,sK9(sK0,k4_waybel_0(sK0,sK1),X0))
        | r2_yellow_0(sK0,X0)
        | r1_lattice3(sK0,sK1,sK9(sK0,k4_waybel_0(sK0,sK1),X0))
        | ~ m1_subset_1(sK9(sK0,k4_waybel_0(sK0,sK1),X0),u1_struct_0(sK0))
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl23_4
    | ~ spl23_6
    | ~ spl23_56
    | ~ spl23_1014
    | ~ spl23_1138 ),
    inference(subsumption_resolution,[],[f10331,f352])).

fof(f10331,plain,
    ( ! [X0] :
        ( r1_lattice3(sK0,X0,sK9(sK0,k4_waybel_0(sK0,sK1),X0))
        | r2_yellow_0(sK0,X0)
        | r1_lattice3(sK0,sK1,sK9(sK0,k4_waybel_0(sK0,sK1),X0))
        | ~ m1_subset_1(sK9(sK0,k4_waybel_0(sK0,sK1),X0),u1_struct_0(sK0))
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl23_6
    | ~ spl23_56
    | ~ spl23_1014
    | ~ spl23_1138 ),
    inference(subsumption_resolution,[],[f10330,f359])).

fof(f10330,plain,
    ( ! [X0] :
        ( r1_lattice3(sK0,X0,sK9(sK0,k4_waybel_0(sK0,sK1),X0))
        | r2_yellow_0(sK0,X0)
        | r1_lattice3(sK0,sK1,sK9(sK0,k4_waybel_0(sK0,sK1),X0))
        | ~ m1_subset_1(sK9(sK0,k4_waybel_0(sK0,sK1),X0),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl23_56
    | ~ spl23_1014
    | ~ spl23_1138 ),
    inference(subsumption_resolution,[],[f10317,f516])).

fof(f10317,plain,
    ( ! [X0] :
        ( r1_lattice3(sK0,X0,sK9(sK0,k4_waybel_0(sK0,sK1),X0))
        | r2_yellow_0(sK0,X0)
        | r1_lattice3(sK0,sK1,sK9(sK0,k4_waybel_0(sK0,sK1),X0))
        | ~ m1_subset_1(sK9(sK0,k4_waybel_0(sK0,sK1),X0),u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl23_1014
    | ~ spl23_1138 ),
    inference(resolution,[],[f6423,f5543])).

fof(f6423,plain,
    ( ! [X0] :
        ( r1_lattice3(sK0,X0,sK9(sK0,k4_waybel_0(sK0,sK1),X0))
        | r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK9(sK0,k4_waybel_0(sK0,sK1),X0))
        | r2_yellow_0(sK0,X0) )
    | ~ spl23_1138 ),
    inference(avatar_component_clause,[],[f6422])).

fof(f10035,plain,
    ( spl23_1638
    | spl23_1
    | ~ spl23_2
    | ~ spl23_4
    | ~ spl23_6
    | ~ spl23_56
    | ~ spl23_992
    | ~ spl23_1156 ),
    inference(avatar_split_clause,[],[f6651,f6514,f5379,f515,f358,f351,f344,f337,f10033])).

fof(f6651,plain,
    ( ! [X0] :
        ( r1_lattice3(sK0,X0,sK9(sK0,sK1,X0))
        | r2_yellow_0(sK0,X0)
        | r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK9(sK0,sK1,X0))
        | ~ m1_subset_1(sK9(sK0,sK1,X0),u1_struct_0(sK0)) )
    | ~ spl23_1
    | ~ spl23_2
    | ~ spl23_4
    | ~ spl23_6
    | ~ spl23_56
    | ~ spl23_992
    | ~ spl23_1156 ),
    inference(subsumption_resolution,[],[f6650,f338])).

fof(f6650,plain,
    ( ! [X0] :
        ( r1_lattice3(sK0,X0,sK9(sK0,sK1,X0))
        | r2_yellow_0(sK0,X0)
        | r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK9(sK0,sK1,X0))
        | ~ m1_subset_1(sK9(sK0,sK1,X0),u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl23_2
    | ~ spl23_4
    | ~ spl23_6
    | ~ spl23_56
    | ~ spl23_992
    | ~ spl23_1156 ),
    inference(subsumption_resolution,[],[f6649,f345])).

fof(f6649,plain,
    ( ! [X0] :
        ( r1_lattice3(sK0,X0,sK9(sK0,sK1,X0))
        | r2_yellow_0(sK0,X0)
        | r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK9(sK0,sK1,X0))
        | ~ m1_subset_1(sK9(sK0,sK1,X0),u1_struct_0(sK0))
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl23_4
    | ~ spl23_6
    | ~ spl23_56
    | ~ spl23_992
    | ~ spl23_1156 ),
    inference(subsumption_resolution,[],[f6648,f352])).

fof(f6648,plain,
    ( ! [X0] :
        ( r1_lattice3(sK0,X0,sK9(sK0,sK1,X0))
        | r2_yellow_0(sK0,X0)
        | r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK9(sK0,sK1,X0))
        | ~ m1_subset_1(sK9(sK0,sK1,X0),u1_struct_0(sK0))
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl23_6
    | ~ spl23_56
    | ~ spl23_992
    | ~ spl23_1156 ),
    inference(subsumption_resolution,[],[f6647,f359])).

fof(f6647,plain,
    ( ! [X0] :
        ( r1_lattice3(sK0,X0,sK9(sK0,sK1,X0))
        | r2_yellow_0(sK0,X0)
        | r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK9(sK0,sK1,X0))
        | ~ m1_subset_1(sK9(sK0,sK1,X0),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl23_56
    | ~ spl23_992
    | ~ spl23_1156 ),
    inference(subsumption_resolution,[],[f6636,f516])).

fof(f6636,plain,
    ( ! [X0] :
        ( r1_lattice3(sK0,X0,sK9(sK0,sK1,X0))
        | r2_yellow_0(sK0,X0)
        | r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK9(sK0,sK1,X0))
        | ~ m1_subset_1(sK9(sK0,sK1,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl23_992
    | ~ spl23_1156 ),
    inference(resolution,[],[f6515,f5380])).

fof(f6516,plain,
    ( spl23_1156
    | spl23_1
    | ~ spl23_6
    | ~ spl23_102
    | ~ spl23_914 ),
    inference(avatar_split_clause,[],[f6428,f5009,f619,f358,f337,f6514])).

fof(f5009,plain,
    ( spl23_914
  <=> ! [X1,X0,X2] :
        ( r2_yellow_0(X0,X2)
        | ~ r2_yellow_0(X0,X1)
        | r1_lattice3(X0,X2,sK9(X0,X1,X2))
        | r1_lattice3(X0,X1,sK9(X0,X1,X2))
        | ~ l1_orders_2(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_914])])).

fof(f6428,plain,
    ( ! [X0] :
        ( r2_yellow_0(sK0,X0)
        | r1_lattice3(sK0,X0,sK9(sK0,sK1,X0))
        | r1_lattice3(sK0,sK1,sK9(sK0,sK1,X0)) )
    | ~ spl23_1
    | ~ spl23_6
    | ~ spl23_102
    | ~ spl23_914 ),
    inference(subsumption_resolution,[],[f6427,f338])).

fof(f6427,plain,
    ( ! [X0] :
        ( r2_yellow_0(sK0,X0)
        | r1_lattice3(sK0,X0,sK9(sK0,sK1,X0))
        | r1_lattice3(sK0,sK1,sK9(sK0,sK1,X0))
        | v2_struct_0(sK0) )
    | ~ spl23_6
    | ~ spl23_102
    | ~ spl23_914 ),
    inference(subsumption_resolution,[],[f6426,f359])).

fof(f6426,plain,
    ( ! [X0] :
        ( r2_yellow_0(sK0,X0)
        | r1_lattice3(sK0,X0,sK9(sK0,sK1,X0))
        | r1_lattice3(sK0,sK1,sK9(sK0,sK1,X0))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl23_102
    | ~ spl23_914 ),
    inference(resolution,[],[f620,f5010])).

fof(f5010,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_yellow_0(X0,X1)
        | r2_yellow_0(X0,X2)
        | r1_lattice3(X0,X2,sK9(X0,X1,X2))
        | r1_lattice3(X0,X1,sK9(X0,X1,X2))
        | ~ l1_orders_2(X0)
        | v2_struct_0(X0) )
    | ~ spl23_914 ),
    inference(avatar_component_clause,[],[f5009])).

fof(f6424,plain,
    ( spl23_1138
    | spl23_1
    | ~ spl23_6
    | ~ spl23_104
    | ~ spl23_914 ),
    inference(avatar_split_clause,[],[f5174,f5009,f625,f358,f337,f6422])).

fof(f5174,plain,
    ( ! [X0] :
        ( r2_yellow_0(sK0,X0)
        | r1_lattice3(sK0,X0,sK9(sK0,k4_waybel_0(sK0,sK1),X0))
        | r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK9(sK0,k4_waybel_0(sK0,sK1),X0)) )
    | ~ spl23_1
    | ~ spl23_6
    | ~ spl23_104
    | ~ spl23_914 ),
    inference(subsumption_resolution,[],[f5173,f338])).

fof(f5173,plain,
    ( ! [X0] :
        ( r2_yellow_0(sK0,X0)
        | r1_lattice3(sK0,X0,sK9(sK0,k4_waybel_0(sK0,sK1),X0))
        | r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK9(sK0,k4_waybel_0(sK0,sK1),X0))
        | v2_struct_0(sK0) )
    | ~ spl23_6
    | ~ spl23_104
    | ~ spl23_914 ),
    inference(subsumption_resolution,[],[f5172,f359])).

fof(f5172,plain,
    ( ! [X0] :
        ( r2_yellow_0(sK0,X0)
        | r1_lattice3(sK0,X0,sK9(sK0,k4_waybel_0(sK0,sK1),X0))
        | r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK9(sK0,k4_waybel_0(sK0,sK1),X0))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl23_104
    | ~ spl23_914 ),
    inference(resolution,[],[f5010,f626])).

fof(f5544,plain,(
    spl23_1014 ),
    inference(avatar_split_clause,[],[f279,f5542])).

fof(f279,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | ~ r1_lattice3(X0,k4_waybel_0(X0,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f188])).

fof(f188,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_lattice3(X0,X1,X2)
                  | ~ r1_lattice3(X0,k4_waybel_0(X0,X1),X2) )
                & ( r1_lattice3(X0,k4_waybel_0(X0,X1),X2)
                  | ~ r1_lattice3(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f139])).

fof(f139,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattice3(X0,X1,X2)
              <=> r1_lattice3(X0,k4_waybel_0(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f138])).

fof(f138,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattice3(X0,X1,X2)
              <=> r1_lattice3(X0,k4_waybel_0(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f69])).

fof(f69,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_lattice3(X0,X1,X2)
              <=> r1_lattice3(X0,k4_waybel_0(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t37_waybel_0.p',t36_waybel_0)).

fof(f5381,plain,(
    spl23_992 ),
    inference(avatar_split_clause,[],[f278,f5379])).

fof(f278,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,k4_waybel_0(X0,X1),X2)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f188])).

fof(f5088,plain,(
    spl23_932 ),
    inference(avatar_split_clause,[],[f289,f5086])).

fof(f289,plain,(
    ! [X2,X0,X1] :
      ( r2_yellow_0(X0,X2)
      | ~ r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X2,sK9(X0,X1,X2))
      | ~ r1_lattice3(X0,X1,sK9(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f196])).

fof(f196,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ( ( ~ r1_lattice3(X0,X2,sK9(X0,X1,X2))
              | ~ r1_lattice3(X0,X1,sK9(X0,X1,X2)) )
            & ( r1_lattice3(X0,X2,sK9(X0,X1,X2))
              | r1_lattice3(X0,X1,sK9(X0,X1,X2)) )
            & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f194,f195])).

fof(f195,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r1_lattice3(X0,X2,X3)
            | ~ r1_lattice3(X0,X1,X3) )
          & ( r1_lattice3(X0,X2,X3)
            | r1_lattice3(X0,X1,X3) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ~ r1_lattice3(X0,X2,sK9(X0,X1,X2))
          | ~ r1_lattice3(X0,X1,sK9(X0,X1,X2)) )
        & ( r1_lattice3(X0,X2,sK9(X0,X1,X2))
          | r1_lattice3(X0,X1,sK9(X0,X1,X2)) )
        & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f194,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ? [X3] :
              ( ( ~ r1_lattice3(X0,X2,X3)
                | ~ r1_lattice3(X0,X1,X3) )
              & ( r1_lattice3(X0,X2,X3)
                | r1_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f193])).

fof(f193,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ? [X3] :
              ( ( ~ r1_lattice3(X0,X2,X3)
                | ~ r1_lattice3(X0,X1,X3) )
              & ( r1_lattice3(X0,X2,X3)
                | r1_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f145])).

fof(f145,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ? [X3] :
              ( ( r1_lattice3(X0,X1,X3)
              <~> r1_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f144])).

fof(f144,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ? [X3] :
              ( ( r1_lattice3(X0,X1,X3)
              <~> r1_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f71])).

fof(f71,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( ( r2_yellow_0(X0,X1)
            & ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r1_lattice3(X0,X1,X3)
                <=> r1_lattice3(X0,X2,X3) ) ) )
         => r2_yellow_0(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t37_waybel_0.p',t48_yellow_0)).

fof(f5011,plain,(
    spl23_914 ),
    inference(avatar_split_clause,[],[f288,f5009])).

fof(f288,plain,(
    ! [X2,X0,X1] :
      ( r2_yellow_0(X0,X2)
      | ~ r2_yellow_0(X0,X1)
      | r1_lattice3(X0,X2,sK9(X0,X1,X2))
      | r1_lattice3(X0,X1,sK9(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f196])).

fof(f4375,plain,(
    spl23_806 ),
    inference(avatar_split_clause,[],[f287,f4373])).

fof(f287,plain,(
    ! [X2,X0,X1] :
      ( r2_yellow_0(X0,X2)
      | ~ r2_yellow_0(X0,X1)
      | m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f196])).

fof(f627,plain,
    ( spl23_102
    | spl23_104 ),
    inference(avatar_split_clause,[],[f228,f625,f619])).

fof(f228,plain,
    ( r2_yellow_0(sK0,k4_waybel_0(sK0,sK1))
    | r2_yellow_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f177])).

fof(f517,plain,(
    spl23_56 ),
    inference(avatar_split_clause,[],[f227,f515])).

fof(f227,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f177])).

fof(f360,plain,(
    spl23_6 ),
    inference(avatar_split_clause,[],[f226,f358])).

fof(f226,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f177])).

fof(f353,plain,(
    spl23_4 ),
    inference(avatar_split_clause,[],[f225,f351])).

fof(f225,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f177])).

fof(f346,plain,(
    spl23_2 ),
    inference(avatar_split_clause,[],[f224,f344])).

fof(f224,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f177])).

fof(f339,plain,(
    ~ spl23_1 ),
    inference(avatar_split_clause,[],[f223,f337])).

fof(f223,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f177])).
%------------------------------------------------------------------------------
