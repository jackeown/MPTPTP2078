%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1656+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:16 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  270 ( 532 expanded)
%              Number of leaves         :   57 ( 250 expanded)
%              Depth                    :    7
%              Number of atoms          : 1298 (2398 expanded)
%              Number of equality atoms :    6 (  12 expanded)
%              Maximal formula depth    :   15 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f862,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f64,f68,f72,f76,f80,f87,f90,f94,f98,f102,f106,f110,f114,f119,f124,f128,f136,f141,f154,f161,f169,f173,f182,f187,f198,f208,f212,f218,f222,f239,f245,f249,f257,f275,f294,f308,f312,f351,f419,f487,f531,f578,f601,f625,f657,f687,f778,f797,f819,f861])).

fof(f861,plain,
    ( spl7_88
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_35
    | ~ spl7_89 ),
    inference(avatar_split_clause,[],[f835,f776,f220,f78,f70,f772])).

fof(f772,plain,
    ( spl7_88
  <=> ! [X1] :
        ( ~ r1_orders_2(sK0,sK5(sK0,sK1,X1),sK6(sK0,k4_waybel_0(sK0,sK1),sK2))
        | ~ r2_hidden(X1,k4_waybel_0(sK0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_88])])).

fof(f70,plain,
    ( spl7_4
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f78,plain,
    ( spl7_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f220,plain,
    ( spl7_35
  <=> ! [X1,X3,X0] :
        ( ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | m1_subset_1(sK5(X0,X1,X3),u1_struct_0(X0))
        | ~ r2_hidden(X3,k4_waybel_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f776,plain,
    ( spl7_89
  <=> ! [X1] :
        ( ~ m1_subset_1(sK5(sK0,sK1,X1),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,sK1,X1),sK6(sK0,k4_waybel_0(sK0,sK1),sK2))
        | ~ r2_hidden(X1,k4_waybel_0(sK0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_89])])).

fof(f835,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK5(sK0,sK1,X0),sK6(sK0,k4_waybel_0(sK0,sK1),sK2))
        | ~ r2_hidden(X0,k4_waybel_0(sK0,sK1)) )
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_35
    | ~ spl7_89 ),
    inference(subsumption_resolution,[],[f834,f71])).

fof(f71,plain,
    ( l1_orders_2(sK0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f70])).

fof(f834,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK5(sK0,sK1,X0),sK6(sK0,k4_waybel_0(sK0,sK1),sK2))
        | ~ r2_hidden(X0,k4_waybel_0(sK0,sK1))
        | ~ l1_orders_2(sK0) )
    | ~ spl7_6
    | ~ spl7_35
    | ~ spl7_89 ),
    inference(subsumption_resolution,[],[f833,f79])).

fof(f79,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f78])).

fof(f833,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK5(sK0,sK1,X0),sK6(sK0,k4_waybel_0(sK0,sK1),sK2))
        | ~ r2_hidden(X0,k4_waybel_0(sK0,sK1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0) )
    | ~ spl7_35
    | ~ spl7_89 ),
    inference(duplicate_literal_removal,[],[f830])).

fof(f830,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK5(sK0,sK1,X0),sK6(sK0,k4_waybel_0(sK0,sK1),sK2))
        | ~ r2_hidden(X0,k4_waybel_0(sK0,sK1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | ~ r2_hidden(X0,k4_waybel_0(sK0,sK1)) )
    | ~ spl7_35
    | ~ spl7_89 ),
    inference(resolution,[],[f777,f221])).

fof(f221,plain,
    ( ! [X0,X3,X1] :
        ( m1_subset_1(sK5(X0,X1,X3),u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_orders_2(X0)
        | ~ r2_hidden(X3,k4_waybel_0(X0,X1)) )
    | ~ spl7_35 ),
    inference(avatar_component_clause,[],[f220])).

fof(f777,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK5(sK0,sK1,X1),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,sK1,X1),sK6(sK0,k4_waybel_0(sK0,sK1),sK2))
        | ~ r2_hidden(X1,k4_waybel_0(sK0,sK1)) )
    | ~ spl7_89 ),
    inference(avatar_component_clause,[],[f776])).

fof(f819,plain,
    ( ~ spl7_5
    | spl7_8
    | ~ spl7_15
    | spl7_91 ),
    inference(avatar_contradiction_clause,[],[f818])).

fof(f818,plain,
    ( $false
    | ~ spl7_5
    | spl7_8
    | ~ spl7_15
    | spl7_91 ),
    inference(subsumption_resolution,[],[f817,f89])).

fof(f89,plain,
    ( ~ r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)
    | spl7_8 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl7_8
  <=> r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f817,plain,
    ( r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)
    | ~ spl7_5
    | ~ spl7_15
    | spl7_91 ),
    inference(subsumption_resolution,[],[f814,f75])).

fof(f75,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl7_5
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f814,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)
    | ~ spl7_15
    | spl7_91 ),
    inference(resolution,[],[f796,f118])).

fof(f118,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK6(sK0,X1,X0),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattice3(sK0,X1,X0) )
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl7_15
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(sK6(sK0,X1,X0),X1)
        | r1_lattice3(sK0,X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f796,plain,
    ( ~ r2_hidden(sK6(sK0,k4_waybel_0(sK0,sK1),sK2),k4_waybel_0(sK0,sK1))
    | spl7_91 ),
    inference(avatar_component_clause,[],[f795])).

fof(f795,plain,
    ( spl7_91
  <=> r2_hidden(sK6(sK0,k4_waybel_0(sK0,sK1),sK2),k4_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_91])])).

fof(f797,plain,
    ( ~ spl7_91
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_32
    | ~ spl7_88 ),
    inference(avatar_split_clause,[],[f789,f772,f206,f78,f70,f795])).

fof(f206,plain,
    ( spl7_32
  <=> ! [X1,X3,X0] :
        ( ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | r1_orders_2(X0,sK5(X0,X1,X3),X3)
        | ~ r2_hidden(X3,k4_waybel_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f789,plain,
    ( ~ r2_hidden(sK6(sK0,k4_waybel_0(sK0,sK1),sK2),k4_waybel_0(sK0,sK1))
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_32
    | ~ spl7_88 ),
    inference(subsumption_resolution,[],[f788,f71])).

fof(f788,plain,
    ( ~ r2_hidden(sK6(sK0,k4_waybel_0(sK0,sK1),sK2),k4_waybel_0(sK0,sK1))
    | ~ l1_orders_2(sK0)
    | ~ spl7_6
    | ~ spl7_32
    | ~ spl7_88 ),
    inference(subsumption_resolution,[],[f787,f79])).

fof(f787,plain,
    ( ~ r2_hidden(sK6(sK0,k4_waybel_0(sK0,sK1),sK2),k4_waybel_0(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ spl7_32
    | ~ spl7_88 ),
    inference(duplicate_literal_removal,[],[f786])).

fof(f786,plain,
    ( ~ r2_hidden(sK6(sK0,k4_waybel_0(sK0,sK1),sK2),k4_waybel_0(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ r2_hidden(sK6(sK0,k4_waybel_0(sK0,sK1),sK2),k4_waybel_0(sK0,sK1))
    | ~ spl7_32
    | ~ spl7_88 ),
    inference(resolution,[],[f773,f207])).

fof(f207,plain,
    ( ! [X0,X3,X1] :
        ( r1_orders_2(X0,sK5(X0,X1,X3),X3)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_orders_2(X0)
        | ~ r2_hidden(X3,k4_waybel_0(X0,X1)) )
    | ~ spl7_32 ),
    inference(avatar_component_clause,[],[f206])).

fof(f773,plain,
    ( ! [X1] :
        ( ~ r1_orders_2(sK0,sK5(sK0,sK1,X1),sK6(sK0,k4_waybel_0(sK0,sK1),sK2))
        | ~ r2_hidden(X1,k4_waybel_0(sK0,sK1)) )
    | ~ spl7_88 ),
    inference(avatar_component_clause,[],[f772])).

fof(f778,plain,
    ( spl7_89
    | ~ spl7_6
    | ~ spl7_28
    | ~ spl7_80 ),
    inference(avatar_split_clause,[],[f699,f685,f185,f78,f776])).

fof(f185,plain,
    ( spl7_28
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(sK5(sK0,X0,X1),X0)
        | ~ r2_hidden(X1,k4_waybel_0(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f685,plain,
    ( spl7_80
  <=> ! [X0] :
        ( ~ r1_orders_2(sK0,X0,sK6(sK0,k4_waybel_0(sK0,sK1),sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_80])])).

fof(f699,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK5(sK0,sK1,X1),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,sK1,X1),sK6(sK0,k4_waybel_0(sK0,sK1),sK2))
        | ~ r2_hidden(X1,k4_waybel_0(sK0,sK1)) )
    | ~ spl7_6
    | ~ spl7_28
    | ~ spl7_80 ),
    inference(subsumption_resolution,[],[f697,f79])).

fof(f697,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK5(sK0,sK1,X1),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK5(sK0,sK1,X1),sK6(sK0,k4_waybel_0(sK0,sK1),sK2))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X1,k4_waybel_0(sK0,sK1)) )
    | ~ spl7_28
    | ~ spl7_80 ),
    inference(resolution,[],[f686,f186])).

fof(f186,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK5(sK0,X0,X1),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X1,k4_waybel_0(sK0,X0)) )
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f185])).

fof(f686,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,sK6(sK0,k4_waybel_0(sK0,sK1),sK2)) )
    | ~ spl7_80 ),
    inference(avatar_component_clause,[],[f685])).

fof(f687,plain,
    ( spl7_80
    | ~ spl7_62
    | ~ spl7_67 ),
    inference(avatar_split_clause,[],[f669,f485,f417,f685])).

fof(f417,plain,
    ( spl7_62
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1)
        | r1_orders_2(sK0,sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_62])])).

fof(f485,plain,
    ( spl7_67
  <=> ! [X1] :
        ( ~ r1_orders_2(sK0,sK2,X1)
        | ~ r1_orders_2(sK0,X1,sK6(sK0,k4_waybel_0(sK0,sK1),sK2))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_67])])).

fof(f669,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,X0,sK6(sK0,k4_waybel_0(sK0,sK1),sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl7_62
    | ~ spl7_67 ),
    inference(duplicate_literal_removal,[],[f662])).

fof(f662,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,X0,sK6(sK0,k4_waybel_0(sK0,sK1),sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_62
    | ~ spl7_67 ),
    inference(resolution,[],[f486,f418])).

fof(f418,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK2,X0)
        | ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_62 ),
    inference(avatar_component_clause,[],[f417])).

fof(f486,plain,
    ( ! [X1] :
        ( ~ r1_orders_2(sK0,sK2,X1)
        | ~ r1_orders_2(sK0,X1,sK6(sK0,k4_waybel_0(sK0,sK1),sK2))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl7_67 ),
    inference(avatar_component_clause,[],[f485])).

fof(f657,plain,
    ( ~ spl7_68
    | spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_11
    | spl7_77 ),
    inference(avatar_split_clause,[],[f642,f623,f100,f70,f62,f58,f495])).

fof(f495,plain,
    ( spl7_68
  <=> m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_68])])).

fof(f58,plain,
    ( spl7_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f62,plain,
    ( spl7_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f100,plain,
    ( spl7_11
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(X1))
        | v2_struct_0(X1)
        | ~ v3_orders_2(X1)
        | ~ l1_orders_2(X1)
        | r3_orders_2(X1,X0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f623,plain,
    ( spl7_77
  <=> r3_orders_2(sK0,sK6(sK0,sK1,sK2),sK6(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_77])])).

fof(f642,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK0))
    | spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_11
    | spl7_77 ),
    inference(subsumption_resolution,[],[f641,f71])).

fof(f641,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK0))
    | spl7_1
    | ~ spl7_2
    | ~ spl7_11
    | spl7_77 ),
    inference(subsumption_resolution,[],[f640,f63])).

fof(f63,plain,
    ( v3_orders_2(sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f640,plain,
    ( ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK0))
    | spl7_1
    | ~ spl7_11
    | spl7_77 ),
    inference(subsumption_resolution,[],[f637,f59])).

fof(f59,plain,
    ( ~ v2_struct_0(sK0)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f637,plain,
    ( v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl7_11
    | spl7_77 ),
    inference(resolution,[],[f624,f101])).

fof(f101,plain,
    ( ! [X0,X1] :
        ( r3_orders_2(X1,X0,X0)
        | v2_struct_0(X1)
        | ~ v3_orders_2(X1)
        | ~ l1_orders_2(X1)
        | ~ m1_subset_1(X0,u1_struct_0(X1)) )
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f100])).

fof(f624,plain,
    ( ~ r3_orders_2(sK0,sK6(sK0,sK1,sK2),sK6(sK0,sK1,sK2))
    | spl7_77 ),
    inference(avatar_component_clause,[],[f623])).

fof(f625,plain,
    ( ~ spl7_77
    | ~ spl7_68
    | ~ spl7_25
    | spl7_75 ),
    inference(avatar_split_clause,[],[f606,f599,f167,f495,f623])).

fof(f167,plain,
    ( spl7_25
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,X1)
        | ~ r3_orders_2(sK0,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f599,plain,
    ( spl7_75
  <=> r1_orders_2(sK0,sK6(sK0,sK1,sK2),sK6(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_75])])).

fof(f606,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ r3_orders_2(sK0,sK6(sK0,sK1,sK2),sK6(sK0,sK1,sK2))
    | ~ spl7_25
    | spl7_75 ),
    inference(duplicate_literal_removal,[],[f605])).

fof(f605,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ r3_orders_2(sK0,sK6(sK0,sK1,sK2),sK6(sK0,sK1,sK2))
    | ~ spl7_25
    | spl7_75 ),
    inference(resolution,[],[f600,f168])).

fof(f168,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_orders_2(sK0,X0,X1) )
    | ~ spl7_25 ),
    inference(avatar_component_clause,[],[f167])).

fof(f600,plain,
    ( ~ r1_orders_2(sK0,sK6(sK0,sK1,sK2),sK6(sK0,sK1,sK2))
    | spl7_75 ),
    inference(avatar_component_clause,[],[f599])).

fof(f601,plain,
    ( ~ spl7_75
    | ~ spl7_5
    | spl7_7
    | ~ spl7_73 ),
    inference(avatar_split_clause,[],[f588,f576,f82,f74,f599])).

fof(f82,plain,
    ( spl7_7
  <=> r1_lattice3(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f576,plain,
    ( spl7_73
  <=> ! [X0] :
        ( ~ r1_orders_2(sK0,sK6(sK0,sK1,X0),sK6(sK0,sK1,sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattice3(sK0,sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_73])])).

fof(f588,plain,
    ( ~ r1_orders_2(sK0,sK6(sK0,sK1,sK2),sK6(sK0,sK1,sK2))
    | ~ spl7_5
    | spl7_7
    | ~ spl7_73 ),
    inference(subsumption_resolution,[],[f585,f75])).

fof(f585,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK6(sK0,sK1,sK2),sK6(sK0,sK1,sK2))
    | spl7_7
    | ~ spl7_73 ),
    inference(resolution,[],[f577,f88])).

fof(f88,plain,
    ( ~ r1_lattice3(sK0,sK1,sK2)
    | spl7_7 ),
    inference(avatar_component_clause,[],[f82])).

fof(f577,plain,
    ( ! [X0] :
        ( r1_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK6(sK0,sK1,X0),sK6(sK0,sK1,sK2)) )
    | ~ spl7_73 ),
    inference(avatar_component_clause,[],[f576])).

fof(f578,plain,
    ( spl7_73
    | ~ spl7_15
    | ~ spl7_49 ),
    inference(avatar_split_clause,[],[f313,f306,f117,f576])).

fof(f306,plain,
    ( spl7_49
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ r1_orders_2(sK0,X0,sK6(sK0,sK1,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_49])])).

fof(f313,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK6(sK0,sK1,X0),sK6(sK0,sK1,sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattice3(sK0,sK1,X0) )
    | ~ spl7_15
    | ~ spl7_49 ),
    inference(resolution,[],[f307,f118])).

fof(f307,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ r1_orders_2(sK0,X0,sK6(sK0,sK1,sK2)) )
    | ~ spl7_49 ),
    inference(avatar_component_clause,[],[f306])).

fof(f531,plain,
    ( spl7_7
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_17
    | spl7_68 ),
    inference(avatar_split_clause,[],[f517,f495,f126,f78,f74,f82])).

fof(f126,plain,
    ( spl7_17
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattice3(sK0,X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | m1_subset_1(sK6(sK0,X1,X0),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f517,plain,
    ( r1_lattice3(sK0,sK1,sK2)
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_17
    | spl7_68 ),
    inference(subsumption_resolution,[],[f516,f75])).

fof(f516,plain,
    ( r1_lattice3(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl7_6
    | ~ spl7_17
    | spl7_68 ),
    inference(subsumption_resolution,[],[f505,f79])).

fof(f505,plain,
    ( r1_lattice3(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl7_17
    | spl7_68 ),
    inference(resolution,[],[f496,f127])).

fof(f127,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(sK6(sK0,X1,X0),X2)
        | r1_lattice3(sK0,X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f126])).

fof(f496,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK0))
    | spl7_68 ),
    inference(avatar_component_clause,[],[f495])).

fof(f487,plain,
    ( spl7_67
    | ~ spl7_5
    | spl7_8
    | ~ spl7_55 ),
    inference(avatar_split_clause,[],[f470,f349,f85,f74,f485])).

fof(f349,plain,
    ( spl7_55
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ r1_orders_2(sK0,X0,sK6(sK0,X2,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_lattice3(sK0,X2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_55])])).

fof(f470,plain,
    ( ! [X1] :
        ( ~ r1_orders_2(sK0,sK2,X1)
        | ~ r1_orders_2(sK0,X1,sK6(sK0,k4_waybel_0(sK0,sK1),sK2))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl7_5
    | spl7_8
    | ~ spl7_55 ),
    inference(subsumption_resolution,[],[f469,f75])).

fof(f469,plain,
    ( ! [X1] :
        ( ~ r1_orders_2(sK0,sK2,X1)
        | ~ r1_orders_2(sK0,X1,sK6(sK0,k4_waybel_0(sK0,sK1),sK2))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | spl7_8
    | ~ spl7_55 ),
    inference(resolution,[],[f89,f350])).

fof(f350,plain,
    ( ! [X2,X0,X1] :
        ( r1_lattice3(sK0,X2,X1)
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ r1_orders_2(sK0,X0,sK6(sK0,X2,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_55 ),
    inference(avatar_component_clause,[],[f349])).

fof(f419,plain,
    ( spl7_62
    | ~ spl7_5
    | ~ spl7_7
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f412,f139,f82,f74,f417])).

fof(f139,plain,
    ( spl7_20
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,X2)
        | r1_orders_2(sK0,X0,X1)
        | ~ r1_lattice3(sK0,X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f412,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1)
        | r1_orders_2(sK0,sK2,X0) )
    | ~ spl7_5
    | ~ spl7_7
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f411,f75])).

fof(f411,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1)
        | r1_orders_2(sK0,sK2,X0)
        | ~ m1_subset_1(sK2,u1_struct_0(sK0)) )
    | ~ spl7_7
    | ~ spl7_20 ),
    inference(resolution,[],[f83,f140])).

fof(f140,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_lattice3(sK0,X2,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,X2)
        | r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f139])).

fof(f83,plain,
    ( r1_lattice3(sK0,sK1,sK2)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f82])).

fof(f351,plain,
    ( spl7_55
    | ~ spl7_4
    | ~ spl7_13
    | ~ spl7_50 ),
    inference(avatar_split_clause,[],[f322,f310,f108,f70,f349])).

fof(f108,plain,
    ( spl7_13
  <=> ! [X1,X0,X2] :
        ( ~ l1_orders_2(X0)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
        | r1_lattice3(X0,X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f310,plain,
    ( spl7_50
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK6(sK0,X1,X2),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,X0)
        | ~ r1_orders_2(sK0,X0,sK6(sK0,X1,X2))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_lattice3(sK0,X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_50])])).

fof(f322,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ r1_orders_2(sK0,X0,sK6(sK0,X2,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_lattice3(sK0,X2,X1) )
    | ~ spl7_4
    | ~ spl7_13
    | ~ spl7_50 ),
    inference(subsumption_resolution,[],[f321,f71])).

fof(f321,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ r1_orders_2(sK0,X0,sK6(sK0,X2,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_lattice3(sK0,X2,X1)
        | ~ l1_orders_2(sK0) )
    | ~ spl7_13
    | ~ spl7_50 ),
    inference(duplicate_literal_removal,[],[f318])).

fof(f318,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ r1_orders_2(sK0,X0,sK6(sK0,X2,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_lattice3(sK0,X2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | r1_lattice3(sK0,X2,X1) )
    | ~ spl7_13
    | ~ spl7_50 ),
    inference(resolution,[],[f311,f109])).

fof(f109,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ l1_orders_2(X0)
        | r1_lattice3(X0,X1,X2) )
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f108])).

fof(f311,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK6(sK0,X1,X2),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,X0)
        | ~ r1_orders_2(sK0,X0,sK6(sK0,X1,X2))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_lattice3(sK0,X1,X2) )
    | ~ spl7_50 ),
    inference(avatar_component_clause,[],[f310])).

fof(f312,plain,
    ( spl7_50
    | ~ spl7_4
    | ~ spl7_14
    | ~ spl7_39 ),
    inference(avatar_split_clause,[],[f252,f243,f112,f70,f310])).

fof(f112,plain,
    ( spl7_14
  <=> ! [X1,X0,X2] :
        ( ~ l1_orders_2(X0)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ r1_orders_2(X0,X2,sK6(X0,X1,X2))
        | r1_lattice3(X0,X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f243,plain,
    ( spl7_39
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ r1_orders_2(sK0,X1,X2)
        | r1_orders_2(sK0,X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).

fof(f252,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK6(sK0,X1,X2),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,X0)
        | ~ r1_orders_2(sK0,X0,sK6(sK0,X1,X2))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_lattice3(sK0,X1,X2) )
    | ~ spl7_4
    | ~ spl7_14
    | ~ spl7_39 ),
    inference(subsumption_resolution,[],[f251,f71])).

fof(f251,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK6(sK0,X1,X2),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,X0)
        | ~ r1_orders_2(sK0,X0,sK6(sK0,X1,X2))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | r1_lattice3(sK0,X1,X2) )
    | ~ spl7_14
    | ~ spl7_39 ),
    inference(duplicate_literal_removal,[],[f250])).

fof(f250,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK6(sK0,X1,X2),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,X0)
        | ~ r1_orders_2(sK0,X0,sK6(sK0,X1,X2))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | r1_lattice3(sK0,X1,X2) )
    | ~ spl7_14
    | ~ spl7_39 ),
    inference(resolution,[],[f244,f113])).

fof(f113,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_orders_2(X0,X2,sK6(X0,X1,X2))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ l1_orders_2(X0)
        | r1_lattice3(X0,X1,X2) )
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f112])).

fof(f244,plain,
    ( ! [X2,X0,X1] :
        ( r1_orders_2(sK0,X0,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ r1_orders_2(sK0,X1,X2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_39 ),
    inference(avatar_component_clause,[],[f243])).

fof(f308,plain,
    ( spl7_49
    | spl7_7
    | ~ spl7_47 ),
    inference(avatar_split_clause,[],[f296,f292,f82,f306])).

fof(f292,plain,
    ( spl7_47
  <=> ! [X1,X0] :
        ( ~ r1_orders_2(sK0,X0,sK6(sK0,X1,sK2))
        | ~ r2_hidden(X0,sK1)
        | r1_lattice3(sK0,X1,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).

fof(f296,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ r1_orders_2(sK0,X0,sK6(sK0,sK1,sK2)) )
    | spl7_7
    | ~ spl7_47 ),
    inference(resolution,[],[f293,f88])).

fof(f293,plain,
    ( ! [X0,X1] :
        ( r1_lattice3(sK0,X1,sK2)
        | ~ r2_hidden(X0,sK1)
        | ~ r1_orders_2(sK0,X0,sK6(sK0,X1,sK2)) )
    | ~ spl7_47 ),
    inference(avatar_component_clause,[],[f292])).

fof(f294,plain,
    ( spl7_47
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_13
    | ~ spl7_44 ),
    inference(avatar_split_clause,[],[f285,f273,f108,f74,f70,f292])).

fof(f273,plain,
    ( spl7_44
  <=> ! [X5,X4] :
        ( ~ m1_subset_1(sK6(sK0,X4,sK2),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X5,sK6(sK0,X4,sK2))
        | ~ r2_hidden(X5,sK1)
        | r1_lattice3(sK0,X4,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f285,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,sK6(sK0,X1,sK2))
        | ~ r2_hidden(X0,sK1)
        | r1_lattice3(sK0,X1,sK2) )
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_13
    | ~ spl7_44 ),
    inference(subsumption_resolution,[],[f284,f71])).

fof(f284,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,sK6(sK0,X1,sK2))
        | ~ r2_hidden(X0,sK1)
        | r1_lattice3(sK0,X1,sK2)
        | ~ l1_orders_2(sK0) )
    | ~ spl7_5
    | ~ spl7_13
    | ~ spl7_44 ),
    inference(subsumption_resolution,[],[f283,f75])).

fof(f283,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,sK6(sK0,X1,sK2))
        | ~ r2_hidden(X0,sK1)
        | r1_lattice3(sK0,X1,sK2)
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl7_13
    | ~ spl7_44 ),
    inference(duplicate_literal_removal,[],[f280])).

fof(f280,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,sK6(sK0,X1,sK2))
        | ~ r2_hidden(X0,sK1)
        | r1_lattice3(sK0,X1,sK2)
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | r1_lattice3(sK0,X1,sK2) )
    | ~ spl7_13
    | ~ spl7_44 ),
    inference(resolution,[],[f274,f109])).

fof(f274,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(sK6(sK0,X4,sK2),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X5,sK6(sK0,X4,sK2))
        | ~ r2_hidden(X5,sK1)
        | r1_lattice3(sK0,X4,sK2) )
    | ~ spl7_44 ),
    inference(avatar_component_clause,[],[f273])).

fof(f275,plain,
    ( spl7_44
    | ~ spl7_6
    | ~ spl7_34
    | ~ spl7_41 ),
    inference(avatar_split_clause,[],[f266,f255,f216,f78,f273])).

fof(f216,plain,
    ( spl7_34
  <=> ! [X0] :
        ( ~ r2_hidden(sK6(sK0,X0,sK2),k4_waybel_0(sK0,sK1))
        | ~ m1_subset_1(sK6(sK0,X0,sK2),u1_struct_0(sK0))
        | r1_lattice3(sK0,X0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f255,plain,
    ( spl7_41
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,X1)
        | ~ r2_hidden(X2,X0)
        | r2_hidden(X1,k4_waybel_0(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).

fof(f266,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(sK6(sK0,X4,sK2),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X5,sK6(sK0,X4,sK2))
        | ~ r2_hidden(X5,sK1)
        | r1_lattice3(sK0,X4,sK2) )
    | ~ spl7_6
    | ~ spl7_34
    | ~ spl7_41 ),
    inference(subsumption_resolution,[],[f265,f79])).

fof(f265,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(sK6(sK0,X4,sK2),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X5,sK6(sK0,X4,sK2))
        | ~ r2_hidden(X5,sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_lattice3(sK0,X4,sK2) )
    | ~ spl7_34
    | ~ spl7_41 ),
    inference(duplicate_literal_removal,[],[f264])).

fof(f264,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(sK6(sK0,X4,sK2),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X5,sK6(sK0,X4,sK2))
        | ~ r2_hidden(X5,sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK6(sK0,X4,sK2),u1_struct_0(sK0))
        | r1_lattice3(sK0,X4,sK2) )
    | ~ spl7_34
    | ~ spl7_41 ),
    inference(resolution,[],[f256,f217])).

fof(f217,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK6(sK0,X0,sK2),k4_waybel_0(sK0,sK1))
        | ~ m1_subset_1(sK6(sK0,X0,sK2),u1_struct_0(sK0))
        | r1_lattice3(sK0,X0,sK2) )
    | ~ spl7_34 ),
    inference(avatar_component_clause,[],[f216])).

fof(f256,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(X1,k4_waybel_0(sK0,X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,X1)
        | ~ r2_hidden(X2,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_41 ),
    inference(avatar_component_clause,[],[f255])).

fof(f257,plain,
    ( spl7_41
    | ~ spl7_4
    | ~ spl7_40 ),
    inference(avatar_split_clause,[],[f253,f247,f70,f255])).

fof(f247,plain,
    ( spl7_40
  <=> ! [X1,X3,X0,X4] :
        ( ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X3,u1_struct_0(X0))
        | ~ r1_orders_2(X0,X4,X3)
        | ~ r2_hidden(X4,X1)
        | r2_hidden(X3,k4_waybel_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).

% (9852)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
fof(f253,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,X1)
        | ~ r2_hidden(X2,X0)
        | r2_hidden(X1,k4_waybel_0(sK0,X0)) )
    | ~ spl7_4
    | ~ spl7_40 ),
    inference(resolution,[],[f248,f71])).

fof(f248,plain,
    ( ! [X4,X0,X3,X1] :
        ( ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X3,u1_struct_0(X0))
        | ~ r1_orders_2(X0,X4,X3)
        | ~ r2_hidden(X4,X1)
        | r2_hidden(X3,k4_waybel_0(X0,X1)) )
    | ~ spl7_40 ),
    inference(avatar_component_clause,[],[f247])).

fof(f249,plain,
    ( spl7_40
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_38 ),
    inference(avatar_split_clause,[],[f241,f237,f96,f92,f247])).

fof(f92,plain,
    ( spl7_9
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | m1_subset_1(X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f96,plain,
    ( spl7_10
  <=> ! [X1,X0] :
        ( ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f237,plain,
    ( spl7_38
  <=> ! [X1,X3,X0,X4] :
        ( ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X3,u1_struct_0(X0))
        | ~ m1_subset_1(X4,u1_struct_0(X0))
        | ~ r1_orders_2(X0,X4,X3)
        | ~ r2_hidden(X4,X1)
        | r2_hidden(X3,k4_waybel_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f241,plain,
    ( ! [X4,X0,X3,X1] :
        ( ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X3,u1_struct_0(X0))
        | ~ r1_orders_2(X0,X4,X3)
        | ~ r2_hidden(X4,X1)
        | r2_hidden(X3,k4_waybel_0(X0,X1)) )
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_38 ),
    inference(subsumption_resolution,[],[f240,f97])).

fof(f97,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_orders_2(X0) )
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f96])).

fof(f240,plain,
    ( ! [X4,X0,X3,X1] :
        ( ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X3,u1_struct_0(X0))
        | ~ r1_orders_2(X0,X4,X3)
        | ~ r2_hidden(X4,X1)
        | r2_hidden(X3,k4_waybel_0(X0,X1)) )
    | ~ spl7_9
    | ~ spl7_38 ),
    inference(subsumption_resolution,[],[f238,f93])).

fof(f93,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | m1_subset_1(X0,X2) )
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f92])).

fof(f238,plain,
    ( ! [X4,X0,X3,X1] :
        ( ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X3,u1_struct_0(X0))
        | ~ m1_subset_1(X4,u1_struct_0(X0))
        | ~ r1_orders_2(X0,X4,X3)
        | ~ r2_hidden(X4,X1)
        | r2_hidden(X3,k4_waybel_0(X0,X1)) )
    | ~ spl7_38 ),
    inference(avatar_component_clause,[],[f237])).

fof(f245,plain,
    ( spl7_39
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_23 ),
    inference(avatar_split_clause,[],[f189,f159,f70,f66,f243])).

fof(f66,plain,
    ( spl7_3
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f159,plain,
    ( spl7_23
  <=> ! [X1,X3,X0,X2] :
        ( ~ v4_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X3,u1_struct_0(X0))
        | ~ r1_orders_2(X0,X1,X2)
        | ~ r1_orders_2(X0,X2,X3)
        | r1_orders_2(X0,X1,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f189,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ r1_orders_2(sK0,X1,X2)
        | r1_orders_2(sK0,X0,X2) )
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f188,f71])).

fof(f188,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ r1_orders_2(sK0,X1,X2)
        | r1_orders_2(sK0,X0,X2) )
    | ~ spl7_3
    | ~ spl7_23 ),
    inference(resolution,[],[f160,f67])).

fof(f67,plain,
    ( v4_orders_2(sK0)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f160,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v4_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X3,u1_struct_0(X0))
        | ~ r1_orders_2(X0,X1,X2)
        | ~ r1_orders_2(X0,X2,X3)
        | r1_orders_2(X0,X1,X3) )
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f159])).

fof(f239,plain,(
    spl7_38 ),
    inference(avatar_split_clause,[],[f52,f237])).

fof(f52,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X4,X3)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,k4_waybel_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X4,X3)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,X2)
      | k4_waybel_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_waybel_0(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ? [X4] :
                          ( r2_hidden(X4,X1)
                          & r1_orders_2(X0,X4,X3)
                          & m1_subset_1(X4,u1_struct_0(X0)) ) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k4_waybel_0(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_hidden(X3,X2)
                    <=> ? [X4] :
                          ( r2_hidden(X4,X1)
                          & r1_orders_2(X0,X4,X3)
                          & m1_subset_1(X4,u1_struct_0(X0)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_waybel_0)).

fof(f222,plain,
    ( spl7_35
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_33 ),
    inference(avatar_split_clause,[],[f214,f210,f96,f92,f220])).

fof(f210,plain,
    ( spl7_33
  <=> ! [X1,X3,X0] :
        ( ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X3,u1_struct_0(X0))
        | m1_subset_1(sK5(X0,X1,X3),u1_struct_0(X0))
        | ~ r2_hidden(X3,k4_waybel_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f214,plain,
    ( ! [X0,X3,X1] :
        ( ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | m1_subset_1(sK5(X0,X1,X3),u1_struct_0(X0))
        | ~ r2_hidden(X3,k4_waybel_0(X0,X1)) )
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_33 ),
    inference(subsumption_resolution,[],[f213,f97])).

fof(f213,plain,
    ( ! [X0,X3,X1] :
        ( ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | m1_subset_1(sK5(X0,X1,X3),u1_struct_0(X0))
        | ~ r2_hidden(X3,k4_waybel_0(X0,X1)) )
    | ~ spl7_9
    | ~ spl7_33 ),
    inference(subsumption_resolution,[],[f211,f93])).

fof(f211,plain,
    ( ! [X0,X3,X1] :
        ( ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X3,u1_struct_0(X0))
        | m1_subset_1(sK5(X0,X1,X3),u1_struct_0(X0))
        | ~ r2_hidden(X3,k4_waybel_0(X0,X1)) )
    | ~ spl7_33 ),
    inference(avatar_component_clause,[],[f210])).

fof(f218,plain,
    ( spl7_34
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_14
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f157,f152,f112,f74,f70,f216])).

fof(f152,plain,
    ( spl7_22
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k4_waybel_0(sK0,sK1))
        | r1_orders_2(sK0,sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f157,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK6(sK0,X0,sK2),k4_waybel_0(sK0,sK1))
        | ~ m1_subset_1(sK6(sK0,X0,sK2),u1_struct_0(sK0))
        | r1_lattice3(sK0,X0,sK2) )
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_14
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f156,f71])).

fof(f156,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK6(sK0,X0,sK2),k4_waybel_0(sK0,sK1))
        | ~ m1_subset_1(sK6(sK0,X0,sK2),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | r1_lattice3(sK0,X0,sK2) )
    | ~ spl7_5
    | ~ spl7_14
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f155,f75])).

fof(f155,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK6(sK0,X0,sK2),k4_waybel_0(sK0,sK1))
        | ~ m1_subset_1(sK6(sK0,X0,sK2),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | r1_lattice3(sK0,X0,sK2) )
    | ~ spl7_14
    | ~ spl7_22 ),
    inference(resolution,[],[f153,f113])).

fof(f153,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK2,X0)
        | ~ r2_hidden(X0,k4_waybel_0(sK0,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f152])).

fof(f212,plain,(
    spl7_33 ),
    inference(avatar_split_clause,[],[f55,f210])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | m1_subset_1(sK5(X0,X1,X3),u1_struct_0(X0))
      | ~ r2_hidden(X3,k4_waybel_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | m1_subset_1(sK5(X0,X1,X3),u1_struct_0(X0))
      | ~ r2_hidden(X3,X2)
      | k4_waybel_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f208,plain,
    ( spl7_32
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_30 ),
    inference(avatar_split_clause,[],[f200,f196,f96,f92,f206])).

fof(f196,plain,
    ( spl7_30
  <=> ! [X1,X3,X0] :
        ( ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X3,u1_struct_0(X0))
        | r1_orders_2(X0,sK5(X0,X1,X3),X3)
        | ~ r2_hidden(X3,k4_waybel_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f200,plain,
    ( ! [X0,X3,X1] :
        ( ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | r1_orders_2(X0,sK5(X0,X1,X3),X3)
        | ~ r2_hidden(X3,k4_waybel_0(X0,X1)) )
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_30 ),
    inference(subsumption_resolution,[],[f199,f97])).

fof(f199,plain,
    ( ! [X0,X3,X1] :
        ( ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | r1_orders_2(X0,sK5(X0,X1,X3),X3)
        | ~ r2_hidden(X3,k4_waybel_0(X0,X1)) )
    | ~ spl7_9
    | ~ spl7_30 ),
    inference(subsumption_resolution,[],[f197,f93])).

fof(f197,plain,
    ( ! [X0,X3,X1] :
        ( ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X3,u1_struct_0(X0))
        | r1_orders_2(X0,sK5(X0,X1,X3),X3)
        | ~ r2_hidden(X3,k4_waybel_0(X0,X1)) )
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f196])).

fof(f198,plain,(
    spl7_30 ),
    inference(avatar_split_clause,[],[f54,f196])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_orders_2(X0,sK5(X0,X1,X3),X3)
      | ~ r2_hidden(X3,k4_waybel_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f34])).

% (9844)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_orders_2(X0,sK5(X0,X1,X3),X3)
      | ~ r2_hidden(X3,X2)
      | k4_waybel_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f187,plain,
    ( spl7_28
    | ~ spl7_4
    | ~ spl7_27 ),
    inference(avatar_split_clause,[],[f183,f180,f70,f185])).

fof(f180,plain,
    ( spl7_27
  <=> ! [X1,X3,X0] :
        ( ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | r2_hidden(sK5(X0,X1,X3),X1)
        | ~ r2_hidden(X3,k4_waybel_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f183,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(sK5(sK0,X0,X1),X0)
        | ~ r2_hidden(X1,k4_waybel_0(sK0,X0)) )
    | ~ spl7_4
    | ~ spl7_27 ),
    inference(resolution,[],[f181,f71])).

fof(f181,plain,
    ( ! [X0,X3,X1] :
        ( ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | r2_hidden(sK5(X0,X1,X3),X1)
        | ~ r2_hidden(X3,k4_waybel_0(X0,X1)) )
    | ~ spl7_27 ),
    inference(avatar_component_clause,[],[f180])).

fof(f182,plain,
    ( spl7_27
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f175,f171,f96,f92,f180])).

fof(f171,plain,
    ( spl7_26
  <=> ! [X1,X3,X0] :
        ( ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X3,u1_struct_0(X0))
        | r2_hidden(sK5(X0,X1,X3),X1)
        | ~ r2_hidden(X3,k4_waybel_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f175,plain,
    ( ! [X0,X3,X1] :
        ( ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | r2_hidden(sK5(X0,X1,X3),X1)
        | ~ r2_hidden(X3,k4_waybel_0(X0,X1)) )
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f174,f97])).

fof(f174,plain,
    ( ! [X0,X3,X1] :
        ( ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | r2_hidden(sK5(X0,X1,X3),X1)
        | ~ r2_hidden(X3,k4_waybel_0(X0,X1)) )
    | ~ spl7_9
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f172,f93])).

fof(f172,plain,
    ( ! [X0,X3,X1] :
        ( ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X3,u1_struct_0(X0))
        | r2_hidden(sK5(X0,X1,X3),X1)
        | ~ r2_hidden(X3,k4_waybel_0(X0,X1)) )
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f171])).

fof(f173,plain,(
    spl7_26 ),
    inference(avatar_split_clause,[],[f53,f171])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r2_hidden(sK5(X0,X1,X3),X1)
      | ~ r2_hidden(X3,k4_waybel_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r2_hidden(sK5(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k4_waybel_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f169,plain,
    ( spl7_25
    | spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_19 ),
    inference(avatar_split_clause,[],[f146,f134,f70,f62,f58,f167])).

fof(f134,plain,
    ( spl7_19
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ v3_orders_2(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | r1_orders_2(X0,X1,X2)
        | ~ r3_orders_2(X0,X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f146,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,X1)
        | ~ r3_orders_2(sK0,X0,X1) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_19 ),
    inference(subsumption_resolution,[],[f145,f71])).

fof(f145,plain,
    ( ! [X0,X1] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,X1)
        | ~ r3_orders_2(sK0,X0,X1) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_19 ),
    inference(subsumption_resolution,[],[f144,f59])).

fof(f144,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,X1)
        | ~ r3_orders_2(sK0,X0,X1) )
    | ~ spl7_2
    | ~ spl7_19 ),
    inference(resolution,[],[f135,f63])).

fof(f135,plain,
    ( ! [X2,X0,X1] :
        ( ~ v3_orders_2(X0)
        | v2_struct_0(X0)
        | ~ l1_orders_2(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | r1_orders_2(X0,X1,X2)
        | ~ r3_orders_2(X0,X1,X2) )
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f134])).

fof(f161,plain,(
    spl7_23 ),
    inference(avatar_split_clause,[],[f46,f159])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v4_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ r1_orders_2(X0,X2,X3)
      | r1_orders_2(X0,X1,X3) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X1,X3)
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f15])).

% (9859)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X1,X3)
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X2) )
                   => r1_orders_2(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_orders_2)).

fof(f154,plain,
    ( spl7_22
    | ~ spl7_5
    | ~ spl7_8
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f143,f139,f85,f74,f152])).

fof(f143,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k4_waybel_0(sK0,sK1))
        | r1_orders_2(sK0,sK2,X0) )
    | ~ spl7_5
    | ~ spl7_8
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f142,f75])).

fof(f142,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k4_waybel_0(sK0,sK1))
        | r1_orders_2(sK0,sK2,X0)
        | ~ m1_subset_1(sK2,u1_struct_0(sK0)) )
    | ~ spl7_8
    | ~ spl7_20 ),
    inference(resolution,[],[f140,f86])).

fof(f86,plain,
    ( r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f85])).

fof(f141,plain,
    ( spl7_20
    | ~ spl7_4
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f137,f122,f70,f139])).

fof(f122,plain,
    ( spl7_16
  <=> ! [X1,X3,X0,X2] :
        ( ~ l1_orders_2(X0)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X3,u1_struct_0(X0))
        | ~ r2_hidden(X3,X1)
        | r1_orders_2(X0,X2,X3)
        | ~ r1_lattice3(X0,X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f137,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,X2)
        | r1_orders_2(sK0,X0,X1)
        | ~ r1_lattice3(sK0,X2,X0) )
    | ~ spl7_4
    | ~ spl7_16 ),
    inference(resolution,[],[f123,f71])).

fof(f123,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ l1_orders_2(X0)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X3,u1_struct_0(X0))
        | ~ r2_hidden(X3,X1)
        | r1_orders_2(X0,X2,X3)
        | ~ r1_lattice3(X0,X1,X2) )
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f122])).

fof(f136,plain,(
    spl7_19 ),
    inference(avatar_split_clause,[],[f50,f134])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

% (9860)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f128,plain,
    ( spl7_17
    | ~ spl7_9
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f120,f117,f92,f126])).

fof(f120,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattice3(sK0,X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | m1_subset_1(sK6(sK0,X1,X0),X2) )
    | ~ spl7_9
    | ~ spl7_15 ),
    inference(resolution,[],[f118,f93])).

fof(f124,plain,(
    spl7_16 ),
    inference(avatar_split_clause,[],[f42,f122])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X3,X1)
      | r1_orders_2(X0,X2,X3)
      | ~ r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

% (9841)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattice3)).

fof(f119,plain,
    ( spl7_15
    | ~ spl7_4
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f115,f104,f70,f117])).

fof(f104,plain,
    ( spl7_12
  <=> ! [X1,X0,X2] :
        ( ~ l1_orders_2(X0)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | r2_hidden(sK6(X0,X1,X2),X1)
        | r1_lattice3(X0,X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f115,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(sK6(sK0,X1,X0),X1)
        | r1_lattice3(sK0,X1,X0) )
    | ~ spl7_4
    | ~ spl7_12 ),
    inference(resolution,[],[f105,f71])).

fof(f105,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_orders_2(X0)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | r2_hidden(sK6(X0,X1,X2),X1)
        | r1_lattice3(X0,X1,X2) )
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f104])).

fof(f114,plain,(
    spl7_14 ),
    inference(avatar_split_clause,[],[f45,f112])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X2,sK6(X0,X1,X2))
      | r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f110,plain,(
    spl7_13 ),
    inference(avatar_split_clause,[],[f43,f108])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
      | r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f106,plain,(
    spl7_12 ),
    inference(avatar_split_clause,[],[f44,f104])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(sK6(X0,X1,X2),X1)
      | r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f102,plain,(
    spl7_11 ),
    inference(avatar_split_clause,[],[f56,f100])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ v3_orders_2(X1)
      | ~ l1_orders_2(X1)
      | r3_orders_2(X1,X0,X0) ) ),
    inference(condensation,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r3_orders_2(X0,X1,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r3_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

fof(f98,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f47,f96])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0) )
     => m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_waybel_0)).

fof(f94,plain,(
    spl7_9 ),
    inference(avatar_split_clause,[],[f51,f92])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f90,plain,
    ( ~ spl7_7
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f26,f85,f82])).

fof(f26,plain,
    ( ~ r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)
    | ~ r1_lattice3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_lattice3(X0,X1,X2)
              <~> r1_lattice3(X0,k4_waybel_0(X0,X1),X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_lattice3(X0,X1,X2)
              <~> r1_lattice3(X0,k4_waybel_0(X0,X1),X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_waybel_0)).

fof(f87,plain,
    ( spl7_7
    | spl7_8 ),
    inference(avatar_split_clause,[],[f25,f85,f82])).

fof(f25,plain,
    ( r1_lattice3(sK0,k4_waybel_0(sK0,sK1),sK2)
    | r1_lattice3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f80,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f28,f78])).

fof(f28,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f76,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f27,f74])).

fof(f27,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f72,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f32,f70])).

fof(f32,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f68,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f31,f66])).

fof(f31,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f11])).

% (9843)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
fof(f64,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f30,f62])).

fof(f30,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f60,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f29,f58])).

fof(f29,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f11])).

%------------------------------------------------------------------------------
