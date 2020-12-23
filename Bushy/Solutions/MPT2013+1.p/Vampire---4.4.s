%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_9__t12_waybel_9.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:08 EDT 2019

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :  196 ( 528 expanded)
%              Number of leaves         :   32 ( 170 expanded)
%              Depth                    :   18
%              Number of atoms          :  981 (2488 expanded)
%              Number of equality atoms :   53 ( 196 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f469,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f169,f176,f183,f190,f197,f204,f211,f226,f239,f249,f275,f282,f296,f303,f308,f321,f372,f405,f441,f449,f468])).

fof(f468,plain,
    ( spl11_1
    | spl11_3
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_26
    | spl11_29
    | ~ spl11_32 ),
    inference(avatar_contradiction_clause,[],[f467])).

fof(f467,plain,
    ( $false
    | ~ spl11_1
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_26
    | ~ spl11_29
    | ~ spl11_32 ),
    inference(subsumption_resolution,[],[f466,f175])).

fof(f175,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl11_3 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl11_3
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f466,plain,
    ( v2_struct_0(sK0)
    | ~ spl11_1
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_26
    | ~ spl11_29
    | ~ spl11_32 ),
    inference(subsumption_resolution,[],[f465,f356])).

fof(f356,plain,
    ( r1_orders_2(sK1,sK2,sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))))
    | ~ spl11_1
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_26 ),
    inference(forward_demodulation,[],[f355,f336])).

fof(f336,plain,
    ( sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) = sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))),sK1,sK2)
    | ~ spl11_1
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_26 ),
    inference(subsumption_resolution,[],[f335,f175])).

fof(f335,plain,
    ( sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) = sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))),sK1,sK2)
    | v2_struct_0(sK0)
    | ~ spl11_1
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_26 ),
    inference(subsumption_resolution,[],[f334,f196])).

fof(f196,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl11_8
  <=> m1_subset_1(sK2,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f334,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) = sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))),sK1,sK2)
    | v2_struct_0(sK0)
    | ~ spl11_1
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_26 ),
    inference(subsumption_resolution,[],[f333,f189])).

fof(f189,plain,
    ( l1_waybel_0(sK1,sK0)
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl11_6
  <=> l1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f333,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) = sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))),sK1,sK2)
    | v2_struct_0(sK0)
    | ~ spl11_1
    | ~ spl11_4
    | ~ spl11_26 ),
    inference(subsumption_resolution,[],[f332,f168])).

fof(f168,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl11_1
  <=> ~ v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f332,plain,
    ( v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) = sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))),sK1,sK2)
    | v2_struct_0(sK0)
    | ~ spl11_4
    | ~ spl11_26 ),
    inference(subsumption_resolution,[],[f328,f182])).

fof(f182,plain,
    ( l1_struct_0(sK0)
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl11_4
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f328,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) = sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))),sK1,sK2)
    | v2_struct_0(sK0)
    | ~ spl11_26 ),
    inference(resolution,[],[f106,f286])).

fof(f286,plain,
    ( r2_hidden(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))),a_3_0_waybel_9(sK0,sK1,sK2))
    | ~ spl11_26 ),
    inference(avatar_component_clause,[],[f285])).

fof(f285,plain,
    ( spl11_26
  <=> r2_hidden(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))),a_3_0_waybel_9(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_26])])).

fof(f106,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X2)
      | ~ l1_waybel_0(X2,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | sK4(X0,X2,X3) = X0
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
      <=> ? [X4] :
            ( r1_orders_2(X2,X3,X4)
            & X0 = X4
            & m1_subset_1(X4,u1_struct_0(X2)) ) )
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
      <=> ? [X4] :
            ( r1_orders_2(X2,X3,X4)
            & X0 = X4
            & m1_subset_1(X4,u1_struct_0(X2)) ) )
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,u1_struct_0(X2))
        & l1_waybel_0(X2,X1)
        & ~ v2_struct_0(X2)
        & l1_struct_0(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
      <=> ? [X4] :
            ( r1_orders_2(X2,X3,X4)
            & X0 = X4
            & m1_subset_1(X4,u1_struct_0(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t12_waybel_9.p',fraenkel_a_3_0_waybel_9)).

fof(f355,plain,
    ( r1_orders_2(sK1,sK2,sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))),sK1,sK2))
    | ~ spl11_1
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_26 ),
    inference(subsumption_resolution,[],[f354,f175])).

fof(f354,plain,
    ( r1_orders_2(sK1,sK2,sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))),sK1,sK2))
    | v2_struct_0(sK0)
    | ~ spl11_1
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_26 ),
    inference(subsumption_resolution,[],[f353,f196])).

fof(f353,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | r1_orders_2(sK1,sK2,sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))),sK1,sK2))
    | v2_struct_0(sK0)
    | ~ spl11_1
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_26 ),
    inference(subsumption_resolution,[],[f352,f189])).

fof(f352,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | r1_orders_2(sK1,sK2,sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))),sK1,sK2))
    | v2_struct_0(sK0)
    | ~ spl11_1
    | ~ spl11_4
    | ~ spl11_26 ),
    inference(subsumption_resolution,[],[f351,f168])).

fof(f351,plain,
    ( v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | r1_orders_2(sK1,sK2,sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))),sK1,sK2))
    | v2_struct_0(sK0)
    | ~ spl11_4
    | ~ spl11_26 ),
    inference(subsumption_resolution,[],[f347,f182])).

fof(f347,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | r1_orders_2(sK1,sK2,sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))),sK1,sK2))
    | v2_struct_0(sK0)
    | ~ spl11_26 ),
    inference(resolution,[],[f107,f286])).

fof(f107,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X2)
      | ~ l1_waybel_0(X2,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | r1_orders_2(X2,X3,sK4(X0,X2,X3))
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f465,plain,
    ( ~ r1_orders_2(sK1,sK2,sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))))
    | v2_struct_0(sK0)
    | ~ spl11_1
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_29
    | ~ spl11_32 ),
    inference(subsumption_resolution,[],[f464,f371])).

fof(f371,plain,
    ( m1_subset_1(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))),u1_struct_0(sK1))
    | ~ spl11_32 ),
    inference(avatar_component_clause,[],[f370])).

fof(f370,plain,
    ( spl11_32
  <=> m1_subset_1(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_32])])).

fof(f464,plain,
    ( ~ m1_subset_1(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))),u1_struct_0(sK1))
    | ~ r1_orders_2(sK1,sK2,sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))))
    | v2_struct_0(sK0)
    | ~ spl11_1
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_29 ),
    inference(subsumption_resolution,[],[f463,f196])).

fof(f463,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))),u1_struct_0(sK1))
    | ~ r1_orders_2(sK1,sK2,sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))))
    | v2_struct_0(sK0)
    | ~ spl11_1
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_29 ),
    inference(subsumption_resolution,[],[f462,f189])).

fof(f462,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))),u1_struct_0(sK1))
    | ~ r1_orders_2(sK1,sK2,sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))))
    | v2_struct_0(sK0)
    | ~ spl11_1
    | ~ spl11_4
    | ~ spl11_29 ),
    inference(subsumption_resolution,[],[f461,f168])).

fof(f461,plain,
    ( v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))),u1_struct_0(sK1))
    | ~ r1_orders_2(sK1,sK2,sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))))
    | v2_struct_0(sK0)
    | ~ spl11_4
    | ~ spl11_29 ),
    inference(subsumption_resolution,[],[f455,f182])).

fof(f455,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))),u1_struct_0(sK1))
    | ~ r1_orders_2(sK1,sK2,sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))))
    | v2_struct_0(sK0)
    | ~ spl11_29 ),
    inference(resolution,[],[f156,f295])).

fof(f295,plain,
    ( ~ r2_hidden(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
    | ~ spl11_29 ),
    inference(avatar_component_clause,[],[f294])).

fof(f294,plain,
    ( spl11_29
  <=> ~ r2_hidden(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_29])])).

fof(f156,plain,(
    ! [X2,X0,X5,X1] :
      ( r2_hidden(X5,u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ r1_orders_2(X1,X2,X5)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f155,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
        & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
        & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
        & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t12_waybel_9.p',dt_k4_waybel_9)).

fof(f155,plain,(
    ! [X2,X0,X5,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ r1_orders_2(X1,X2,X5)
      | r2_hidden(X5,u1_struct_0(k4_waybel_9(X0,X1,X2))) ) ),
    inference(subsumption_resolution,[],[f146,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f146,plain,(
    ! [X2,X0,X5,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ r1_orders_2(X1,X2,X5)
      | r2_hidden(X5,u1_struct_0(k4_waybel_9(X0,X1,X2))) ) ),
    inference(equality_resolution,[],[f145])).

fof(f145,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ v6_waybel_0(X3,X0)
      | ~ l1_waybel_0(X3,X0)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ r1_orders_2(X1,X2,X5)
      | r2_hidden(X5,u1_struct_0(X3))
      | k4_waybel_9(X0,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f114])).

fof(f114,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ v6_waybel_0(X3,X0)
      | ~ l1_waybel_0(X3,X0)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | X4 != X5
      | ~ r1_orders_2(X1,X2,X5)
      | r2_hidden(X4,u1_struct_0(X3))
      | k4_waybel_9(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k4_waybel_9(X0,X1,X2) = X3
                  <=> ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                      & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                      & ! [X4] :
                          ( r2_hidden(X4,u1_struct_0(X3))
                        <=> ? [X5] :
                              ( r1_orders_2(X1,X2,X5)
                              & X4 = X5
                              & m1_subset_1(X5,u1_struct_0(X1)) ) ) ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k4_waybel_9(X0,X1,X2) = X3
                  <=> ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                      & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                      & ! [X4] :
                          ( r2_hidden(X4,u1_struct_0(X3))
                        <=> ? [X5] :
                              ( r1_orders_2(X1,X2,X5)
                              & X4 = X5
                              & m1_subset_1(X5,u1_struct_0(X1)) ) ) ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => ! [X3] :
                  ( ( l1_waybel_0(X3,X0)
                    & v6_waybel_0(X3,X0) )
                 => ( k4_waybel_9(X0,X1,X2) = X3
                  <=> ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                      & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                      & ! [X4] :
                          ( r2_hidden(X4,u1_struct_0(X3))
                        <=> ? [X5] :
                              ( r1_orders_2(X1,X2,X5)
                              & X4 = X5
                              & m1_subset_1(X5,u1_struct_0(X1)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t12_waybel_9.p',d7_waybel_9)).

fof(f449,plain,
    ( spl11_1
    | spl11_3
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | spl11_27
    | ~ spl11_28 ),
    inference(avatar_contradiction_clause,[],[f448])).

fof(f448,plain,
    ( $false
    | ~ spl11_1
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_27
    | ~ spl11_28 ),
    inference(subsumption_resolution,[],[f447,f175])).

fof(f447,plain,
    ( v2_struct_0(sK0)
    | ~ spl11_1
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_27
    | ~ spl11_28 ),
    inference(subsumption_resolution,[],[f446,f422])).

fof(f422,plain,
    ( r1_orders_2(sK1,sK2,sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))))
    | ~ spl11_1
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_28 ),
    inference(forward_demodulation,[],[f421,f383])).

fof(f383,plain,
    ( sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) = sK7(sK1,sK2,sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))))
    | ~ spl11_1
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_28 ),
    inference(subsumption_resolution,[],[f382,f175])).

fof(f382,plain,
    ( sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) = sK7(sK1,sK2,sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))))
    | v2_struct_0(sK0)
    | ~ spl11_1
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_28 ),
    inference(subsumption_resolution,[],[f381,f196])).

fof(f381,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) = sK7(sK1,sK2,sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))))
    | v2_struct_0(sK0)
    | ~ spl11_1
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_28 ),
    inference(subsumption_resolution,[],[f380,f189])).

fof(f380,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) = sK7(sK1,sK2,sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))))
    | v2_struct_0(sK0)
    | ~ spl11_1
    | ~ spl11_4
    | ~ spl11_28 ),
    inference(subsumption_resolution,[],[f379,f168])).

fof(f379,plain,
    ( v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) = sK7(sK1,sK2,sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))))
    | v2_struct_0(sK0)
    | ~ spl11_4
    | ~ spl11_28 ),
    inference(subsumption_resolution,[],[f376,f182])).

fof(f376,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) = sK7(sK1,sK2,sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))))
    | v2_struct_0(sK0)
    | ~ spl11_28 ),
    inference(resolution,[],[f292,f160])).

fof(f160,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | sK7(X1,X2,X4) = X4
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f159,f110])).

fof(f159,plain,(
    ! [X4,X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | sK7(X1,X2,X4) = X4
      | ~ r2_hidden(X4,u1_struct_0(k4_waybel_9(X0,X1,X2))) ) ),
    inference(subsumption_resolution,[],[f148,f109])).

fof(f148,plain,(
    ! [X4,X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | sK7(X1,X2,X4) = X4
      | ~ r2_hidden(X4,u1_struct_0(k4_waybel_9(X0,X1,X2))) ) ),
    inference(equality_resolution,[],[f112])).

fof(f112,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ v6_waybel_0(X3,X0)
      | ~ l1_waybel_0(X3,X0)
      | sK7(X1,X2,X4) = X4
      | ~ r2_hidden(X4,u1_struct_0(X3))
      | k4_waybel_9(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f65])).

fof(f292,plain,
    ( r2_hidden(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
    | ~ spl11_28 ),
    inference(avatar_component_clause,[],[f291])).

fof(f291,plain,
    ( spl11_28
  <=> r2_hidden(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_28])])).

fof(f421,plain,
    ( r1_orders_2(sK1,sK2,sK7(sK1,sK2,sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))))
    | ~ spl11_1
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_28 ),
    inference(subsumption_resolution,[],[f420,f175])).

fof(f420,plain,
    ( r1_orders_2(sK1,sK2,sK7(sK1,sK2,sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))))
    | v2_struct_0(sK0)
    | ~ spl11_1
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_28 ),
    inference(subsumption_resolution,[],[f419,f196])).

fof(f419,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | r1_orders_2(sK1,sK2,sK7(sK1,sK2,sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))))
    | v2_struct_0(sK0)
    | ~ spl11_1
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_28 ),
    inference(subsumption_resolution,[],[f418,f189])).

fof(f418,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | r1_orders_2(sK1,sK2,sK7(sK1,sK2,sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))))
    | v2_struct_0(sK0)
    | ~ spl11_1
    | ~ spl11_4
    | ~ spl11_28 ),
    inference(subsumption_resolution,[],[f417,f168])).

fof(f417,plain,
    ( v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | r1_orders_2(sK1,sK2,sK7(sK1,sK2,sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))))
    | v2_struct_0(sK0)
    | ~ spl11_4
    | ~ spl11_28 ),
    inference(subsumption_resolution,[],[f407,f182])).

fof(f407,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | r1_orders_2(sK1,sK2,sK7(sK1,sK2,sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))))
    | v2_struct_0(sK0)
    | ~ spl11_28 ),
    inference(resolution,[],[f158,f292])).

fof(f158,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | r1_orders_2(X1,X2,sK7(X1,X2,X4))
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f157,f110])).

fof(f157,plain,(
    ! [X4,X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | r1_orders_2(X1,X2,sK7(X1,X2,X4))
      | ~ r2_hidden(X4,u1_struct_0(k4_waybel_9(X0,X1,X2))) ) ),
    inference(subsumption_resolution,[],[f147,f109])).

fof(f147,plain,(
    ! [X4,X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | r1_orders_2(X1,X2,sK7(X1,X2,X4))
      | ~ r2_hidden(X4,u1_struct_0(k4_waybel_9(X0,X1,X2))) ) ),
    inference(equality_resolution,[],[f113])).

fof(f113,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ v6_waybel_0(X3,X0)
      | ~ l1_waybel_0(X3,X0)
      | r1_orders_2(X1,X2,sK7(X1,X2,X4))
      | ~ r2_hidden(X4,u1_struct_0(X3))
      | k4_waybel_9(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f65])).

fof(f446,plain,
    ( ~ r1_orders_2(sK1,sK2,sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))))
    | v2_struct_0(sK0)
    | ~ spl11_1
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_27
    | ~ spl11_28 ),
    inference(subsumption_resolution,[],[f445,f439])).

fof(f439,plain,
    ( m1_subset_1(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))),u1_struct_0(sK1))
    | ~ spl11_1
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_28 ),
    inference(forward_demodulation,[],[f438,f383])).

fof(f438,plain,
    ( m1_subset_1(sK7(sK1,sK2,sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))),u1_struct_0(sK1))
    | ~ spl11_1
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_28 ),
    inference(subsumption_resolution,[],[f437,f175])).

fof(f437,plain,
    ( m1_subset_1(sK7(sK1,sK2,sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | ~ spl11_1
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_28 ),
    inference(subsumption_resolution,[],[f436,f196])).

fof(f436,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | m1_subset_1(sK7(sK1,sK2,sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | ~ spl11_1
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_28 ),
    inference(subsumption_resolution,[],[f435,f189])).

fof(f435,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | m1_subset_1(sK7(sK1,sK2,sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | ~ spl11_1
    | ~ spl11_4
    | ~ spl11_28 ),
    inference(subsumption_resolution,[],[f434,f168])).

fof(f434,plain,
    ( v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | m1_subset_1(sK7(sK1,sK2,sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | ~ spl11_4
    | ~ spl11_28 ),
    inference(subsumption_resolution,[],[f424,f182])).

fof(f424,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | m1_subset_1(sK7(sK1,sK2,sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | ~ spl11_28 ),
    inference(resolution,[],[f162,f292])).

fof(f162,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,u1_struct_0(k4_waybel_9(X0,X1,X2)))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | m1_subset_1(sK7(X1,X2,X4),u1_struct_0(X1))
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f161,f110])).

fof(f161,plain,(
    ! [X4,X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | m1_subset_1(sK7(X1,X2,X4),u1_struct_0(X1))
      | ~ r2_hidden(X4,u1_struct_0(k4_waybel_9(X0,X1,X2))) ) ),
    inference(subsumption_resolution,[],[f149,f109])).

fof(f149,plain,(
    ! [X4,X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | m1_subset_1(sK7(X1,X2,X4),u1_struct_0(X1))
      | ~ r2_hidden(X4,u1_struct_0(k4_waybel_9(X0,X1,X2))) ) ),
    inference(equality_resolution,[],[f111])).

fof(f111,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ v6_waybel_0(X3,X0)
      | ~ l1_waybel_0(X3,X0)
      | m1_subset_1(sK7(X1,X2,X4),u1_struct_0(X1))
      | ~ r2_hidden(X4,u1_struct_0(X3))
      | k4_waybel_9(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f65])).

fof(f445,plain,
    ( ~ m1_subset_1(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))),u1_struct_0(sK1))
    | ~ r1_orders_2(sK1,sK2,sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))))
    | v2_struct_0(sK0)
    | ~ spl11_1
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_27 ),
    inference(subsumption_resolution,[],[f444,f196])).

fof(f444,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))),u1_struct_0(sK1))
    | ~ r1_orders_2(sK1,sK2,sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))))
    | v2_struct_0(sK0)
    | ~ spl11_1
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_27 ),
    inference(subsumption_resolution,[],[f443,f189])).

fof(f443,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))),u1_struct_0(sK1))
    | ~ r1_orders_2(sK1,sK2,sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))))
    | v2_struct_0(sK0)
    | ~ spl11_1
    | ~ spl11_4
    | ~ spl11_27 ),
    inference(subsumption_resolution,[],[f442,f168])).

fof(f442,plain,
    ( v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))),u1_struct_0(sK1))
    | ~ r1_orders_2(sK1,sK2,sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))))
    | v2_struct_0(sK0)
    | ~ spl11_4
    | ~ spl11_27 ),
    inference(subsumption_resolution,[],[f385,f182])).

fof(f385,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))),u1_struct_0(sK1))
    | ~ r1_orders_2(sK1,sK2,sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))))
    | v2_struct_0(sK0)
    | ~ spl11_27 ),
    inference(resolution,[],[f141,f289])).

fof(f289,plain,
    ( ~ r2_hidden(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))),a_3_0_waybel_9(sK0,sK1,sK2))
    | ~ spl11_27 ),
    inference(avatar_component_clause,[],[f288])).

fof(f288,plain,
    ( spl11_27
  <=> ~ r2_hidden(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))),a_3_0_waybel_9(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_27])])).

fof(f141,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(X4,a_3_0_waybel_9(X1,X2,X3))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X2)
      | ~ l1_waybel_0(X2,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ m1_subset_1(X4,u1_struct_0(X2))
      | ~ r1_orders_2(X2,X3,X4)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f108])).

fof(f108,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_struct_0(X1)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X2)
      | ~ l1_waybel_0(X2,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ m1_subset_1(X4,u1_struct_0(X2))
      | X0 != X4
      | ~ r1_orders_2(X2,X3,X4)
      | r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f441,plain,
    ( spl11_1
    | spl11_3
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_28
    | spl11_33 ),
    inference(avatar_contradiction_clause,[],[f440])).

fof(f440,plain,
    ( $false
    | ~ spl11_1
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_28
    | ~ spl11_33 ),
    inference(subsumption_resolution,[],[f439,f368])).

fof(f368,plain,
    ( ~ m1_subset_1(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))),u1_struct_0(sK1))
    | ~ spl11_33 ),
    inference(avatar_component_clause,[],[f367])).

fof(f367,plain,
    ( spl11_33
  <=> ~ m1_subset_1(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_33])])).

fof(f405,plain,
    ( spl11_34
    | spl11_27
    | ~ spl11_30 ),
    inference(avatar_split_clause,[],[f375,f319,f288,f403])).

fof(f403,plain,
    ( spl11_34
  <=> v1_xboole_0(a_3_0_waybel_9(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_34])])).

fof(f319,plain,
    ( spl11_30
  <=> m1_subset_1(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))),a_3_0_waybel_9(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_30])])).

fof(f375,plain,
    ( v1_xboole_0(a_3_0_waybel_9(sK0,sK1,sK2))
    | ~ spl11_27
    | ~ spl11_30 ),
    inference(subsumption_resolution,[],[f374,f320])).

fof(f320,plain,
    ( m1_subset_1(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))),a_3_0_waybel_9(sK0,sK1,sK2))
    | ~ spl11_30 ),
    inference(avatar_component_clause,[],[f319])).

fof(f374,plain,
    ( v1_xboole_0(a_3_0_waybel_9(sK0,sK1,sK2))
    | ~ m1_subset_1(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))),a_3_0_waybel_9(sK0,sK1,sK2))
    | ~ spl11_27 ),
    inference(resolution,[],[f289,f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f41])).

fof(f41,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t12_waybel_9.p',t2_subset)).

fof(f372,plain,
    ( spl11_32
    | spl11_1
    | spl11_3
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_26 ),
    inference(avatar_split_clause,[],[f346,f285,f195,f188,f181,f174,f167,f370])).

fof(f346,plain,
    ( m1_subset_1(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))),u1_struct_0(sK1))
    | ~ spl11_1
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_26 ),
    inference(forward_demodulation,[],[f345,f336])).

fof(f345,plain,
    ( m1_subset_1(sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))),sK1,sK2),u1_struct_0(sK1))
    | ~ spl11_1
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_26 ),
    inference(subsumption_resolution,[],[f344,f175])).

fof(f344,plain,
    ( m1_subset_1(sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))),sK1,sK2),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | ~ spl11_1
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_8
    | ~ spl11_26 ),
    inference(subsumption_resolution,[],[f343,f196])).

fof(f343,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | m1_subset_1(sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))),sK1,sK2),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | ~ spl11_1
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_26 ),
    inference(subsumption_resolution,[],[f342,f189])).

fof(f342,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | m1_subset_1(sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))),sK1,sK2),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | ~ spl11_1
    | ~ spl11_4
    | ~ spl11_26 ),
    inference(subsumption_resolution,[],[f341,f168])).

fof(f341,plain,
    ( v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | m1_subset_1(sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))),sK1,sK2),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | ~ spl11_4
    | ~ spl11_26 ),
    inference(subsumption_resolution,[],[f337,f182])).

fof(f337,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | m1_subset_1(sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))),sK1,sK2),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | ~ spl11_26 ),
    inference(resolution,[],[f105,f286])).

fof(f105,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X2)
      | ~ l1_waybel_0(X2,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | m1_subset_1(sK4(X0,X2,X3),u1_struct_0(X2))
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f321,plain,
    ( spl11_30
    | ~ spl11_26 ),
    inference(avatar_split_clause,[],[f309,f285,f319])).

fof(f309,plain,
    ( m1_subset_1(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))),a_3_0_waybel_9(sK0,sK1,sK2))
    | ~ spl11_26 ),
    inference(resolution,[],[f286,f126])).

fof(f126,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t12_waybel_9.p',t1_subset)).

fof(f308,plain,
    ( spl11_26
    | spl11_13
    | spl11_29 ),
    inference(avatar_split_clause,[],[f304,f294,f209,f285])).

fof(f209,plain,
    ( spl11_13
  <=> u1_struct_0(k4_waybel_9(sK0,sK1,sK2)) != a_3_0_waybel_9(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).

fof(f304,plain,
    ( r2_hidden(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))),a_3_0_waybel_9(sK0,sK1,sK2))
    | ~ spl11_13
    | ~ spl11_29 ),
    inference(subsumption_resolution,[],[f299,f210])).

fof(f210,plain,
    ( u1_struct_0(k4_waybel_9(sK0,sK1,sK2)) != a_3_0_waybel_9(sK0,sK1,sK2)
    | ~ spl11_13 ),
    inference(avatar_component_clause,[],[f209])).

fof(f299,plain,
    ( r2_hidden(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))),a_3_0_waybel_9(sK0,sK1,sK2))
    | u1_struct_0(k4_waybel_9(sK0,sK1,sK2)) = a_3_0_waybel_9(sK0,sK1,sK2)
    | ~ spl11_29 ),
    inference(resolution,[],[f295,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r2_hidden(sK3(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f42])).

fof(f42,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t12_waybel_9.p',t2_tarski)).

fof(f303,plain,
    ( spl11_13
    | spl11_27
    | spl11_29 ),
    inference(avatar_contradiction_clause,[],[f302])).

fof(f302,plain,
    ( $false
    | ~ spl11_13
    | ~ spl11_27
    | ~ spl11_29 ),
    inference(subsumption_resolution,[],[f301,f210])).

fof(f301,plain,
    ( u1_struct_0(k4_waybel_9(sK0,sK1,sK2)) = a_3_0_waybel_9(sK0,sK1,sK2)
    | ~ spl11_27
    | ~ spl11_29 ),
    inference(subsumption_resolution,[],[f299,f289])).

fof(f296,plain,
    ( ~ spl11_27
    | ~ spl11_29
    | spl11_13 ),
    inference(avatar_split_clause,[],[f258,f209,f294,f288])).

fof(f258,plain,
    ( ~ r2_hidden(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
    | ~ r2_hidden(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))),a_3_0_waybel_9(sK0,sK1,sK2))
    | ~ spl11_13 ),
    inference(extensionality_resolution,[],[f101,f210])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | ~ r2_hidden(sK3(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f282,plain,
    ( spl11_13
    | spl11_23
    | spl11_25 ),
    inference(avatar_contradiction_clause,[],[f281])).

fof(f281,plain,
    ( $false
    | ~ spl11_13
    | ~ spl11_23
    | ~ spl11_25 ),
    inference(subsumption_resolution,[],[f280,f210])).

fof(f280,plain,
    ( u1_struct_0(k4_waybel_9(sK0,sK1,sK2)) = a_3_0_waybel_9(sK0,sK1,sK2)
    | ~ spl11_23
    | ~ spl11_25 ),
    inference(subsumption_resolution,[],[f279,f274])).

fof(f274,plain,
    ( ~ r2_hidden(sK3(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2))
    | ~ spl11_25 ),
    inference(avatar_component_clause,[],[f273])).

fof(f273,plain,
    ( spl11_25
  <=> ~ r2_hidden(sK3(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_25])])).

fof(f279,plain,
    ( r2_hidden(sK3(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2))
    | u1_struct_0(k4_waybel_9(sK0,sK1,sK2)) = a_3_0_waybel_9(sK0,sK1,sK2)
    | ~ spl11_23 ),
    inference(resolution,[],[f268,f100])).

fof(f268,plain,
    ( ~ r2_hidden(sK3(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
    | ~ spl11_23 ),
    inference(avatar_component_clause,[],[f267])).

fof(f267,plain,
    ( spl11_23
  <=> ~ r2_hidden(sK3(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_23])])).

fof(f275,plain,
    ( ~ spl11_23
    | ~ spl11_25
    | spl11_13 ),
    inference(avatar_split_clause,[],[f257,f209,f273,f267])).

fof(f257,plain,
    ( ~ r2_hidden(sK3(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2))
    | ~ r2_hidden(sK3(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
    | ~ spl11_13 ),
    inference(extensionality_resolution,[],[f101,f210])).

fof(f249,plain,
    ( spl11_20
    | ~ spl11_14 ),
    inference(avatar_split_clause,[],[f240,f224,f247])).

fof(f247,plain,
    ( spl11_20
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).

fof(f224,plain,
    ( spl11_14
  <=> l1_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).

fof(f240,plain,
    ( l1_struct_0(sK1)
    | ~ spl11_14 ),
    inference(resolution,[],[f225,f137])).

fof(f137,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t12_waybel_9.p',dt_l1_orders_2)).

fof(f225,plain,
    ( l1_orders_2(sK1)
    | ~ spl11_14 ),
    inference(avatar_component_clause,[],[f224])).

fof(f239,plain,
    ( ~ spl11_17
    | ~ spl11_19
    | spl11_13 ),
    inference(avatar_split_clause,[],[f217,f209,f237,f231])).

fof(f231,plain,
    ( spl11_17
  <=> ~ r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_17])])).

fof(f237,plain,
    ( spl11_19
  <=> ~ r1_tarski(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_19])])).

fof(f217,plain,
    ( ~ r1_tarski(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
    | ~ r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),a_3_0_waybel_9(sK0,sK1,sK2))
    | ~ spl11_13 ),
    inference(extensionality_resolution,[],[f99,f210])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t12_waybel_9.p',d10_xboole_0)).

fof(f226,plain,
    ( spl11_14
    | ~ spl11_4
    | ~ spl11_6 ),
    inference(avatar_split_clause,[],[f215,f188,f181,f224])).

fof(f215,plain,
    ( l1_orders_2(sK1)
    | ~ spl11_4
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f212,f182])).

fof(f212,plain,
    ( ~ l1_struct_0(sK0)
    | l1_orders_2(sK1)
    | ~ spl11_6 ),
    inference(resolution,[],[f135,f189])).

fof(f135,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | l1_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t12_waybel_9.p',dt_l1_waybel_0)).

fof(f211,plain,(
    ~ spl11_13 ),
    inference(avatar_split_clause,[],[f85,f209])).

fof(f85,plain,(
    u1_struct_0(k4_waybel_9(sK0,sK1,sK2)) != a_3_0_waybel_9(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( u1_struct_0(k4_waybel_9(X0,X1,X2)) != a_3_0_waybel_9(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( u1_struct_0(k4_waybel_9(X0,X1,X2)) != a_3_0_waybel_9(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X1))
               => u1_struct_0(k4_waybel_9(X0,X1,X2)) = a_3_0_waybel_9(X0,X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => u1_struct_0(k4_waybel_9(X0,X1,X2)) = a_3_0_waybel_9(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t12_waybel_9.p',t12_waybel_9)).

fof(f204,plain,(
    spl11_10 ),
    inference(avatar_split_clause,[],[f136,f202])).

fof(f202,plain,
    ( spl11_10
  <=> l1_struct_0(sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f136,plain,(
    l1_struct_0(sK10) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,axiom,(
    ? [X0] : l1_struct_0(X0) ),
    file('/export/starexec/sandbox/benchmark/waybel_9__t12_waybel_9.p',existence_l1_struct_0)).

fof(f197,plain,(
    spl11_8 ),
    inference(avatar_split_clause,[],[f84,f195])).

fof(f84,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f51])).

fof(f190,plain,(
    spl11_6 ),
    inference(avatar_split_clause,[],[f87,f188])).

fof(f87,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f183,plain,(
    spl11_4 ),
    inference(avatar_split_clause,[],[f89,f181])).

fof(f89,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f176,plain,(
    ~ spl11_3 ),
    inference(avatar_split_clause,[],[f88,f174])).

fof(f88,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f169,plain,(
    ~ spl11_1 ),
    inference(avatar_split_clause,[],[f86,f167])).

fof(f86,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f51])).
%------------------------------------------------------------------------------
