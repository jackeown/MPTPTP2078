%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:03 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 248 expanded)
%              Number of leaves         :   30 ( 116 expanded)
%              Depth                    :   14
%              Number of atoms          :  453 ( 971 expanded)
%              Number of equality atoms :   27 (  40 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f280,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f66,f71,f76,f81,f86,f131,f136,f149,f182,f209,f238,f243,f250,f272,f278,f279])).

fof(f279,plain,
    ( sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) != sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2)
    | ~ m1_subset_1(sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2),u1_struct_0(sK1))
    | m1_subset_1(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),u1_struct_0(sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f278,plain,
    ( spl5_26
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | spl5_6
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f277,f240,f83,f78,f73,f68,f63,f264])).

fof(f264,plain,
    ( spl5_26
  <=> sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) = sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f63,plain,
    ( spl5_2
  <=> m1_subset_1(sK2,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f68,plain,
    ( spl5_3
  <=> l1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f73,plain,
    ( spl5_4
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f78,plain,
    ( spl5_5
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f83,plain,
    ( spl5_6
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f240,plain,
    ( spl5_23
  <=> r2_hidden(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),a_3_0_waybel_9(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f277,plain,
    ( sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) = sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2)
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | spl5_6
    | ~ spl5_23 ),
    inference(subsumption_resolution,[],[f276,f85])).

fof(f85,plain,
    ( ~ v2_struct_0(sK0)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f83])).

fof(f276,plain,
    ( sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) = sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2)
    | v2_struct_0(sK0)
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | ~ spl5_23 ),
    inference(subsumption_resolution,[],[f275,f80])).

% (19778)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
fof(f80,plain,
    ( l1_struct_0(sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f78])).

fof(f275,plain,
    ( sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) = sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | ~ spl5_23 ),
    inference(subsumption_resolution,[],[f274,f75])).

fof(f75,plain,
    ( ~ v2_struct_0(sK1)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f73])).

fof(f274,plain,
    ( sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) = sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_23 ),
    inference(subsumption_resolution,[],[f273,f70])).

fof(f70,plain,
    ( l1_waybel_0(sK1,sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f68])).

fof(f273,plain,
    ( sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) = sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2)
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_2
    | ~ spl5_23 ),
    inference(subsumption_resolution,[],[f256,f65])).

fof(f65,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f256,plain,
    ( sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) = sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_23 ),
    inference(resolution,[],[f242,f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( sK4(X0,X2,X3) = X0
      | ~ r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
          | ! [X4] :
              ( ~ r1_orders_2(X2,X3,X4)
              | X0 != X4
              | ~ m1_subset_1(X4,u1_struct_0(X2)) ) )
        & ( ( r1_orders_2(X2,X3,sK4(X0,X2,X3))
            & sK4(X0,X2,X3) = X0
            & m1_subset_1(sK4(X0,X2,X3),u1_struct_0(X2)) )
          | ~ r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) ) )
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f37])).

fof(f37,plain,(
    ! [X3,X2,X0] :
      ( ? [X5] :
          ( r1_orders_2(X2,X3,X5)
          & X0 = X5
          & m1_subset_1(X5,u1_struct_0(X2)) )
     => ( r1_orders_2(X2,X3,sK4(X0,X2,X3))
        & sK4(X0,X2,X3) = X0
        & m1_subset_1(sK4(X0,X2,X3),u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
          | ! [X4] :
              ( ~ r1_orders_2(X2,X3,X4)
              | X0 != X4
              | ~ m1_subset_1(X4,u1_struct_0(X2)) ) )
        & ( ? [X5] :
              ( r1_orders_2(X2,X3,X5)
              & X0 = X5
              & m1_subset_1(X5,u1_struct_0(X2)) )
          | ~ r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) ) )
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
          | ! [X4] :
              ( ~ r1_orders_2(X2,X3,X4)
              | X0 != X4
              | ~ m1_subset_1(X4,u1_struct_0(X2)) ) )
        & ( ? [X4] :
              ( r1_orders_2(X2,X3,X4)
              & X0 = X4
              & m1_subset_1(X4,u1_struct_0(X2)) )
          | ~ r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) ) )
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_3_0_waybel_9)).

fof(f242,plain,
    ( r2_hidden(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),a_3_0_waybel_9(sK0,sK1,sK2))
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f240])).

fof(f272,plain,
    ( spl5_27
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | spl5_6
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f252,f240,f83,f78,f73,f68,f63,f269])).

fof(f269,plain,
    ( spl5_27
  <=> m1_subset_1(sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f252,plain,
    ( m1_subset_1(sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2),u1_struct_0(sK1))
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | spl5_6
    | ~ spl5_23 ),
    inference(unit_resulting_resolution,[],[f85,f80,f75,f70,f65,f242,f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK4(X0,X2,X3),u1_struct_0(X2))
      | ~ r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f250,plain,
    ( ~ spl5_24
    | spl5_10
    | spl5_22 ),
    inference(avatar_split_clause,[],[f244,f235,f152,f247])).

fof(f247,plain,
    ( spl5_24
  <=> m1_subset_1(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f152,plain,
    ( spl5_10
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f235,plain,
    ( spl5_22
  <=> r2_hidden(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f244,plain,
    ( ~ m1_subset_1(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),u1_struct_0(sK1))
    | spl5_10
    | spl5_22 ),
    inference(unit_resulting_resolution,[],[f153,f237,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f237,plain,
    ( ~ r2_hidden(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),u1_struct_0(sK1))
    | spl5_22 ),
    inference(avatar_component_clause,[],[f235])).

fof(f153,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | spl5_10 ),
    inference(avatar_component_clause,[],[f152])).

fof(f243,plain,
    ( spl5_23
    | spl5_16 ),
    inference(avatar_split_clause,[],[f230,f206,f240])).

fof(f206,plain,
    ( spl5_16
  <=> r1_tarski(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f230,plain,
    ( r2_hidden(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),a_3_0_waybel_9(sK0,sK1,sK2))
    | spl5_16 ),
    inference(unit_resulting_resolution,[],[f208,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f208,plain,
    ( ~ r1_tarski(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1))
    | spl5_16 ),
    inference(avatar_component_clause,[],[f206])).

fof(f238,plain,
    ( ~ spl5_22
    | spl5_16 ),
    inference(avatar_split_clause,[],[f231,f206,f235])).

fof(f231,plain,
    ( ~ r2_hidden(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),u1_struct_0(sK1))
    | spl5_16 ),
    inference(unit_resulting_resolution,[],[f208,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f209,plain,
    ( ~ spl5_16
    | spl5_1
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f195,f146,f58,f206])).

fof(f58,plain,
    ( spl5_1
  <=> r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f146,plain,
    ( spl5_9
  <=> u1_struct_0(k4_waybel_9(sK0,sK1,sK2)) = a_3_0_waybel_9(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f195,plain,
    ( ~ r1_tarski(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1))
    | spl5_1
    | ~ spl5_9 ),
    inference(backward_demodulation,[],[f60,f148])).

fof(f148,plain,
    ( u1_struct_0(k4_waybel_9(sK0,sK1,sK2)) = a_3_0_waybel_9(sK0,sK1,sK2)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f146])).

fof(f60,plain,
    ( ~ r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f182,plain,
    ( ~ spl5_10
    | ~ spl5_7
    | spl5_8 ),
    inference(avatar_split_clause,[],[f181,f133,f128,f152])).

fof(f128,plain,
    ( spl5_7
  <=> m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f133,plain,
    ( spl5_8
  <=> v1_xboole_0(u1_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f181,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ spl5_7
    | spl5_8 ),
    inference(subsumption_resolution,[],[f178,f135])).

fof(f135,plain,
    ( ~ v1_xboole_0(u1_waybel_0(sK0,sK1))
    | spl5_8 ),
    inference(avatar_component_clause,[],[f133])).

fof(f178,plain,
    ( v1_xboole_0(u1_waybel_0(sK0,sK1))
    | ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ spl5_7 ),
    inference(resolution,[],[f130,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

fof(f130,plain,
    ( m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f128])).

fof(f149,plain,
    ( spl5_9
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | spl5_6 ),
    inference(avatar_split_clause,[],[f137,f83,f78,f73,f68,f63,f146])).

fof(f137,plain,
    ( u1_struct_0(k4_waybel_9(sK0,sK1,sK2)) = a_3_0_waybel_9(sK0,sK1,sK2)
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | spl5_6 ),
    inference(unit_resulting_resolution,[],[f85,f80,f75,f70,f65,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( u1_struct_0(k4_waybel_9(X0,X1,X2)) = a_3_0_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( u1_struct_0(k4_waybel_9(X0,X1,X2)) = a_3_0_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( u1_struct_0(k4_waybel_9(X0,X1,X2)) = a_3_0_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => u1_struct_0(k4_waybel_9(X0,X1,X2)) = a_3_0_waybel_9(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_waybel_9)).

fof(f136,plain,
    ( ~ spl5_8
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | spl5_6 ),
    inference(avatar_split_clause,[],[f118,f83,f78,f73,f68,f133])).

fof(f118,plain,
    ( ~ v1_xboole_0(u1_waybel_0(sK0,sK1))
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | spl5_6 ),
    inference(unit_resulting_resolution,[],[f85,f80,f75,f70,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(u1_waybel_0(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(u1_waybel_0(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(u1_waybel_0(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_waybel_0(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( ~ v1_xboole_0(u1_waybel_0(X0,X1))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & ~ v1_xboole_0(u1_waybel_0(X0,X1))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc15_yellow_6)).

fof(f131,plain,
    ( spl5_7
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f119,f78,f68,f128])).

fof(f119,plain,
    ( m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f80,f70,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_waybel_0)).

fof(f86,plain,(
    ~ spl5_6 ),
    inference(avatar_split_clause,[],[f39,f83])).

fof(f39,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ~ r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_waybel_0(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f31,f30,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1))
                & m1_subset_1(X2,u1_struct_0(X1)) )
            & l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(u1_struct_0(k4_waybel_9(sK0,X1,X2)),u1_struct_0(X1))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(u1_struct_0(k4_waybel_9(sK0,X1,X2)),u1_struct_0(X1))
            & m1_subset_1(X2,u1_struct_0(X1)) )
        & l1_waybel_0(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ~ r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,X2)),u1_struct_0(sK1))
          & m1_subset_1(X2,u1_struct_0(sK1)) )
      & l1_waybel_0(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X2] :
        ( ~ r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,X2)),u1_struct_0(sK1))
        & m1_subset_1(X2,u1_struct_0(sK1)) )
   => ( ~ r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1))
      & m1_subset_1(sK2,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X1))
               => r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_waybel_9)).

fof(f81,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f40,f78])).

fof(f40,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f76,plain,(
    ~ spl5_4 ),
    inference(avatar_split_clause,[],[f41,f73])).

fof(f41,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f71,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f42,f68])).

fof(f42,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f66,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f43,f63])).

fof(f43,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f32])).

fof(f61,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f44,f58])).

fof(f44,plain,(
    ~ r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:51:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (19770)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (19783)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.51  % (19775)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.51  % (19786)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.51  % (19783)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (19762)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (19763)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (19767)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.51  % (19775)Refutation not found, incomplete strategy% (19775)------------------------------
% 0.21/0.51  % (19775)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (19767)Refutation not found, incomplete strategy% (19767)------------------------------
% 0.21/0.51  % (19767)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (19775)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (19775)Memory used [KB]: 10618
% 0.21/0.51  % (19775)Time elapsed: 0.098 s
% 0.21/0.51  % (19775)------------------------------
% 0.21/0.51  % (19775)------------------------------
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f280,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f61,f66,f71,f76,f81,f86,f131,f136,f149,f182,f209,f238,f243,f250,f272,f278,f279])).
% 0.21/0.52  fof(f279,plain,(
% 0.21/0.52    sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) != sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2) | ~m1_subset_1(sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2),u1_struct_0(sK1)) | m1_subset_1(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),u1_struct_0(sK1))),
% 0.21/0.52    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.52  fof(f278,plain,(
% 0.21/0.52    spl5_26 | ~spl5_2 | ~spl5_3 | spl5_4 | ~spl5_5 | spl5_6 | ~spl5_23),
% 0.21/0.52    inference(avatar_split_clause,[],[f277,f240,f83,f78,f73,f68,f63,f264])).
% 0.21/0.52  fof(f264,plain,(
% 0.21/0.52    spl5_26 <=> sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) = sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    spl5_2 <=> m1_subset_1(sK2,u1_struct_0(sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    spl5_3 <=> l1_waybel_0(sK1,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    spl5_4 <=> v2_struct_0(sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    spl5_5 <=> l1_struct_0(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    spl5_6 <=> v2_struct_0(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.52  fof(f240,plain,(
% 0.21/0.52    spl5_23 <=> r2_hidden(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),a_3_0_waybel_9(sK0,sK1,sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.21/0.52  fof(f277,plain,(
% 0.21/0.52    sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) = sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2) | (~spl5_2 | ~spl5_3 | spl5_4 | ~spl5_5 | spl5_6 | ~spl5_23)),
% 0.21/0.52    inference(subsumption_resolution,[],[f276,f85])).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    ~v2_struct_0(sK0) | spl5_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f83])).
% 0.21/0.52  fof(f276,plain,(
% 0.21/0.52    sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) = sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2) | v2_struct_0(sK0) | (~spl5_2 | ~spl5_3 | spl5_4 | ~spl5_5 | ~spl5_23)),
% 0.21/0.52    inference(subsumption_resolution,[],[f275,f80])).
% 0.21/0.52  % (19778)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    l1_struct_0(sK0) | ~spl5_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f78])).
% 0.21/0.52  fof(f275,plain,(
% 0.21/0.52    sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) = sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | (~spl5_2 | ~spl5_3 | spl5_4 | ~spl5_23)),
% 0.21/0.52    inference(subsumption_resolution,[],[f274,f75])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    ~v2_struct_0(sK1) | spl5_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f73])).
% 0.21/0.52  fof(f274,plain,(
% 0.21/0.52    sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) = sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2) | v2_struct_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | (~spl5_2 | ~spl5_3 | ~spl5_23)),
% 0.21/0.52    inference(subsumption_resolution,[],[f273,f70])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    l1_waybel_0(sK1,sK0) | ~spl5_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f68])).
% 0.21/0.52  fof(f273,plain,(
% 0.21/0.52    sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) = sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | (~spl5_2 | ~spl5_23)),
% 0.21/0.52    inference(subsumption_resolution,[],[f256,f65])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    m1_subset_1(sK2,u1_struct_0(sK1)) | ~spl5_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f63])).
% 0.21/0.52  fof(f256,plain,(
% 0.21/0.52    sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) = sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2) | ~m1_subset_1(sK2,u1_struct_0(sK1)) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl5_23),
% 0.21/0.52    inference(resolution,[],[f242,f53])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (sK4(X0,X2,X3) = X0 | ~r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_waybel_0(X2,X1) | v2_struct_0(X2) | ~l1_struct_0(X1) | v2_struct_0(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (((r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) | ! [X4] : (~r1_orders_2(X2,X3,X4) | X0 != X4 | ~m1_subset_1(X4,u1_struct_0(X2)))) & ((r1_orders_2(X2,X3,sK4(X0,X2,X3)) & sK4(X0,X2,X3) = X0 & m1_subset_1(sK4(X0,X2,X3),u1_struct_0(X2))) | ~r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)))) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_waybel_0(X2,X1) | v2_struct_0(X2) | ~l1_struct_0(X1) | v2_struct_0(X1))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ! [X3,X2,X0] : (? [X5] : (r1_orders_2(X2,X3,X5) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X2))) => (r1_orders_2(X2,X3,sK4(X0,X2,X3)) & sK4(X0,X2,X3) = X0 & m1_subset_1(sK4(X0,X2,X3),u1_struct_0(X2))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (((r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) | ! [X4] : (~r1_orders_2(X2,X3,X4) | X0 != X4 | ~m1_subset_1(X4,u1_struct_0(X2)))) & (? [X5] : (r1_orders_2(X2,X3,X5) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X2))) | ~r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)))) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_waybel_0(X2,X1) | v2_struct_0(X2) | ~l1_struct_0(X1) | v2_struct_0(X1))),
% 0.21/0.52    inference(rectify,[],[f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (((r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) | ! [X4] : (~r1_orders_2(X2,X3,X4) | X0 != X4 | ~m1_subset_1(X4,u1_struct_0(X2)))) & (? [X4] : (r1_orders_2(X2,X3,X4) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X2))) | ~r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)))) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_waybel_0(X2,X1) | v2_struct_0(X2) | ~l1_struct_0(X1) | v2_struct_0(X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) <=> ? [X4] : (r1_orders_2(X2,X3,X4) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X2)))) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_waybel_0(X2,X1) | v2_struct_0(X2) | ~l1_struct_0(X1) | v2_struct_0(X1))),
% 0.21/0.52    inference(flattening,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) <=> ? [X4] : (r1_orders_2(X2,X3,X4) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X2)))) | (~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_waybel_0(X2,X1) | v2_struct_0(X2) | ~l1_struct_0(X1) | v2_struct_0(X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,u1_struct_0(X2)) & l1_waybel_0(X2,X1) & ~v2_struct_0(X2) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) <=> ? [X4] : (r1_orders_2(X2,X3,X4) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X2)))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_3_0_waybel_9)).
% 0.21/0.52  fof(f242,plain,(
% 0.21/0.52    r2_hidden(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),a_3_0_waybel_9(sK0,sK1,sK2)) | ~spl5_23),
% 0.21/0.52    inference(avatar_component_clause,[],[f240])).
% 0.21/0.52  fof(f272,plain,(
% 0.21/0.52    spl5_27 | ~spl5_2 | ~spl5_3 | spl5_4 | ~spl5_5 | spl5_6 | ~spl5_23),
% 0.21/0.52    inference(avatar_split_clause,[],[f252,f240,f83,f78,f73,f68,f63,f269])).
% 0.21/0.52  fof(f269,plain,(
% 0.21/0.52    spl5_27 <=> m1_subset_1(sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2),u1_struct_0(sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 0.21/0.52  fof(f252,plain,(
% 0.21/0.52    m1_subset_1(sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2),u1_struct_0(sK1)) | (~spl5_2 | ~spl5_3 | spl5_4 | ~spl5_5 | spl5_6 | ~spl5_23)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f85,f80,f75,f70,f65,f242,f52])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK4(X0,X2,X3),u1_struct_0(X2)) | ~r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_waybel_0(X2,X1) | v2_struct_0(X2) | ~l1_struct_0(X1) | v2_struct_0(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f38])).
% 0.21/0.52  fof(f250,plain,(
% 0.21/0.52    ~spl5_24 | spl5_10 | spl5_22),
% 0.21/0.52    inference(avatar_split_clause,[],[f244,f235,f152,f247])).
% 0.21/0.52  fof(f247,plain,(
% 0.21/0.52    spl5_24 <=> m1_subset_1(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),u1_struct_0(sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.21/0.52  fof(f152,plain,(
% 0.21/0.52    spl5_10 <=> v1_xboole_0(u1_struct_0(sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.52  fof(f235,plain,(
% 0.21/0.52    spl5_22 <=> r2_hidden(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),u1_struct_0(sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.21/0.52  fof(f244,plain,(
% 0.21/0.52    ~m1_subset_1(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),u1_struct_0(sK1)) | (spl5_10 | spl5_22)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f153,f237,f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.52    inference(flattening,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.52  fof(f237,plain,(
% 0.21/0.52    ~r2_hidden(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),u1_struct_0(sK1)) | spl5_22),
% 0.21/0.52    inference(avatar_component_clause,[],[f235])).
% 0.21/0.52  fof(f153,plain,(
% 0.21/0.52    ~v1_xboole_0(u1_struct_0(sK1)) | spl5_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f152])).
% 0.21/0.52  fof(f243,plain,(
% 0.21/0.52    spl5_23 | spl5_16),
% 0.21/0.52    inference(avatar_split_clause,[],[f230,f206,f240])).
% 0.21/0.52  fof(f206,plain,(
% 0.21/0.52    spl5_16 <=> r1_tarski(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.21/0.52  fof(f230,plain,(
% 0.21/0.52    r2_hidden(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),a_3_0_waybel_9(sK0,sK1,sK2)) | spl5_16),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f208,f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 0.21/0.52    inference(unused_predicate_definition_removal,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.52  fof(f208,plain,(
% 0.21/0.52    ~r1_tarski(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) | spl5_16),
% 0.21/0.52    inference(avatar_component_clause,[],[f206])).
% 0.21/0.52  fof(f238,plain,(
% 0.21/0.52    ~spl5_22 | spl5_16),
% 0.21/0.52    inference(avatar_split_clause,[],[f231,f206,f235])).
% 0.21/0.52  fof(f231,plain,(
% 0.21/0.52    ~r2_hidden(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),u1_struct_0(sK1)) | spl5_16),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f208,f51])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK3(X0,X1),X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f34])).
% 0.21/0.52  fof(f209,plain,(
% 0.21/0.52    ~spl5_16 | spl5_1 | ~spl5_9),
% 0.21/0.52    inference(avatar_split_clause,[],[f195,f146,f58,f206])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    spl5_1 <=> r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.52  fof(f146,plain,(
% 0.21/0.52    spl5_9 <=> u1_struct_0(k4_waybel_9(sK0,sK1,sK2)) = a_3_0_waybel_9(sK0,sK1,sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.52  fof(f195,plain,(
% 0.21/0.52    ~r1_tarski(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) | (spl5_1 | ~spl5_9)),
% 0.21/0.52    inference(backward_demodulation,[],[f60,f148])).
% 0.21/0.52  fof(f148,plain,(
% 0.21/0.52    u1_struct_0(k4_waybel_9(sK0,sK1,sK2)) = a_3_0_waybel_9(sK0,sK1,sK2) | ~spl5_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f146])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    ~r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1)) | spl5_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f58])).
% 0.21/0.52  fof(f182,plain,(
% 0.21/0.52    ~spl5_10 | ~spl5_7 | spl5_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f181,f133,f128,f152])).
% 0.21/0.52  fof(f128,plain,(
% 0.21/0.52    spl5_7 <=> m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.52  fof(f133,plain,(
% 0.21/0.52    spl5_8 <=> v1_xboole_0(u1_waybel_0(sK0,sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.52  fof(f181,plain,(
% 0.21/0.52    ~v1_xboole_0(u1_struct_0(sK1)) | (~spl5_7 | spl5_8)),
% 0.21/0.52    inference(subsumption_resolution,[],[f178,f135])).
% 0.21/0.52  fof(f135,plain,(
% 0.21/0.52    ~v1_xboole_0(u1_waybel_0(sK0,sK1)) | spl5_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f133])).
% 0.21/0.52  fof(f178,plain,(
% 0.21/0.52    v1_xboole_0(u1_waybel_0(sK0,sK1)) | ~v1_xboole_0(u1_struct_0(sK1)) | ~spl5_7),
% 0.21/0.52    inference(resolution,[],[f130,f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).
% 0.21/0.52  fof(f130,plain,(
% 0.21/0.52    m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~spl5_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f128])).
% 0.21/0.52  fof(f149,plain,(
% 0.21/0.52    spl5_9 | ~spl5_2 | ~spl5_3 | spl5_4 | ~spl5_5 | spl5_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f137,f83,f78,f73,f68,f63,f146])).
% 0.21/0.52  fof(f137,plain,(
% 0.21/0.52    u1_struct_0(k4_waybel_9(sK0,sK1,sK2)) = a_3_0_waybel_9(sK0,sK1,sK2) | (~spl5_2 | ~spl5_3 | spl5_4 | ~spl5_5 | spl5_6)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f85,f80,f75,f70,f65,f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (u1_struct_0(k4_waybel_9(X0,X1,X2)) = a_3_0_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (u1_struct_0(k4_waybel_9(X0,X1,X2)) = a_3_0_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (u1_struct_0(k4_waybel_9(X0,X1,X2)) = a_3_0_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => u1_struct_0(k4_waybel_9(X0,X1,X2)) = a_3_0_waybel_9(X0,X1,X2))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_waybel_9)).
% 0.21/0.52  fof(f136,plain,(
% 0.21/0.52    ~spl5_8 | ~spl5_3 | spl5_4 | ~spl5_5 | spl5_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f118,f83,f78,f73,f68,f133])).
% 0.21/0.52  fof(f118,plain,(
% 0.21/0.52    ~v1_xboole_0(u1_waybel_0(sK0,sK1)) | (~spl5_3 | spl5_4 | ~spl5_5 | spl5_6)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f85,f80,f75,f70,f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_xboole_0(u1_waybel_0(X0,X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0,X1] : (~v1_xboole_0(u1_waybel_0(X0,X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0,X1] : (~v1_xboole_0(u1_waybel_0(X0,X1)) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ! [X0,X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_waybel_0(X0,X1)))),
% 0.21/0.52    inference(pure_predicate_removal,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X0,X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (~v1_xboole_0(u1_waybel_0(X0,X1)) & v1_funct_1(u1_waybel_0(X0,X1))))),
% 0.21/0.52    inference(pure_predicate_removal,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & ~v1_xboole_0(u1_waybel_0(X0,X1)) & v1_funct_1(u1_waybel_0(X0,X1))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc15_yellow_6)).
% 0.21/0.52  fof(f131,plain,(
% 0.21/0.52    spl5_7 | ~spl5_3 | ~spl5_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f119,f78,f68,f128])).
% 0.21/0.52  fof(f119,plain,(
% 0.21/0.52    m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | (~spl5_3 | ~spl5_5)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f80,f70,f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))))),
% 0.21/0.52    inference(pure_predicate_removal,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_1(u1_waybel_0(X0,X1))))),
% 0.21/0.52    inference(pure_predicate_removal,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(u1_waybel_0(X0,X1))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_waybel_0)).
% 0.21/0.52  fof(f86,plain,(
% 0.21/0.52    ~spl5_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f39,f83])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ~v2_struct_0(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ((~r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1)) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_waybel_0(sK1,sK0) & ~v2_struct_0(sK1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f31,f30,f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)) & m1_subset_1(X2,u1_struct_0(X1))) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r1_tarski(u1_struct_0(k4_waybel_9(sK0,X1,X2)),u1_struct_0(X1)) & m1_subset_1(X2,u1_struct_0(X1))) & l1_waybel_0(X1,sK0) & ~v2_struct_0(X1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ? [X1] : (? [X2] : (~r1_tarski(u1_struct_0(k4_waybel_9(sK0,X1,X2)),u1_struct_0(X1)) & m1_subset_1(X2,u1_struct_0(X1))) & l1_waybel_0(X1,sK0) & ~v2_struct_0(X1)) => (? [X2] : (~r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,X2)),u1_struct_0(sK1)) & m1_subset_1(X2,u1_struct_0(sK1))) & l1_waybel_0(sK1,sK0) & ~v2_struct_0(sK1))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ? [X2] : (~r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,X2)),u1_struct_0(sK1)) & m1_subset_1(X2,u1_struct_0(sK1))) => (~r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1)) & m1_subset_1(sK2,u1_struct_0(sK1)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)) & m1_subset_1(X2,u1_struct_0(X1))) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)) & m1_subset_1(X2,u1_struct_0(X1))) & (l1_waybel_0(X1,X0) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,negated_conjecture,(
% 0.21/0.52    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)))))),
% 0.21/0.52    inference(negated_conjecture,[],[f8])).
% 0.21/0.52  fof(f8,conjecture,(
% 0.21/0.52    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_waybel_9)).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    spl5_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f40,f78])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    l1_struct_0(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    ~spl5_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f41,f73])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ~v2_struct_0(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    spl5_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f42,f68])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    l1_waybel_0(sK1,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    spl5_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f43,f63])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    m1_subset_1(sK2,u1_struct_0(sK1))),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    ~spl5_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f44,f58])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ~r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1))),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (19783)------------------------------
% 0.21/0.52  % (19783)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (19783)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (19783)Memory used [KB]: 6396
% 0.21/0.52  % (19783)Time elapsed: 0.102 s
% 0.21/0.52  % (19783)------------------------------
% 0.21/0.52  % (19783)------------------------------
% 0.21/0.52  % (19757)Success in time 0.16 s
%------------------------------------------------------------------------------
