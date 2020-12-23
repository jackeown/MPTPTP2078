%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:03 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 247 expanded)
%              Number of leaves         :   30 ( 116 expanded)
%              Depth                    :   14
%              Number of atoms          :  463 ( 981 expanded)
%              Number of equality atoms :   27 (  40 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f308,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f69,f74,f79,f84,f89,f134,f139,f153,f227,f256,f261,f268,f297,f303,f304,f307])).

fof(f307,plain,
    ( ~ spl5_10
    | ~ spl5_7
    | spl5_8 ),
    inference(avatar_split_clause,[],[f196,f136,f131,f156])).

fof(f156,plain,
    ( spl5_10
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f131,plain,
    ( spl5_7
  <=> m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f136,plain,
    ( spl5_8
  <=> v1_xboole_0(u1_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f196,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ spl5_7
    | spl5_8 ),
    inference(unit_resulting_resolution,[],[f138,f133,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

% (23166)Refutation not found, incomplete strategy% (23166)------------------------------
% (23166)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f133,plain,
    ( m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f131])).

% (23166)Termination reason: Refutation not found, incomplete strategy

fof(f138,plain,
    ( ~ v1_xboole_0(u1_waybel_0(sK0,sK1))
    | spl5_8 ),
    inference(avatar_component_clause,[],[f136])).

% (23166)Memory used [KB]: 10746
% (23166)Time elapsed: 0.081 s
% (23166)------------------------------
% (23166)------------------------------
fof(f304,plain,
    ( sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) != sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2)
    | ~ m1_subset_1(sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2),u1_struct_0(sK1))
    | m1_subset_1(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),u1_struct_0(sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f303,plain,
    ( spl5_27
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | spl5_6
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f302,f258,f86,f81,f76,f71,f66,f289])).

fof(f289,plain,
    ( spl5_27
  <=> sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) = sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f66,plain,
    ( spl5_2
  <=> m1_subset_1(sK2,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f71,plain,
    ( spl5_3
  <=> l1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f76,plain,
    ( spl5_4
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f81,plain,
    ( spl5_5
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f86,plain,
    ( spl5_6
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f258,plain,
    ( spl5_24
  <=> r2_hidden(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),a_3_0_waybel_9(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f302,plain,
    ( sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) = sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2)
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | spl5_6
    | ~ spl5_24 ),
    inference(subsumption_resolution,[],[f301,f88])).

fof(f88,plain,
    ( ~ v2_struct_0(sK0)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f86])).

fof(f301,plain,
    ( sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) = sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2)
    | v2_struct_0(sK0)
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | ~ spl5_24 ),
    inference(subsumption_resolution,[],[f300,f83])).

fof(f83,plain,
    ( l1_struct_0(sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f81])).

fof(f300,plain,
    ( sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) = sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | ~ spl5_24 ),
    inference(subsumption_resolution,[],[f299,f78])).

fof(f78,plain,
    ( ~ v2_struct_0(sK1)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f76])).

fof(f299,plain,
    ( sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) = sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_24 ),
    inference(subsumption_resolution,[],[f298,f73])).

fof(f73,plain,
    ( l1_waybel_0(sK1,sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f71])).

fof(f298,plain,
    ( sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) = sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2)
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_2
    | ~ spl5_24 ),
    inference(subsumption_resolution,[],[f280,f68])).

fof(f68,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f280,plain,
    ( sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) = sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_24 ),
    inference(resolution,[],[f260,f56])).

fof(f56,plain,(
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
    inference(nnf_transformation,[],[f27])).

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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_3_0_waybel_9)).

fof(f260,plain,
    ( r2_hidden(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),a_3_0_waybel_9(sK0,sK1,sK2))
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f258])).

fof(f297,plain,
    ( spl5_28
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | spl5_6
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f276,f258,f86,f81,f76,f71,f66,f294])).

fof(f294,plain,
    ( spl5_28
  <=> m1_subset_1(sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f276,plain,
    ( m1_subset_1(sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2),u1_struct_0(sK1))
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | spl5_6
    | ~ spl5_24 ),
    inference(unit_resulting_resolution,[],[f88,f83,f78,f73,f68,f260,f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK4(X0,X2,X3),u1_struct_0(X2))
      | ~ r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3))
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f268,plain,
    ( ~ spl5_25
    | spl5_10
    | spl5_23 ),
    inference(avatar_split_clause,[],[f262,f253,f156,f265])).

fof(f265,plain,
    ( spl5_25
  <=> m1_subset_1(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f253,plain,
    ( spl5_23
  <=> r2_hidden(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f262,plain,
    ( ~ m1_subset_1(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),u1_struct_0(sK1))
    | spl5_10
    | spl5_23 ),
    inference(unit_resulting_resolution,[],[f157,f255,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f255,plain,
    ( ~ r2_hidden(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),u1_struct_0(sK1))
    | spl5_23 ),
    inference(avatar_component_clause,[],[f253])).

fof(f157,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | spl5_10 ),
    inference(avatar_component_clause,[],[f156])).

fof(f261,plain,
    ( spl5_24
    | spl5_17 ),
    inference(avatar_split_clause,[],[f248,f224,f258])).

fof(f224,plain,
    ( spl5_17
  <=> r1_tarski(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f248,plain,
    ( r2_hidden(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),a_3_0_waybel_9(sK0,sK1,sK2))
    | spl5_17 ),
    inference(unit_resulting_resolution,[],[f226,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f226,plain,
    ( ~ r1_tarski(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1))
    | spl5_17 ),
    inference(avatar_component_clause,[],[f224])).

fof(f256,plain,
    ( ~ spl5_23
    | spl5_17 ),
    inference(avatar_split_clause,[],[f249,f224,f253])).

fof(f249,plain,
    ( ~ r2_hidden(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),u1_struct_0(sK1))
    | spl5_17 ),
    inference(unit_resulting_resolution,[],[f226,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f227,plain,
    ( ~ spl5_17
    | spl5_1
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f213,f150,f61,f224])).

fof(f61,plain,
    ( spl5_1
  <=> r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f150,plain,
    ( spl5_9
  <=> u1_struct_0(k4_waybel_9(sK0,sK1,sK2)) = a_3_0_waybel_9(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f213,plain,
    ( ~ r1_tarski(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1))
    | spl5_1
    | ~ spl5_9 ),
    inference(backward_demodulation,[],[f63,f152])).

fof(f152,plain,
    ( u1_struct_0(k4_waybel_9(sK0,sK1,sK2)) = a_3_0_waybel_9(sK0,sK1,sK2)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f150])).

fof(f63,plain,
    ( ~ r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f153,plain,
    ( spl5_9
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | spl5_6 ),
    inference(avatar_split_clause,[],[f140,f86,f81,f76,f71,f66,f150])).

fof(f140,plain,
    ( u1_struct_0(k4_waybel_9(sK0,sK1,sK2)) = a_3_0_waybel_9(sK0,sK1,sK2)
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | spl5_6 ),
    inference(unit_resulting_resolution,[],[f88,f83,f78,f73,f68,f45])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_waybel_9)).

fof(f139,plain,
    ( ~ spl5_8
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | spl5_6 ),
    inference(avatar_split_clause,[],[f121,f86,f81,f76,f71,f136])).

fof(f121,plain,
    ( ~ v1_xboole_0(u1_waybel_0(sK0,sK1))
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | spl5_6 ),
    inference(unit_resulting_resolution,[],[f88,f83,f78,f73,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(u1_waybel_0(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(u1_waybel_0(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc15_yellow_6)).

fof(f134,plain,
    ( spl5_7
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f122,f81,f71,f131])).

fof(f122,plain,
    ( m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f83,f73,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_waybel_0)).

fof(f89,plain,(
    ~ spl5_6 ),
    inference(avatar_split_clause,[],[f39,f86])).

fof(f39,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ~ r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_waybel_0(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f30,f29,f28])).

fof(f28,plain,
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

fof(f29,plain,
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

fof(f30,plain,
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

% (23150)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_waybel_9)).

fof(f84,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f40,f81])).

fof(f40,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f79,plain,(
    ~ spl5_4 ),
    inference(avatar_split_clause,[],[f41,f76])).

fof(f41,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f74,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f42,f71])).

fof(f42,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f69,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f43,f66])).

fof(f43,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f64,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f44,f61])).

fof(f44,plain,(
    ~ r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:18:46 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (23153)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (23161)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (23147)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (23169)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (23152)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (23151)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.55  % (23161)Refutation not found, incomplete strategy% (23161)------------------------------
% 0.21/0.55  % (23161)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (23148)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.56  % (23145)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.56  % (23163)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.56  % (23158)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.56  % (23166)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.56  % (23161)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (23161)Memory used [KB]: 10618
% 0.21/0.56  % (23161)Time elapsed: 0.129 s
% 0.21/0.56  % (23161)------------------------------
% 0.21/0.56  % (23161)------------------------------
% 0.21/0.56  % (23167)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.56  % (23168)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.56  % (23144)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.57  % (23146)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.57  % (23149)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.57  % (23146)Refutation not found, incomplete strategy% (23146)------------------------------
% 0.21/0.57  % (23146)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (23146)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (23146)Memory used [KB]: 10746
% 0.21/0.57  % (23146)Time elapsed: 0.144 s
% 0.21/0.57  % (23146)------------------------------
% 0.21/0.57  % (23146)------------------------------
% 0.21/0.57  % (23155)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.57  % (23152)Refutation not found, incomplete strategy% (23152)------------------------------
% 0.21/0.57  % (23152)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (23152)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (23152)Memory used [KB]: 10746
% 0.21/0.57  % (23152)Time elapsed: 0.154 s
% 0.21/0.57  % (23152)------------------------------
% 0.21/0.57  % (23152)------------------------------
% 0.21/0.57  % (23169)Refutation found. Thanks to Tanya!
% 0.21/0.57  % SZS status Theorem for theBenchmark
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f308,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(avatar_sat_refutation,[],[f64,f69,f74,f79,f84,f89,f134,f139,f153,f227,f256,f261,f268,f297,f303,f304,f307])).
% 0.21/0.57  fof(f307,plain,(
% 0.21/0.57    ~spl5_10 | ~spl5_7 | spl5_8),
% 0.21/0.57    inference(avatar_split_clause,[],[f196,f136,f131,f156])).
% 0.21/0.57  fof(f156,plain,(
% 0.21/0.57    spl5_10 <=> v1_xboole_0(u1_struct_0(sK1))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.57  fof(f131,plain,(
% 0.21/0.57    spl5_7 <=> m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.57  fof(f136,plain,(
% 0.21/0.57    spl5_8 <=> v1_xboole_0(u1_waybel_0(sK0,sK1))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.57  fof(f196,plain,(
% 0.21/0.57    ~v1_xboole_0(u1_struct_0(sK1)) | (~spl5_7 | spl5_8)),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f138,f133,f50])).
% 0.21/0.57  fof(f50,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f20])).
% 0.21/0.57  fof(f20,plain,(
% 0.21/0.57    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f3])).
% 0.21/0.57  fof(f3,axiom,(
% 0.21/0.57    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).
% 0.21/0.57  % (23166)Refutation not found, incomplete strategy% (23166)------------------------------
% 0.21/0.57  % (23166)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  fof(f133,plain,(
% 0.21/0.57    m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~spl5_7),
% 0.21/0.57    inference(avatar_component_clause,[],[f131])).
% 0.21/0.57  % (23166)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  fof(f138,plain,(
% 0.21/0.57    ~v1_xboole_0(u1_waybel_0(sK0,sK1)) | spl5_8),
% 0.21/0.57    inference(avatar_component_clause,[],[f136])).
% 0.21/0.57  % (23166)Memory used [KB]: 10746
% 0.21/0.57  % (23166)Time elapsed: 0.081 s
% 0.21/0.57  % (23166)------------------------------
% 0.21/0.57  % (23166)------------------------------
% 0.21/0.57  fof(f304,plain,(
% 0.21/0.57    sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) != sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2) | ~m1_subset_1(sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2),u1_struct_0(sK1)) | m1_subset_1(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),u1_struct_0(sK1))),
% 0.21/0.57    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.57  fof(f303,plain,(
% 0.21/0.57    spl5_27 | ~spl5_2 | ~spl5_3 | spl5_4 | ~spl5_5 | spl5_6 | ~spl5_24),
% 0.21/0.57    inference(avatar_split_clause,[],[f302,f258,f86,f81,f76,f71,f66,f289])).
% 0.21/0.57  fof(f289,plain,(
% 0.21/0.57    spl5_27 <=> sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) = sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 0.21/0.57  fof(f66,plain,(
% 0.21/0.57    spl5_2 <=> m1_subset_1(sK2,u1_struct_0(sK1))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.57  fof(f71,plain,(
% 0.21/0.57    spl5_3 <=> l1_waybel_0(sK1,sK0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.57  fof(f76,plain,(
% 0.21/0.57    spl5_4 <=> v2_struct_0(sK1)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.57  fof(f81,plain,(
% 0.21/0.57    spl5_5 <=> l1_struct_0(sK0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.57  fof(f86,plain,(
% 0.21/0.57    spl5_6 <=> v2_struct_0(sK0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.57  fof(f258,plain,(
% 0.21/0.57    spl5_24 <=> r2_hidden(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),a_3_0_waybel_9(sK0,sK1,sK2))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.21/0.57  fof(f302,plain,(
% 0.21/0.57    sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) = sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2) | (~spl5_2 | ~spl5_3 | spl5_4 | ~spl5_5 | spl5_6 | ~spl5_24)),
% 0.21/0.57    inference(subsumption_resolution,[],[f301,f88])).
% 0.21/0.57  fof(f88,plain,(
% 0.21/0.57    ~v2_struct_0(sK0) | spl5_6),
% 0.21/0.57    inference(avatar_component_clause,[],[f86])).
% 0.21/0.57  fof(f301,plain,(
% 0.21/0.57    sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) = sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2) | v2_struct_0(sK0) | (~spl5_2 | ~spl5_3 | spl5_4 | ~spl5_5 | ~spl5_24)),
% 0.21/0.57    inference(subsumption_resolution,[],[f300,f83])).
% 0.21/0.57  fof(f83,plain,(
% 0.21/0.57    l1_struct_0(sK0) | ~spl5_5),
% 0.21/0.57    inference(avatar_component_clause,[],[f81])).
% 0.21/0.57  fof(f300,plain,(
% 0.21/0.57    sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) = sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | (~spl5_2 | ~spl5_3 | spl5_4 | ~spl5_24)),
% 0.21/0.57    inference(subsumption_resolution,[],[f299,f78])).
% 0.21/0.57  fof(f78,plain,(
% 0.21/0.57    ~v2_struct_0(sK1) | spl5_4),
% 0.21/0.57    inference(avatar_component_clause,[],[f76])).
% 0.21/0.57  fof(f299,plain,(
% 0.21/0.57    sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) = sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2) | v2_struct_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | (~spl5_2 | ~spl5_3 | ~spl5_24)),
% 0.21/0.57    inference(subsumption_resolution,[],[f298,f73])).
% 0.21/0.57  fof(f73,plain,(
% 0.21/0.57    l1_waybel_0(sK1,sK0) | ~spl5_3),
% 0.21/0.57    inference(avatar_component_clause,[],[f71])).
% 0.21/0.57  fof(f298,plain,(
% 0.21/0.57    sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) = sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | (~spl5_2 | ~spl5_24)),
% 0.21/0.57    inference(subsumption_resolution,[],[f280,f68])).
% 0.21/0.57  fof(f68,plain,(
% 0.21/0.57    m1_subset_1(sK2,u1_struct_0(sK1)) | ~spl5_2),
% 0.21/0.57    inference(avatar_component_clause,[],[f66])).
% 0.21/0.57  fof(f280,plain,(
% 0.21/0.57    sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) = sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2) | ~m1_subset_1(sK2,u1_struct_0(sK1)) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl5_24),
% 0.21/0.57    inference(resolution,[],[f260,f56])).
% 0.21/0.57  fof(f56,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (sK4(X0,X2,X3) = X0 | ~r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_waybel_0(X2,X1) | v2_struct_0(X2) | ~l1_struct_0(X1) | v2_struct_0(X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f38])).
% 0.21/0.57  fof(f38,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3] : (((r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) | ! [X4] : (~r1_orders_2(X2,X3,X4) | X0 != X4 | ~m1_subset_1(X4,u1_struct_0(X2)))) & ((r1_orders_2(X2,X3,sK4(X0,X2,X3)) & sK4(X0,X2,X3) = X0 & m1_subset_1(sK4(X0,X2,X3),u1_struct_0(X2))) | ~r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)))) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_waybel_0(X2,X1) | v2_struct_0(X2) | ~l1_struct_0(X1) | v2_struct_0(X1))),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f37])).
% 0.21/0.57  fof(f37,plain,(
% 0.21/0.57    ! [X3,X2,X0] : (? [X5] : (r1_orders_2(X2,X3,X5) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X2))) => (r1_orders_2(X2,X3,sK4(X0,X2,X3)) & sK4(X0,X2,X3) = X0 & m1_subset_1(sK4(X0,X2,X3),u1_struct_0(X2))))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f36,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3] : (((r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) | ! [X4] : (~r1_orders_2(X2,X3,X4) | X0 != X4 | ~m1_subset_1(X4,u1_struct_0(X2)))) & (? [X5] : (r1_orders_2(X2,X3,X5) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X2))) | ~r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)))) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_waybel_0(X2,X1) | v2_struct_0(X2) | ~l1_struct_0(X1) | v2_struct_0(X1))),
% 0.21/0.57    inference(rectify,[],[f35])).
% 0.21/0.57  fof(f35,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3] : (((r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) | ! [X4] : (~r1_orders_2(X2,X3,X4) | X0 != X4 | ~m1_subset_1(X4,u1_struct_0(X2)))) & (? [X4] : (r1_orders_2(X2,X3,X4) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X2))) | ~r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)))) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_waybel_0(X2,X1) | v2_struct_0(X2) | ~l1_struct_0(X1) | v2_struct_0(X1))),
% 0.21/0.57    inference(nnf_transformation,[],[f27])).
% 0.21/0.57  fof(f27,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3] : ((r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) <=> ? [X4] : (r1_orders_2(X2,X3,X4) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X2)))) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_waybel_0(X2,X1) | v2_struct_0(X2) | ~l1_struct_0(X1) | v2_struct_0(X1))),
% 0.21/0.57    inference(flattening,[],[f26])).
% 0.21/0.57  fof(f26,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3] : ((r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) <=> ? [X4] : (r1_orders_2(X2,X3,X4) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X2)))) | (~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_waybel_0(X2,X1) | v2_struct_0(X2) | ~l1_struct_0(X1) | v2_struct_0(X1)))),
% 0.21/0.57    inference(ennf_transformation,[],[f6])).
% 0.21/0.57  fof(f6,axiom,(
% 0.21/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,u1_struct_0(X2)) & l1_waybel_0(X2,X1) & ~v2_struct_0(X2) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) <=> ? [X4] : (r1_orders_2(X2,X3,X4) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X2)))))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_3_0_waybel_9)).
% 0.21/0.57  fof(f260,plain,(
% 0.21/0.57    r2_hidden(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),a_3_0_waybel_9(sK0,sK1,sK2)) | ~spl5_24),
% 0.21/0.57    inference(avatar_component_clause,[],[f258])).
% 0.21/0.57  fof(f297,plain,(
% 0.21/0.57    spl5_28 | ~spl5_2 | ~spl5_3 | spl5_4 | ~spl5_5 | spl5_6 | ~spl5_24),
% 0.21/0.57    inference(avatar_split_clause,[],[f276,f258,f86,f81,f76,f71,f66,f294])).
% 0.21/0.57  fof(f294,plain,(
% 0.21/0.57    spl5_28 <=> m1_subset_1(sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2),u1_struct_0(sK1))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 0.21/0.57  fof(f276,plain,(
% 0.21/0.57    m1_subset_1(sK4(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),sK1,sK2),u1_struct_0(sK1)) | (~spl5_2 | ~spl5_3 | spl5_4 | ~spl5_5 | spl5_6 | ~spl5_24)),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f88,f83,f78,f73,f68,f260,f55])).
% 0.21/0.57  fof(f55,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK4(X0,X2,X3),u1_struct_0(X2)) | ~r2_hidden(X0,a_3_0_waybel_9(X1,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_waybel_0(X2,X1) | v2_struct_0(X2) | ~l1_struct_0(X1) | v2_struct_0(X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f38])).
% 0.21/0.57  fof(f268,plain,(
% 0.21/0.57    ~spl5_25 | spl5_10 | spl5_23),
% 0.21/0.57    inference(avatar_split_clause,[],[f262,f253,f156,f265])).
% 0.21/0.57  fof(f265,plain,(
% 0.21/0.57    spl5_25 <=> m1_subset_1(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),u1_struct_0(sK1))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 0.21/0.57  fof(f253,plain,(
% 0.21/0.57    spl5_23 <=> r2_hidden(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),u1_struct_0(sK1))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.21/0.57  fof(f262,plain,(
% 0.21/0.57    ~m1_subset_1(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),u1_struct_0(sK1)) | (spl5_10 | spl5_23)),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f157,f255,f46])).
% 0.21/0.57  fof(f46,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f32])).
% 0.21/0.57  fof(f32,plain,(
% 0.21/0.57    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.21/0.57    inference(nnf_transformation,[],[f19])).
% 0.21/0.57  fof(f19,plain,(
% 0.21/0.57    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f2])).
% 0.21/0.57  fof(f2,axiom,(
% 0.21/0.57    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.57  fof(f255,plain,(
% 0.21/0.57    ~r2_hidden(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),u1_struct_0(sK1)) | spl5_23),
% 0.21/0.57    inference(avatar_component_clause,[],[f253])).
% 0.21/0.57  fof(f157,plain,(
% 0.21/0.57    ~v1_xboole_0(u1_struct_0(sK1)) | spl5_10),
% 0.21/0.57    inference(avatar_component_clause,[],[f156])).
% 0.21/0.57  fof(f261,plain,(
% 0.21/0.57    spl5_24 | spl5_17),
% 0.21/0.57    inference(avatar_split_clause,[],[f248,f224,f258])).
% 0.21/0.57  fof(f224,plain,(
% 0.21/0.57    spl5_17 <=> r1_tarski(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.21/0.57  fof(f248,plain,(
% 0.21/0.57    r2_hidden(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),a_3_0_waybel_9(sK0,sK1,sK2)) | spl5_17),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f226,f53])).
% 0.21/0.57  fof(f53,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f34])).
% 0.21/0.57  fof(f34,plain,(
% 0.21/0.57    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f33])).
% 0.21/0.57  fof(f33,plain,(
% 0.21/0.57    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f25,plain,(
% 0.21/0.57    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f10])).
% 0.21/0.57  fof(f10,plain,(
% 0.21/0.57    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 0.21/0.57    inference(unused_predicate_definition_removal,[],[f1])).
% 0.21/0.57  fof(f1,axiom,(
% 0.21/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.57  fof(f226,plain,(
% 0.21/0.57    ~r1_tarski(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) | spl5_17),
% 0.21/0.57    inference(avatar_component_clause,[],[f224])).
% 0.21/0.57  fof(f256,plain,(
% 0.21/0.57    ~spl5_23 | spl5_17),
% 0.21/0.57    inference(avatar_split_clause,[],[f249,f224,f253])).
% 0.21/0.57  fof(f249,plain,(
% 0.21/0.57    ~r2_hidden(sK3(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)),u1_struct_0(sK1)) | spl5_17),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f226,f54])).
% 0.21/0.57  fof(f54,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK3(X0,X1),X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f34])).
% 0.21/0.57  fof(f227,plain,(
% 0.21/0.57    ~spl5_17 | spl5_1 | ~spl5_9),
% 0.21/0.57    inference(avatar_split_clause,[],[f213,f150,f61,f224])).
% 0.21/0.57  fof(f61,plain,(
% 0.21/0.57    spl5_1 <=> r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.57  fof(f150,plain,(
% 0.21/0.57    spl5_9 <=> u1_struct_0(k4_waybel_9(sK0,sK1,sK2)) = a_3_0_waybel_9(sK0,sK1,sK2)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.57  fof(f213,plain,(
% 0.21/0.57    ~r1_tarski(a_3_0_waybel_9(sK0,sK1,sK2),u1_struct_0(sK1)) | (spl5_1 | ~spl5_9)),
% 0.21/0.57    inference(backward_demodulation,[],[f63,f152])).
% 0.21/0.57  fof(f152,plain,(
% 0.21/0.57    u1_struct_0(k4_waybel_9(sK0,sK1,sK2)) = a_3_0_waybel_9(sK0,sK1,sK2) | ~spl5_9),
% 0.21/0.57    inference(avatar_component_clause,[],[f150])).
% 0.21/0.57  fof(f63,plain,(
% 0.21/0.57    ~r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1)) | spl5_1),
% 0.21/0.57    inference(avatar_component_clause,[],[f61])).
% 0.21/0.57  fof(f153,plain,(
% 0.21/0.57    spl5_9 | ~spl5_2 | ~spl5_3 | spl5_4 | ~spl5_5 | spl5_6),
% 0.21/0.57    inference(avatar_split_clause,[],[f140,f86,f81,f76,f71,f66,f150])).
% 0.21/0.57  fof(f140,plain,(
% 0.21/0.57    u1_struct_0(k4_waybel_9(sK0,sK1,sK2)) = a_3_0_waybel_9(sK0,sK1,sK2) | (~spl5_2 | ~spl5_3 | spl5_4 | ~spl5_5 | spl5_6)),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f88,f83,f78,f73,f68,f45])).
% 0.21/0.57  fof(f45,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (u1_struct_0(k4_waybel_9(X0,X1,X2)) = a_3_0_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f18])).
% 0.21/0.57  fof(f18,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (! [X2] : (u1_struct_0(k4_waybel_9(X0,X1,X2)) = a_3_0_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.57    inference(flattening,[],[f17])).
% 0.21/0.57  fof(f17,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (! [X2] : (u1_struct_0(k4_waybel_9(X0,X1,X2)) = a_3_0_waybel_9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f7])).
% 0.21/0.57  fof(f7,axiom,(
% 0.21/0.57    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => u1_struct_0(k4_waybel_9(X0,X1,X2)) = a_3_0_waybel_9(X0,X1,X2))))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_waybel_9)).
% 0.21/0.57  fof(f139,plain,(
% 0.21/0.57    ~spl5_8 | ~spl5_3 | spl5_4 | ~spl5_5 | spl5_6),
% 0.21/0.57    inference(avatar_split_clause,[],[f121,f86,f81,f76,f71,f136])).
% 0.21/0.57  fof(f121,plain,(
% 0.21/0.57    ~v1_xboole_0(u1_waybel_0(sK0,sK1)) | (~spl5_3 | spl5_4 | ~spl5_5 | spl5_6)),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f88,f83,f78,f73,f51])).
% 0.21/0.57  fof(f51,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~v1_xboole_0(u1_waybel_0(X0,X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f22])).
% 0.21/0.57  fof(f22,plain,(
% 0.21/0.57    ! [X0,X1] : (~v1_xboole_0(u1_waybel_0(X0,X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.57    inference(flattening,[],[f21])).
% 0.21/0.57  fof(f21,plain,(
% 0.21/0.57    ! [X0,X1] : (~v1_xboole_0(u1_waybel_0(X0,X1)) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f13])).
% 0.21/0.57  fof(f13,plain,(
% 0.21/0.57    ! [X0,X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_waybel_0(X0,X1)))),
% 0.21/0.57    inference(pure_predicate_removal,[],[f12])).
% 0.21/0.57  fof(f12,plain,(
% 0.21/0.57    ! [X0,X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (~v1_xboole_0(u1_waybel_0(X0,X1)) & v1_funct_1(u1_waybel_0(X0,X1))))),
% 0.21/0.57    inference(pure_predicate_removal,[],[f5])).
% 0.21/0.57  fof(f5,axiom,(
% 0.21/0.57    ! [X0,X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & ~v1_xboole_0(u1_waybel_0(X0,X1)) & v1_funct_1(u1_waybel_0(X0,X1))))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc15_yellow_6)).
% 0.21/0.57  fof(f134,plain,(
% 0.21/0.57    spl5_7 | ~spl5_3 | ~spl5_5),
% 0.21/0.57    inference(avatar_split_clause,[],[f122,f81,f71,f131])).
% 0.21/0.57  fof(f122,plain,(
% 0.21/0.57    m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | (~spl5_3 | ~spl5_5)),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f83,f73,f52])).
% 0.21/0.57  fof(f52,plain,(
% 0.21/0.57    ( ! [X0,X1] : (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f24])).
% 0.21/0.57  fof(f24,plain,(
% 0.21/0.57    ! [X0,X1] : (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0))),
% 0.21/0.57    inference(flattening,[],[f23])).
% 0.21/0.57  fof(f23,plain,(
% 0.21/0.57    ! [X0,X1] : (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f14])).
% 0.21/0.57  fof(f14,plain,(
% 0.21/0.57    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))))),
% 0.21/0.57    inference(pure_predicate_removal,[],[f11])).
% 0.21/0.57  fof(f11,plain,(
% 0.21/0.57    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_1(u1_waybel_0(X0,X1))))),
% 0.21/0.57    inference(pure_predicate_removal,[],[f4])).
% 0.21/0.57  fof(f4,axiom,(
% 0.21/0.57    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(u1_waybel_0(X0,X1))))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_waybel_0)).
% 0.21/0.57  fof(f89,plain,(
% 0.21/0.57    ~spl5_6),
% 0.21/0.57    inference(avatar_split_clause,[],[f39,f86])).
% 0.21/0.57  fof(f39,plain,(
% 0.21/0.57    ~v2_struct_0(sK0)),
% 0.21/0.57    inference(cnf_transformation,[],[f31])).
% 0.21/0.57  fof(f31,plain,(
% 0.21/0.57    ((~r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1)) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_waybel_0(sK1,sK0) & ~v2_struct_0(sK1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f30,f29,f28])).
% 0.21/0.57  fof(f28,plain,(
% 0.21/0.57    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)) & m1_subset_1(X2,u1_struct_0(X1))) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r1_tarski(u1_struct_0(k4_waybel_9(sK0,X1,X2)),u1_struct_0(X1)) & m1_subset_1(X2,u1_struct_0(X1))) & l1_waybel_0(X1,sK0) & ~v2_struct_0(X1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f29,plain,(
% 0.21/0.57    ? [X1] : (? [X2] : (~r1_tarski(u1_struct_0(k4_waybel_9(sK0,X1,X2)),u1_struct_0(X1)) & m1_subset_1(X2,u1_struct_0(X1))) & l1_waybel_0(X1,sK0) & ~v2_struct_0(X1)) => (? [X2] : (~r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,X2)),u1_struct_0(sK1)) & m1_subset_1(X2,u1_struct_0(sK1))) & l1_waybel_0(sK1,sK0) & ~v2_struct_0(sK1))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f30,plain,(
% 0.21/0.57    ? [X2] : (~r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,X2)),u1_struct_0(sK1)) & m1_subset_1(X2,u1_struct_0(sK1))) => (~r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1)) & m1_subset_1(sK2,u1_struct_0(sK1)))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f16,plain,(
% 0.21/0.57    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)) & m1_subset_1(X2,u1_struct_0(X1))) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 0.21/0.57    inference(flattening,[],[f15])).
% 0.21/0.57  fof(f15,plain,(
% 0.21/0.57    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)) & m1_subset_1(X2,u1_struct_0(X1))) & (l1_waybel_0(X1,X0) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f9])).
% 0.21/0.57  % (23150)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.57  fof(f9,negated_conjecture,(
% 0.21/0.57    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)))))),
% 0.21/0.57    inference(negated_conjecture,[],[f8])).
% 0.21/0.57  fof(f8,conjecture,(
% 0.21/0.57    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)))))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_waybel_9)).
% 0.21/0.57  fof(f84,plain,(
% 0.21/0.57    spl5_5),
% 0.21/0.57    inference(avatar_split_clause,[],[f40,f81])).
% 0.21/0.57  fof(f40,plain,(
% 0.21/0.57    l1_struct_0(sK0)),
% 0.21/0.57    inference(cnf_transformation,[],[f31])).
% 0.21/0.57  fof(f79,plain,(
% 0.21/0.57    ~spl5_4),
% 0.21/0.57    inference(avatar_split_clause,[],[f41,f76])).
% 0.21/0.57  fof(f41,plain,(
% 0.21/0.57    ~v2_struct_0(sK1)),
% 0.21/0.57    inference(cnf_transformation,[],[f31])).
% 0.21/0.57  fof(f74,plain,(
% 0.21/0.57    spl5_3),
% 0.21/0.57    inference(avatar_split_clause,[],[f42,f71])).
% 0.21/0.57  fof(f42,plain,(
% 0.21/0.57    l1_waybel_0(sK1,sK0)),
% 0.21/0.57    inference(cnf_transformation,[],[f31])).
% 0.21/0.57  fof(f69,plain,(
% 0.21/0.57    spl5_2),
% 0.21/0.57    inference(avatar_split_clause,[],[f43,f66])).
% 0.21/0.57  fof(f43,plain,(
% 0.21/0.57    m1_subset_1(sK2,u1_struct_0(sK1))),
% 0.21/0.57    inference(cnf_transformation,[],[f31])).
% 0.21/0.57  fof(f64,plain,(
% 0.21/0.57    ~spl5_1),
% 0.21/0.57    inference(avatar_split_clause,[],[f44,f61])).
% 0.21/0.57  fof(f44,plain,(
% 0.21/0.57    ~r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1))),
% 0.21/0.57    inference(cnf_transformation,[],[f31])).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (23169)------------------------------
% 0.21/0.57  % (23169)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (23169)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (23169)Memory used [KB]: 6396
% 0.21/0.57  % (23169)Time elapsed: 0.147 s
% 0.21/0.57  % (23169)------------------------------
% 0.21/0.57  % (23169)------------------------------
% 0.21/0.57  % (23143)Success in time 0.21 s
%------------------------------------------------------------------------------
