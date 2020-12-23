%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 432 expanded)
%              Number of leaves         :   34 ( 210 expanded)
%              Depth                    :   23
%              Number of atoms          :  942 (2324 expanded)
%              Number of equality atoms :   64 ( 315 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f309,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f77,f82,f87,f92,f97,f102,f107,f112,f117,f129,f158,f180,f187,f228,f258,f279,f288,f307,f308])).

fof(f308,plain,
    ( sK1 != sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1))
    | r2_hidden(sK1,k3_orders_2(sK0,sK3,sK1))
    | ~ r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1)),k3_orders_2(sK0,sK3,sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f307,plain,
    ( spl5_22
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_16
    | ~ spl5_19
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f295,f285,f276,f225,f109,f104,f99,f94,f89,f84,f79,f74,f69,f304])).

fof(f304,plain,
    ( spl5_22
  <=> sK1 = sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f69,plain,
    ( spl5_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f74,plain,
    ( spl5_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f79,plain,
    ( spl5_3
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f84,plain,
    ( spl5_4
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f89,plain,
    ( spl5_5
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f94,plain,
    ( spl5_6
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f99,plain,
    ( spl5_7
  <=> m2_orders_2(sK3,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f104,plain,
    ( spl5_8
  <=> m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f109,plain,
    ( spl5_9
  <=> sK1 = k1_funct_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f225,plain,
    ( spl5_16
  <=> m1_subset_1(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f276,plain,
    ( spl5_19
  <=> r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f285,plain,
    ( spl5_20
  <=> r2_orders_2(sK0,sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f295,plain,
    ( sK1 = sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_16
    | ~ spl5_19
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f294,f280])).

fof(f280,plain,
    ( r1_orders_2(sK0,sK1,sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1)))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_16
    | ~ spl5_19 ),
    inference(unit_resulting_resolution,[],[f227,f278,f201])).

fof(f201,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK1,X0) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f200,f71])).

fof(f71,plain,
    ( ~ v2_struct_0(sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f200,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK1,X0)
        | v2_struct_0(sK0) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f199,f76])).

fof(f76,plain,
    ( v3_orders_2(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f74])).

fof(f199,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK1,X0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f198,f91])).

fof(f91,plain,
    ( l1_orders_2(sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f89])).

fof(f198,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK1,X0)
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f197,f96])).

fof(f96,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f94])).

fof(f197,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK1,X0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(duplicate_literal_removal,[],[f196])).

fof(f196,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(resolution,[],[f163,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(X0,X1,X2)
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_orders_2(X0,X1,X2)
          | ~ r1_orders_2(X0,X1,X2) )
        & ( r1_orders_2(X0,X1,X2)
          | ~ r3_orders_2(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
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
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f163,plain,
    ( ! [X0] :
        ( r3_orders_2(sK0,sK1,X0)
        | ~ r2_hidden(X0,sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(resolution,[],[f153,f101])).

fof(f101,plain,
    ( m2_orders_2(sK3,sK0,sK2)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f99])).

fof(f153,plain,
    ( ! [X0,X1] :
        ( ~ m2_orders_2(X1,sK0,sK2)
        | ~ r2_hidden(X0,X1)
        | r3_orders_2(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f152,f71])).

fof(f152,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ m2_orders_2(X1,sK0,sK2)
        | r3_orders_2(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f151,f76])).

fof(f151,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ m2_orders_2(X1,sK0,sK2)
        | r3_orders_2(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f150,f81])).

fof(f81,plain,
    ( v4_orders_2(sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f79])).

fof(f150,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ m2_orders_2(X1,sK0,sK2)
        | r3_orders_2(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f149,f86])).

fof(f86,plain,
    ( v5_orders_2(sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f84])).

fof(f149,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ m2_orders_2(X1,sK0,sK2)
        | r3_orders_2(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f148,f91])).

fof(f148,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ m2_orders_2(X1,sK0,sK2)
        | r3_orders_2(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f147,f106])).

fof(f106,plain,
    ( m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK0)))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f104])).

fof(f147,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ m2_orders_2(X1,sK0,sK2)
        | ~ m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK0)))
        | r3_orders_2(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_6
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f146,f96])).

fof(f146,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ r2_hidden(X0,X1)
        | ~ m2_orders_2(X1,sK0,sK2)
        | ~ m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK0)))
        | r3_orders_2(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_9 ),
    inference(superposition,[],[f66,f111])).

fof(f111,plain,
    ( sK1 = k1_funct_1(sK2,u1_struct_0(sK0))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f109])).

fof(f66,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ m1_subset_1(k1_funct_1(X3,u1_struct_0(X0)),u1_struct_0(X0))
      | ~ r2_hidden(X1,X4)
      | ~ m2_orders_2(X4,X0,X3)
      | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X0)))
      | r3_orders_2(X0,k1_funct_1(X3,u1_struct_0(X0)),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r3_orders_2(X0,X2,X1)
      | k1_funct_1(X3,u1_struct_0(X0)) != X2
      | ~ r2_hidden(X1,X4)
      | ~ m2_orders_2(X4,X0,X3)
      | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r3_orders_2(X0,X2,X1)
                      | k1_funct_1(X3,u1_struct_0(X0)) != X2
                      | ~ r2_hidden(X1,X4)
                      | ~ m2_orders_2(X4,X0,X3) )
                  | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r3_orders_2(X0,X2,X1)
                      | k1_funct_1(X3,u1_struct_0(X0)) != X2
                      | ~ r2_hidden(X1,X4)
                      | ~ m2_orders_2(X4,X0,X3) )
                  | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_orders_1(X3,k1_orders_1(u1_struct_0(X0)))
                 => ! [X4] :
                      ( m2_orders_2(X4,X0,X3)
                     => ( ( k1_funct_1(X3,u1_struct_0(X0)) = X2
                          & r2_hidden(X1,X4) )
                       => r3_orders_2(X0,X2,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_orders_2)).

fof(f278,plain,
    ( r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1)),sK3)
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f276])).

fof(f227,plain,
    ( m1_subset_1(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1)),u1_struct_0(sK0))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f225])).

fof(f294,plain,
    ( sK1 = sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1))
    | ~ r1_orders_2(sK0,sK1,sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1)))
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_16
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f293,f96])).

fof(f293,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | sK1 = sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1))
    | ~ r1_orders_2(sK0,sK1,sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1)))
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_16
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f292,f227])).

fof(f292,plain,
    ( ~ m1_subset_1(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | sK1 = sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1))
    | ~ r1_orders_2(sK0,sK1,sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1)))
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_20 ),
    inference(resolution,[],[f287,f170])).

fof(f170,plain,
    ( ! [X0,X1] :
        ( ~ r2_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | X0 = X1
        | ~ r1_orders_2(sK0,X0,X1) )
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f169,f91])).

fof(f169,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | X0 = X1
        | ~ r2_orders_2(sK0,X1,X0)
        | ~ l1_orders_2(sK0) )
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(duplicate_literal_removal,[],[f168])).

fof(f168,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | X0 = X1
        | ~ r2_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(resolution,[],[f124,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).

fof(f124,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | X0 = X1 )
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f123,f91])).

fof(f123,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | X0 = X1 )
    | ~ spl5_4 ),
    inference(resolution,[],[f58,f86])).

% (28225)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ r1_orders_2(X0,X2,X1)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_orders_2(X0,X2,X1)
                  & r1_orders_2(X0,X1,X2) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_orders_2)).

fof(f287,plain,
    ( r2_orders_2(sK0,sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1)),sK1)
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f285])).

fof(f288,plain,
    ( spl5_20
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_12
    | ~ spl5_16
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f263,f255,f225,f155,f94,f89,f84,f79,f74,f69,f285])).

fof(f155,plain,
    ( spl5_12
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f255,plain,
    ( spl5_18
  <=> r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1)),k3_orders_2(sK0,sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f263,plain,
    ( r2_orders_2(sK0,sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1)),sK1)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_12
    | ~ spl5_16
    | ~ spl5_18 ),
    inference(unit_resulting_resolution,[],[f71,f76,f81,f86,f91,f96,f157,f227,f257,f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_orders_2(X0,X1,X2)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                      | ~ r2_hidden(X1,X3)
                      | ~ r2_orders_2(X0,X1,X2) )
                    & ( ( r2_hidden(X1,X3)
                        & r2_orders_2(X0,X1,X2) )
                      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2)) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                      | ~ r2_hidden(X1,X3)
                      | ~ r2_orders_2(X0,X1,X2) )
                    & ( ( r2_hidden(X1,X3)
                        & r2_orders_2(X0,X1,X2) )
                      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2)) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_orders_2)).

fof(f257,plain,
    ( r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1)),k3_orders_2(sK0,sK3,sK1))
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f255])).

fof(f157,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f155])).

fof(f279,plain,
    ( spl5_19
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_12
    | ~ spl5_16
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f264,f255,f225,f155,f94,f89,f84,f79,f74,f69,f276])).

fof(f264,plain,
    ( r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1)),sK3)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_12
    | ~ spl5_16
    | ~ spl5_18 ),
    inference(unit_resulting_resolution,[],[f71,f76,f81,f86,f91,f96,f157,f227,f257,f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_hidden(X1,X3)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f258,plain,
    ( spl5_18
    | spl5_10
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f193,f184,f114,f255])).

fof(f114,plain,
    ( spl5_10
  <=> k1_xboole_0 = k3_orders_2(sK0,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f184,plain,
    ( spl5_14
  <=> m1_subset_1(k3_orders_2(sK0,sK3,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f193,plain,
    ( r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1)),k3_orders_2(sK0,sK3,sK1))
    | spl5_10
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f116,f186,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(sK4(X0,X1),X1)
        & m1_subset_1(sK4(X0,X1),X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & m1_subset_1(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ~ ( ! [X2] :
              ( m1_subset_1(X2,X0)
             => ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).

fof(f186,plain,
    ( m1_subset_1(k3_orders_2(sK0,sK3,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f184])).

fof(f116,plain,
    ( k1_xboole_0 != k3_orders_2(sK0,sK3,sK1)
    | spl5_10 ),
    inference(avatar_component_clause,[],[f114])).

fof(f228,plain,
    ( spl5_16
    | spl5_10
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f194,f184,f114,f225])).

fof(f194,plain,
    ( m1_subset_1(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1)),u1_struct_0(sK0))
    | spl5_10
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f116,f186,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(X0,X1),X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f187,plain,
    ( spl5_14
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f160,f155,f94,f89,f84,f79,f74,f69,f184])).

fof(f160,plain,
    ( m1_subset_1(k3_orders_2(sK0,sK3,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f71,f76,f81,f86,f91,f96,f157,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_orders_2)).

fof(f180,plain,
    ( ~ spl5_13
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_11
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f159,f155,f126,f94,f89,f84,f79,f74,f69,f177])).

fof(f177,plain,
    ( spl5_13
  <=> r2_hidden(sK1,k3_orders_2(sK0,sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f126,plain,
    ( spl5_11
  <=> r2_orders_2(sK0,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f159,plain,
    ( ~ r2_hidden(sK1,k3_orders_2(sK0,sK3,sK1))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_11
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f71,f76,f81,f86,f91,f128,f96,f96,f157,f55])).

fof(f128,plain,
    ( ~ r2_orders_2(sK0,sK1,sK1)
    | spl5_11 ),
    inference(avatar_component_clause,[],[f126])).

fof(f158,plain,
    ( spl5_12
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f130,f104,f99,f89,f84,f79,f74,f69,f155])).

fof(f130,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(unit_resulting_resolution,[],[f71,f76,f81,f86,f91,f101,f106,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m2_orders_2(X2,X0,X1) )
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m2_orders_2(X2,X0,X1) )
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m2_orders_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m2_orders_2(X2,X0,X1)
         => ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_orders_2)).

fof(f129,plain,
    ( ~ spl5_11
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f118,f94,f89,f126])).

fof(f118,plain,
    ( ~ r2_orders_2(sK0,sK1,sK1)
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f91,f96,f67])).

fof(f67,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f65])).

fof(f65,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f117,plain,(
    ~ spl5_10 ),
    inference(avatar_split_clause,[],[f50,f114])).

fof(f50,plain,(
    k1_xboole_0 != k3_orders_2(sK0,sK3,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( k1_xboole_0 != k3_orders_2(sK0,sK3,sK1)
    & sK1 = k1_funct_1(sK2,u1_struct_0(sK0))
    & m2_orders_2(sK3,sK0,sK2)
    & m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f32,f31,f30,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( k1_xboole_0 != k3_orders_2(X0,X3,X1)
                    & k1_funct_1(X2,u1_struct_0(X0)) = X1
                    & m2_orders_2(X3,X0,X2) )
                & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k1_xboole_0 != k3_orders_2(sK0,X3,X1)
                  & k1_funct_1(X2,u1_struct_0(sK0)) = X1
                  & m2_orders_2(X3,sK0,X2) )
              & m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( k1_xboole_0 != k3_orders_2(sK0,X3,X1)
                & k1_funct_1(X2,u1_struct_0(sK0)) = X1
                & m2_orders_2(X3,sK0,X2) )
            & m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( k1_xboole_0 != k3_orders_2(sK0,X3,sK1)
              & k1_funct_1(X2,u1_struct_0(sK0)) = sK1
              & m2_orders_2(X3,sK0,X2) )
          & m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( k1_xboole_0 != k3_orders_2(sK0,X3,sK1)
            & k1_funct_1(X2,u1_struct_0(sK0)) = sK1
            & m2_orders_2(X3,sK0,X2) )
        & m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0))) )
   => ( ? [X3] :
          ( k1_xboole_0 != k3_orders_2(sK0,X3,sK1)
          & sK1 = k1_funct_1(sK2,u1_struct_0(sK0))
          & m2_orders_2(X3,sK0,sK2) )
      & m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X3] :
        ( k1_xboole_0 != k3_orders_2(sK0,X3,sK1)
        & sK1 = k1_funct_1(sK2,u1_struct_0(sK0))
        & m2_orders_2(X3,sK0,sK2) )
   => ( k1_xboole_0 != k3_orders_2(sK0,sK3,sK1)
      & sK1 = k1_funct_1(sK2,u1_struct_0(sK0))
      & m2_orders_2(sK3,sK0,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k1_xboole_0 != k3_orders_2(X0,X3,X1)
                  & k1_funct_1(X2,u1_struct_0(X0)) = X1
                  & m2_orders_2(X3,X0,X2) )
              & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k1_xboole_0 != k3_orders_2(X0,X3,X1)
                  & k1_funct_1(X2,u1_struct_0(X0)) = X1
                  & m2_orders_2(X3,X0,X2) )
              & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m2_orders_2(X3,X0,X2)
                   => ( k1_funct_1(X2,u1_struct_0(X0)) = X1
                     => k1_xboole_0 = k3_orders_2(X0,X3,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m2_orders_2(X3,X0,X2)
                 => ( k1_funct_1(X2,u1_struct_0(X0)) = X1
                   => k1_xboole_0 = k3_orders_2(X0,X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_orders_2)).

fof(f112,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f49,f109])).

fof(f49,plain,(
    sK1 = k1_funct_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f33])).

fof(f107,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f47,f104])).

fof(f47,plain,(
    m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f102,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f48,f99])).

fof(f48,plain,(
    m2_orders_2(sK3,sK0,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f97,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f46,f94])).

fof(f46,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f33])).

fof(f92,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f45,f89])).

fof(f45,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f87,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f44,f84])).

fof(f44,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f82,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f43,f79])).

fof(f43,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f77,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f42,f74])).

fof(f42,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f72,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f41,f69])).

fof(f41,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:38:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (28229)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.48  % (28244)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.49  % (28244)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f309,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f72,f77,f82,f87,f92,f97,f102,f107,f112,f117,f129,f158,f180,f187,f228,f258,f279,f288,f307,f308])).
% 0.21/0.49  fof(f308,plain,(
% 0.21/0.49    sK1 != sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1)) | r2_hidden(sK1,k3_orders_2(sK0,sK3,sK1)) | ~r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1)),k3_orders_2(sK0,sK3,sK1))),
% 0.21/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.49  fof(f307,plain,(
% 0.21/0.49    spl5_22 | spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7 | ~spl5_8 | ~spl5_9 | ~spl5_16 | ~spl5_19 | ~spl5_20),
% 0.21/0.49    inference(avatar_split_clause,[],[f295,f285,f276,f225,f109,f104,f99,f94,f89,f84,f79,f74,f69,f304])).
% 0.21/0.50  fof(f304,plain,(
% 0.21/0.50    spl5_22 <=> sK1 = sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    spl5_1 <=> v2_struct_0(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    spl5_2 <=> v3_orders_2(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    spl5_3 <=> v4_orders_2(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    spl5_4 <=> v5_orders_2(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.50  fof(f89,plain,(
% 0.21/0.50    spl5_5 <=> l1_orders_2(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    spl5_6 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.50  fof(f99,plain,(
% 0.21/0.50    spl5_7 <=> m2_orders_2(sK3,sK0,sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.50  fof(f104,plain,(
% 0.21/0.50    spl5_8 <=> m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.50  fof(f109,plain,(
% 0.21/0.50    spl5_9 <=> sK1 = k1_funct_1(sK2,u1_struct_0(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.50  fof(f225,plain,(
% 0.21/0.50    spl5_16 <=> m1_subset_1(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1)),u1_struct_0(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.21/0.50  fof(f276,plain,(
% 0.21/0.50    spl5_19 <=> r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1)),sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.21/0.50  fof(f285,plain,(
% 0.21/0.50    spl5_20 <=> r2_orders_2(sK0,sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1)),sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.21/0.50  fof(f295,plain,(
% 0.21/0.50    sK1 = sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1)) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7 | ~spl5_8 | ~spl5_9 | ~spl5_16 | ~spl5_19 | ~spl5_20)),
% 0.21/0.50    inference(subsumption_resolution,[],[f294,f280])).
% 0.21/0.50  fof(f280,plain,(
% 0.21/0.50    r1_orders_2(sK0,sK1,sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1))) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7 | ~spl5_8 | ~spl5_9 | ~spl5_16 | ~spl5_19)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f227,f278,f201])).
% 0.21/0.50  fof(f201,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,sK3) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,sK1,X0)) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7 | ~spl5_8 | ~spl5_9)),
% 0.21/0.50    inference(subsumption_resolution,[],[f200,f71])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    ~v2_struct_0(sK0) | spl5_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f69])).
% 0.21/0.50  fof(f200,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,sK3) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,sK1,X0) | v2_struct_0(sK0)) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7 | ~spl5_8 | ~spl5_9)),
% 0.21/0.50    inference(subsumption_resolution,[],[f199,f76])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    v3_orders_2(sK0) | ~spl5_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f74])).
% 0.21/0.50  fof(f199,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,sK3) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,sK1,X0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7 | ~spl5_8 | ~spl5_9)),
% 0.21/0.50    inference(subsumption_resolution,[],[f198,f91])).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    l1_orders_2(sK0) | ~spl5_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f89])).
% 0.21/0.50  fof(f198,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,sK3) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,sK1,X0) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7 | ~spl5_8 | ~spl5_9)),
% 0.21/0.50    inference(subsumption_resolution,[],[f197,f96])).
% 0.21/0.50  fof(f96,plain,(
% 0.21/0.50    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl5_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f94])).
% 0.21/0.50  fof(f197,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,sK3) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,sK1,X0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7 | ~spl5_8 | ~spl5_9)),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f196])).
% 0.21/0.50  fof(f196,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,sK3) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7 | ~spl5_8 | ~spl5_9)),
% 0.21/0.50    inference(resolution,[],[f163,f63])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r3_orders_2(X0,X1,X2) | r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 0.21/0.50  fof(f163,plain,(
% 0.21/0.50    ( ! [X0] : (r3_orders_2(sK0,sK1,X0) | ~r2_hidden(X0,sK3) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7 | ~spl5_8 | ~spl5_9)),
% 0.21/0.50    inference(resolution,[],[f153,f101])).
% 0.21/0.50  fof(f101,plain,(
% 0.21/0.50    m2_orders_2(sK3,sK0,sK2) | ~spl5_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f99])).
% 0.21/0.50  fof(f153,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m2_orders_2(X1,sK0,sK2) | ~r2_hidden(X0,X1) | r3_orders_2(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_8 | ~spl5_9)),
% 0.21/0.50    inference(subsumption_resolution,[],[f152,f71])).
% 0.21/0.50  fof(f152,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~m2_orders_2(X1,sK0,sK2) | r3_orders_2(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_8 | ~spl5_9)),
% 0.21/0.50    inference(subsumption_resolution,[],[f151,f76])).
% 0.21/0.50  fof(f151,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~m2_orders_2(X1,sK0,sK2) | r3_orders_2(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_8 | ~spl5_9)),
% 0.21/0.50    inference(subsumption_resolution,[],[f150,f81])).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    v4_orders_2(sK0) | ~spl5_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f79])).
% 0.21/0.50  fof(f150,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~m2_orders_2(X1,sK0,sK2) | r3_orders_2(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_8 | ~spl5_9)),
% 0.21/0.50    inference(subsumption_resolution,[],[f149,f86])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    v5_orders_2(sK0) | ~spl5_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f84])).
% 0.21/0.50  fof(f149,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~m2_orders_2(X1,sK0,sK2) | r3_orders_2(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl5_5 | ~spl5_6 | ~spl5_8 | ~spl5_9)),
% 0.21/0.50    inference(subsumption_resolution,[],[f148,f91])).
% 0.21/0.50  fof(f148,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~m2_orders_2(X1,sK0,sK2) | r3_orders_2(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl5_6 | ~spl5_8 | ~spl5_9)),
% 0.21/0.50    inference(subsumption_resolution,[],[f147,f106])).
% 0.21/0.50  fof(f106,plain,(
% 0.21/0.50    m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK0))) | ~spl5_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f104])).
% 0.21/0.50  fof(f147,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~m2_orders_2(X1,sK0,sK2) | ~m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK0))) | r3_orders_2(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl5_6 | ~spl5_9)),
% 0.21/0.50    inference(subsumption_resolution,[],[f146,f96])).
% 0.21/0.50  fof(f146,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r2_hidden(X0,X1) | ~m2_orders_2(X1,sK0,sK2) | ~m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK0))) | r3_orders_2(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl5_9),
% 0.21/0.50    inference(superposition,[],[f66,f111])).
% 0.21/0.50  fof(f111,plain,(
% 0.21/0.50    sK1 = k1_funct_1(sK2,u1_struct_0(sK0)) | ~spl5_9),
% 0.21/0.50    inference(avatar_component_clause,[],[f109])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    ( ! [X4,X0,X3,X1] : (~m1_subset_1(k1_funct_1(X3,u1_struct_0(X0)),u1_struct_0(X0)) | ~r2_hidden(X1,X4) | ~m2_orders_2(X4,X0,X3) | ~m1_orders_1(X3,k1_orders_1(u1_struct_0(X0))) | r3_orders_2(X0,k1_funct_1(X3,u1_struct_0(X0)),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f54])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (r3_orders_2(X0,X2,X1) | k1_funct_1(X3,u1_struct_0(X0)) != X2 | ~r2_hidden(X1,X4) | ~m2_orders_2(X4,X0,X3) | ~m1_orders_1(X3,k1_orders_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r3_orders_2(X0,X2,X1) | k1_funct_1(X3,u1_struct_0(X0)) != X2 | ~r2_hidden(X1,X4) | ~m2_orders_2(X4,X0,X3)) | ~m1_orders_1(X3,k1_orders_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r3_orders_2(X0,X2,X1) | (k1_funct_1(X3,u1_struct_0(X0)) != X2 | ~r2_hidden(X1,X4))) | ~m2_orders_2(X4,X0,X3)) | ~m1_orders_1(X3,k1_orders_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_orders_1(X3,k1_orders_1(u1_struct_0(X0))) => ! [X4] : (m2_orders_2(X4,X0,X3) => ((k1_funct_1(X3,u1_struct_0(X0)) = X2 & r2_hidden(X1,X4)) => r3_orders_2(X0,X2,X1)))))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_orders_2)).
% 0.21/0.50  fof(f278,plain,(
% 0.21/0.50    r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1)),sK3) | ~spl5_19),
% 0.21/0.50    inference(avatar_component_clause,[],[f276])).
% 0.21/0.50  fof(f227,plain,(
% 0.21/0.50    m1_subset_1(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1)),u1_struct_0(sK0)) | ~spl5_16),
% 0.21/0.50    inference(avatar_component_clause,[],[f225])).
% 0.21/0.50  fof(f294,plain,(
% 0.21/0.50    sK1 = sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1)) | ~r1_orders_2(sK0,sK1,sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1))) | (~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_16 | ~spl5_20)),
% 0.21/0.50    inference(subsumption_resolution,[],[f293,f96])).
% 0.21/0.50  fof(f293,plain,(
% 0.21/0.50    ~m1_subset_1(sK1,u1_struct_0(sK0)) | sK1 = sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1)) | ~r1_orders_2(sK0,sK1,sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1))) | (~spl5_4 | ~spl5_5 | ~spl5_16 | ~spl5_20)),
% 0.21/0.50    inference(subsumption_resolution,[],[f292,f227])).
% 0.21/0.50  fof(f292,plain,(
% 0.21/0.50    ~m1_subset_1(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1)),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | sK1 = sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1)) | ~r1_orders_2(sK0,sK1,sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1))) | (~spl5_4 | ~spl5_5 | ~spl5_20)),
% 0.21/0.50    inference(resolution,[],[f287,f170])).
% 0.21/0.50  fof(f170,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_orders_2(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | X0 = X1 | ~r1_orders_2(sK0,X0,X1)) ) | (~spl5_4 | ~spl5_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f169,f91])).
% 0.21/0.50  fof(f169,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | X0 = X1 | ~r2_orders_2(sK0,X1,X0) | ~l1_orders_2(sK0)) ) | (~spl5_4 | ~spl5_5)),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f168])).
% 0.21/0.50  fof(f168,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | X0 = X1 | ~r2_orders_2(sK0,X1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_orders_2(sK0)) ) | (~spl5_4 | ~spl5_5)),
% 0.21/0.50    inference(resolution,[],[f124,f51])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | X1 = X2 | ~r1_orders_2(X0,X1,X2)) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.50    inference(flattening,[],[f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | (X1 = X2 | ~r1_orders_2(X0,X1,X2))) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).
% 0.21/0.50  fof(f124,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_orders_2(sK0,X0,X1) | ~r1_orders_2(sK0,X1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | X0 = X1) ) | (~spl5_4 | ~spl5_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f123,f91])).
% 0.21/0.50  fof(f123,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_orders_2(sK0,X0,X1) | ~r1_orders_2(sK0,X1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | X0 = X1) ) | ~spl5_4),
% 0.21/0.50    inference(resolution,[],[f58,f86])).
% 0.21/0.50  % (28225)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v5_orders_2(X0) | ~r1_orders_2(X0,X2,X1) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | X1 = X2) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (X1 = X2 | ~r1_orders_2(X0,X2,X1) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.21/0.50    inference(flattening,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((X1 = X2 | (~r1_orders_2(X0,X2,X1) | ~r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X1) & r1_orders_2(X0,X1,X2)) => X1 = X2))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_orders_2)).
% 0.21/0.50  fof(f287,plain,(
% 0.21/0.50    r2_orders_2(sK0,sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1)),sK1) | ~spl5_20),
% 0.21/0.50    inference(avatar_component_clause,[],[f285])).
% 0.21/0.50  fof(f288,plain,(
% 0.21/0.50    spl5_20 | spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_12 | ~spl5_16 | ~spl5_18),
% 0.21/0.50    inference(avatar_split_clause,[],[f263,f255,f225,f155,f94,f89,f84,f79,f74,f69,f285])).
% 0.21/0.50  fof(f155,plain,(
% 0.21/0.50    spl5_12 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.50  fof(f255,plain,(
% 0.21/0.50    spl5_18 <=> r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1)),k3_orders_2(sK0,sK3,sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.21/0.50  fof(f263,plain,(
% 0.21/0.50    r2_orders_2(sK0,sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1)),sK1) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_12 | ~spl5_16 | ~spl5_18)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f71,f76,f81,f86,f91,f96,f157,f227,f257,f55])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~v5_orders_2(X0) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_orders_2(X0,X1,X2) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2)) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | (~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2))) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)))))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_orders_2)).
% 0.21/0.50  fof(f257,plain,(
% 0.21/0.50    r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1)),k3_orders_2(sK0,sK3,sK1)) | ~spl5_18),
% 0.21/0.50    inference(avatar_component_clause,[],[f255])).
% 0.21/0.50  fof(f157,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_12),
% 0.21/0.50    inference(avatar_component_clause,[],[f155])).
% 0.21/0.50  fof(f279,plain,(
% 0.21/0.50    spl5_19 | spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_12 | ~spl5_16 | ~spl5_18),
% 0.21/0.50    inference(avatar_split_clause,[],[f264,f255,f225,f155,f94,f89,f84,f79,f74,f69,f276])).
% 0.21/0.50  fof(f264,plain,(
% 0.21/0.50    r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1)),sK3) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_12 | ~spl5_16 | ~spl5_18)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f71,f76,f81,f86,f91,f96,f157,f227,f257,f56])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~v5_orders_2(X0) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_hidden(X1,X3) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f37])).
% 0.21/0.50  fof(f258,plain,(
% 0.21/0.50    spl5_18 | spl5_10 | ~spl5_14),
% 0.21/0.50    inference(avatar_split_clause,[],[f193,f184,f114,f255])).
% 0.21/0.50  fof(f114,plain,(
% 0.21/0.50    spl5_10 <=> k1_xboole_0 = k3_orders_2(sK0,sK3,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.50  fof(f184,plain,(
% 0.21/0.50    spl5_14 <=> m1_subset_1(k3_orders_2(sK0,sK3,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.21/0.50  fof(f193,plain,(
% 0.21/0.50    r2_hidden(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1)),k3_orders_2(sK0,sK3,sK1)) | (spl5_10 | ~spl5_14)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f116,f186,f60])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ! [X0,X1] : ((r2_hidden(sK4(X0,X1),X1) & m1_subset_1(sK4(X0,X1),X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ! [X1,X0] : (? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) => (r2_hidden(sK4(X0,X1),X1) & m1_subset_1(sK4(X0,X1),X0)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0,X1] : (? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(flattening,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0,X1] : ((? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~(! [X2] : (m1_subset_1(X2,X0) => ~r2_hidden(X2,X1)) & k1_xboole_0 != X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).
% 0.21/0.50  fof(f186,plain,(
% 0.21/0.50    m1_subset_1(k3_orders_2(sK0,sK3,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_14),
% 0.21/0.50    inference(avatar_component_clause,[],[f184])).
% 0.21/0.50  fof(f116,plain,(
% 0.21/0.50    k1_xboole_0 != k3_orders_2(sK0,sK3,sK1) | spl5_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f114])).
% 0.21/0.50  fof(f228,plain,(
% 0.21/0.50    spl5_16 | spl5_10 | ~spl5_14),
% 0.21/0.50    inference(avatar_split_clause,[],[f194,f184,f114,f225])).
% 0.21/0.50  fof(f194,plain,(
% 0.21/0.50    m1_subset_1(sK4(u1_struct_0(sK0),k3_orders_2(sK0,sK3,sK1)),u1_struct_0(sK0)) | (spl5_10 | ~spl5_14)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f116,f186,f59])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(sK4(X0,X1),X0) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f39])).
% 0.21/0.50  fof(f187,plain,(
% 0.21/0.50    spl5_14 | spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f160,f155,f94,f89,f84,f79,f74,f69,f184])).
% 0.21/0.50  fof(f160,plain,(
% 0.21/0.50    m1_subset_1(k3_orders_2(sK0,sK3,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_12)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f71,f76,f81,f86,f91,f96,f157,f62])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_orders_2)).
% 0.21/0.50  fof(f180,plain,(
% 0.21/0.50    ~spl5_13 | spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_11 | ~spl5_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f159,f155,f126,f94,f89,f84,f79,f74,f69,f177])).
% 0.21/0.50  fof(f177,plain,(
% 0.21/0.50    spl5_13 <=> r2_hidden(sK1,k3_orders_2(sK0,sK3,sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.50  fof(f126,plain,(
% 0.21/0.50    spl5_11 <=> r2_orders_2(sK0,sK1,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.50  fof(f159,plain,(
% 0.21/0.50    ~r2_hidden(sK1,k3_orders_2(sK0,sK3,sK1)) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_11 | ~spl5_12)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f71,f76,f81,f86,f91,f128,f96,f96,f157,f55])).
% 0.21/0.50  fof(f128,plain,(
% 0.21/0.50    ~r2_orders_2(sK0,sK1,sK1) | spl5_11),
% 0.21/0.50    inference(avatar_component_clause,[],[f126])).
% 0.21/0.50  fof(f158,plain,(
% 0.21/0.50    spl5_12 | spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f130,f104,f99,f89,f84,f79,f74,f69,f155])).
% 0.21/0.50  fof(f130,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_8)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f71,f76,f81,f86,f91,f101,f106,f61])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v5_orders_2(X0) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.50    inference(pure_predicate_removal,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_orders_2)).
% 0.21/0.50  fof(f129,plain,(
% 0.21/0.50    ~spl5_11 | ~spl5_5 | ~spl5_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f118,f94,f89,f126])).
% 0.21/0.50  fof(f118,plain,(
% 0.21/0.50    ~r2_orders_2(sK0,sK1,sK1) | (~spl5_5 | ~spl5_6)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f91,f96,f67])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f65])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f52])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (X1 != X2 | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f117,plain,(
% 0.21/0.50    ~spl5_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f50,f114])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    k1_xboole_0 != k3_orders_2(sK0,sK3,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    (((k1_xboole_0 != k3_orders_2(sK0,sK3,sK1) & sK1 = k1_funct_1(sK2,u1_struct_0(sK0)) & m2_orders_2(sK3,sK0,sK2)) & m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f32,f31,f30,f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k1_xboole_0 != k3_orders_2(X0,X3,X1) & k1_funct_1(X2,u1_struct_0(X0)) = X1 & m2_orders_2(X3,X0,X2)) & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (k1_xboole_0 != k3_orders_2(sK0,X3,X1) & k1_funct_1(X2,u1_struct_0(sK0)) = X1 & m2_orders_2(X3,sK0,X2)) & m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ? [X1] : (? [X2] : (? [X3] : (k1_xboole_0 != k3_orders_2(sK0,X3,X1) & k1_funct_1(X2,u1_struct_0(sK0)) = X1 & m2_orders_2(X3,sK0,X2)) & m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (? [X3] : (k1_xboole_0 != k3_orders_2(sK0,X3,sK1) & k1_funct_1(X2,u1_struct_0(sK0)) = sK1 & m2_orders_2(X3,sK0,X2)) & m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ? [X2] : (? [X3] : (k1_xboole_0 != k3_orders_2(sK0,X3,sK1) & k1_funct_1(X2,u1_struct_0(sK0)) = sK1 & m2_orders_2(X3,sK0,X2)) & m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0)))) => (? [X3] : (k1_xboole_0 != k3_orders_2(sK0,X3,sK1) & sK1 = k1_funct_1(sK2,u1_struct_0(sK0)) & m2_orders_2(X3,sK0,sK2)) & m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ? [X3] : (k1_xboole_0 != k3_orders_2(sK0,X3,sK1) & sK1 = k1_funct_1(sK2,u1_struct_0(sK0)) & m2_orders_2(X3,sK0,sK2)) => (k1_xboole_0 != k3_orders_2(sK0,sK3,sK1) & sK1 = k1_funct_1(sK2,u1_struct_0(sK0)) & m2_orders_2(sK3,sK0,sK2))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k1_xboole_0 != k3_orders_2(X0,X3,X1) & k1_funct_1(X2,u1_struct_0(X0)) = X1 & m2_orders_2(X3,X0,X2)) & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((k1_xboole_0 != k3_orders_2(X0,X3,X1) & k1_funct_1(X2,u1_struct_0(X0)) = X1) & m2_orders_2(X3,X0,X2)) & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,negated_conjecture,(
% 0.21/0.50    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_orders_1(X2,k1_orders_1(u1_struct_0(X0))) => ! [X3] : (m2_orders_2(X3,X0,X2) => (k1_funct_1(X2,u1_struct_0(X0)) = X1 => k1_xboole_0 = k3_orders_2(X0,X3,X1))))))),
% 0.21/0.50    inference(negated_conjecture,[],[f9])).
% 0.21/0.50  fof(f9,conjecture,(
% 0.21/0.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_orders_1(X2,k1_orders_1(u1_struct_0(X0))) => ! [X3] : (m2_orders_2(X3,X0,X2) => (k1_funct_1(X2,u1_struct_0(X0)) = X1 => k1_xboole_0 = k3_orders_2(X0,X3,X1))))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_orders_2)).
% 0.21/0.50  fof(f112,plain,(
% 0.21/0.50    spl5_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f49,f109])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    sK1 = k1_funct_1(sK2,u1_struct_0(sK0))),
% 0.21/0.50    inference(cnf_transformation,[],[f33])).
% 0.21/0.50  fof(f107,plain,(
% 0.21/0.50    spl5_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f47,f104])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK0)))),
% 0.21/0.50    inference(cnf_transformation,[],[f33])).
% 0.21/0.50  fof(f102,plain,(
% 0.21/0.50    spl5_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f48,f99])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    m2_orders_2(sK3,sK0,sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f33])).
% 0.21/0.50  fof(f97,plain,(
% 0.21/0.50    spl5_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f46,f94])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.50    inference(cnf_transformation,[],[f33])).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    spl5_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f45,f89])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    l1_orders_2(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f33])).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    spl5_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f44,f84])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    v5_orders_2(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f33])).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    spl5_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f43,f79])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    v4_orders_2(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f33])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    spl5_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f42,f74])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    v3_orders_2(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f33])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    ~spl5_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f41,f69])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ~v2_struct_0(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f33])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (28244)------------------------------
% 0.21/0.50  % (28244)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (28244)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (28244)Memory used [KB]: 10874
% 0.21/0.50  % (28244)Time elapsed: 0.087 s
% 0.21/0.50  % (28244)------------------------------
% 0.21/0.50  % (28244)------------------------------
% 0.21/0.50  % (28224)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (28236)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.50  % (28220)Success in time 0.144 s
%------------------------------------------------------------------------------
